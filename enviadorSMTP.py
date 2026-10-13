#!/usr/bin/env python3
"""
Validador SMTP v3.16 - CORREÇÃO COMPLETA DE PROXY E RETRY
- Cada SMTP envia apenas 1 email por minuto
- Rotação completa da lista antes de reutilizar
- Sistema de COOLDOWN para SMTPs com erro temporário (5-10 minutos)
- Emails com falha são GARANTIDAMENTE reenviados com SMTP diferente
- Proxy SOCKS5 com DNS remoto para evitar vazamento de informações
- Headers limpos para evitar identificação da máquina real
- Blacklist temporária por email para evitar retry com mesmo SMTP
- ADAPTAÇÃO: Integração de PDF opcional no menu principal
"""

import smtplib
import socket
import socks
import ssl
import os
import time
import csv
import json
import threading
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
from email.mime.base import MIMEBase
from email import encoders
from email.utils import formataddr, formatdate, make_msgid
from threading import Thread, Lock
from typing import Tuple, Optional
import sys
from queue import Queue, Empty
from datetime import datetime, date
import random
import string
import re
import requests
import pdfkit

# ============================================================================
# CONFIGURAÇÕES GLOBAIS - EDITE AQUI
# ============================================================================

# Credenciais do Proxy (EDITE AQUI)
PROXY_HOST = "dc.oxylabs.io"
PROXY_PORT = 8000
PROXY_USER = "user-bruxaonervoso_CHfaJ-country-US"
PROXY_PASS = "Opera098~098"

# Configurações gerais
MAX_WORKERS = 10  # Número de threads
TIMEOUT = 35
DNS_TIMEOUT = 7
TEST_EMAIL_TO = "manustotax@gmail.com"

# Configurações de envio em massa
EMAILS_POR_MINUTO_POR_SMTP = 3  # CADA SMTP ENVIA 1 EMAIL POR MINUTO
MIN_DELAY_SECONDS = 10  # 120 segundos de delay entre envios do mesmo SMTP
SMTP_COOLDOWN_SECONDS = 300  # 5 minutos de cooldown para SMTPs com erro temporário
FROM_NAME = "Simples Nacional"
ASSUNTO = "ENC: Prezado Responsavel "

# Arquivos
ARQUIVO_SMTPS_ENVIO = "smtp_envio.txt"
ARQUIVO_EMAILS = "emails.txt"
ARQUIVO_HTML = "mensagem.html"
ARQUIVO_SMTP_ERRO = "SMTPERROENVIO.txt"
ARQUIVO_LOG = "log_smtp_proxy.txt"
ARQUIVO_CONTROLE_JSON = "smtp_controle.json"
ARQUIVO_COOLDOWN_JSON = "smtp_cooldown.json"  # NOVO: Fila de cooldown
ARQUIVO_LAST_EMAIL = "last_email_sent.txt"

# --- CONFIGURAÇÕES PDF (INTEGRADAS) ---
PATH_TO_WKHTMLTOPF = r'/usr/bin/wkhtmltopdf'
TEMP_FOLDER = "temp_pdf"
ARQUIVO_DESTINATARIOS_PDF = "destinatarios.txt"
MODO_PDF_ATIVO = False

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
smtp_queue_lock = Lock()
json_lock = Lock()
proxy_lock = Lock()
uso_lock = Lock()
cooldown_lock = Lock()  # NOVO: Lock para cooldown
blacklist_lock = Lock()  # NOVO: Lock para blacklist

# Controle de uso simultâneo
smtps_em_uso = set()

# NOVO: Blacklist temporária - evita que mesmo SMTP tente mesmo email repetidamente
email_smtp_blacklist = {}  # {email: set(smtp_keys)}

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
    'emails_retry': 0,  # NOVO: Contador de retries
    'smtp_errors': {}
}

# Fila de SMTPs para envio em massa
smtp_queue_index = 0

# ============================================================================
# LÓGICA DE PDF INTEGRADA
# ============================================================================

try:
    pdf_config = pdfkit.configuration(wkhtmltopdf=PATH_TO_WKHTMLTOPF)
except Exception:
    pdf_config = None

pdfkit_options = {
    'quiet': '',
    'no-stop-slow-scripts': '',
    'disable-external-links': '',
    'enable-local-file-access': '',
    'allow': '.',
}

def convert_html_to_pdf(html_content, output_pdf_filename, email_destinatario):
    os.makedirs(TEMP_FOLDER, exist_ok=True)
    thread_id = threading.get_ident()
    temp_html_filename = f"temp_input_{thread_id}_{random.randint(1000, 9999)}.html"
    temp_html_path = os.path.join(TEMP_FOLDER, temp_html_filename)
    output_path = os.path.join(TEMP_FOLDER, output_pdf_filename)

    try:
        with open(temp_html_path, "w", encoding="utf-8") as f:
            f.write(html_content)

        if pdf_config is None:
            raise RuntimeError("wkhtmltopdf não configurado.")

        pdfkit.from_file(temp_html_path, output_path, configuration=pdf_config, options=pdfkit_options)
        
        if os.path.exists(temp_html_path):
            os.remove(temp_html_path)

        return output_path

    except Exception as e:
        if os.path.exists(temp_html_path):
            os.remove(temp_html_path)
        return None

def carregar_destinatarios_pdf():
    if not os.path.exists(ARQUIVO_DESTINATARIOS_PDF):
        return []
    try:
        with open(ARQUIVO_DESTINATARIOS_PDF, "r", encoding="utf-8") as file:
            lines = [line.strip() for line in file.readlines() if line.strip()]
            if not lines:
                return []
            header = [h.strip() for h in lines[0].split(';')]
            data_list = []
            for line in lines[1:]:
                values = [v.strip() for v in line.split(';')]
                if len(header) == len(values):
                    data_list.append(dict(zip(header, values)))
            return data_list
    except Exception:
        return []

def _safe_filename(name: str) -> str:
    return name.replace(" ", "_")

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

# ============================================================================
# NOVO: SISTEMA DE COOLDOWN PARA SMTPs COM ERRO TEMPORÁRIO
# ============================================================================

def carregar_cooldown_smtp():
    """Carrega SMTPs em cooldown do arquivo JSON."""
    if not os.path.exists(ARQUIVO_COOLDOWN_JSON):
        return {}
    
    with cooldown_lock:
        try:
            with open(ARQUIVO_COOLDOWN_JSON, 'r', encoding='utf-8') as f:
                return json.load(f)
        except (json.JSONDecodeError, FileNotFoundError):
            return {}

def salvar_cooldown_smtp(cooldown_data):
    """Salva SMTPs em cooldown no arquivo JSON."""
    with cooldown_lock:
        try:
            with open(ARQUIVO_COOLDOWN_JSON, 'w', encoding='utf-8') as f:
                json.dump(cooldown_data, f, indent=4)
        except Exception as e:
            print(f"{Colors.RED}❌ Erro ao salvar cooldown JSON: {e}{Colors.RESET}")

def adicionar_smtp_cooldown(smtp_key: str, motivo: str):
    """Adiciona um SMTP à fila de cooldown por 5-10 minutos."""
    cooldown_data = carregar_cooldown_smtp()
    tempo_atual = time.time()
    
    # Incrementa contador de erros
    if smtp_key not in cooldown_data:
        cooldown_data[smtp_key] = {
            'timestamp': tempo_atual,
            'motivo': motivo,
            'tentativas': 1
        }
    else:
        cooldown_data[smtp_key]['tentativas'] += 1
        cooldown_data[smtp_key]['timestamp'] = tempo_atual
        cooldown_data[smtp_key]['motivo'] = motivo
    
    salvar_cooldown_smtp(cooldown_data)
    print(f"{Colors.YELLOW}⏸️  SMTP em cooldown (5min): {smtp_key[:50]}... - {motivo}{Colors.RESET}")

def smtp_esta_em_cooldown(smtp_key: str) -> bool:
    """Verifica se um SMTP está em cooldown."""
    cooldown_data = carregar_cooldown_smtp()
    
    if smtp_key not in cooldown_data:
        return False
    
    tempo_atual = time.time()
    tempo_cooldown = cooldown_data[smtp_key]['timestamp']
    tempo_decorrido = tempo_atual - tempo_cooldown
    
    # Se passou o tempo de cooldown, remove da lista
    if tempo_decorrido >= SMTP_COOLDOWN_SECONDS:
        del cooldown_data[smtp_key]
        salvar_cooldown_smtp(cooldown_data)
        print(f"{Colors.GREEN}✓ SMTP saiu do cooldown: {smtp_key[:50]}...{Colors.RESET}")
        return False
    
    return True

def limpar_cooldowns_expirados():
    """Remove SMTPs cujo cooldown já expirou."""
    cooldown_data = carregar_cooldown_smtp()
    tempo_atual = time.time()
    
    smtps_para_remover = []
    for smtp_key, info in cooldown_data.items():
        tempo_decorrido = tempo_atual - info['timestamp']
        if tempo_decorrido >= SMTP_COOLDOWN_SECONDS:
            smtps_para_remover.append(smtp_key)
    
    for smtp_key in smtps_para_remover:
        del cooldown_data[smtp_key]
    
    if smtps_para_remover:
        salvar_cooldown_smtp(cooldown_data)
        print(f"{Colors.GREEN}✓ {len(smtps_para_remover)} SMTPs saíram do cooldown{Colors.RESET}")

# ============================================================================
# NOVO: BLACKLIST TEMPORÁRIA POR EMAIL
# ============================================================================

def adicionar_blacklist_email_smtp(email: str, smtp_key: str):
    """Adiciona um SMTP à blacklist temporária de um email específico."""
    with blacklist_lock:
        if email not in email_smtp_blacklist:
            email_smtp_blacklist[email] = set()
        email_smtp_blacklist[email].add(smtp_key)

def smtp_esta_blacklisted_para_email(email: str, smtp_key: str) -> bool:
    """Verifica se um SMTP está na blacklist de um email específico."""
    with blacklist_lock:
        if email not in email_smtp_blacklist:
            return False
        return smtp_key in email_smtp_blacklist[email]

def limpar_blacklist_email(email: str):
    """Remove um email da blacklist após envio bem-sucedido."""
    with blacklist_lock:
        if email in email_smtp_blacklist:
            del email_smtp_blacklist[email]

# ============================================================================
# FUNÇÃO DE SELEÇÃO DE SMTP CORRIGIDA
# ============================================================================

def obter_proximo_smtp_disponivel(smtps_list, email_atual=None):
    """
    Obtém o próximo SMTP disponível que:
    1. Não tenha enviado um email no último minuto (MIN_DELAY_SECONDS)
    2. Não esteja em cooldown (erro temporário)
    3. Não esteja na blacklist do email atual (se fornecido)
    """
    global smtp_queue_index
    
    # Limpa cooldowns expirados periodicamente
    limpar_cooldowns_expirados()
    
    tentativas_maximas = len(smtps_list) * 2  # Evita loop infinito
    tentativas = 0
    
    while tentativas < tentativas_maximas:
        tentativas += 1
        controle_data = carregar_controle_smtp()
        tempo_atual = time.time()
        
        # Verifica se há algum SMTP disponível
        smtp_mais_antigo = None
        menor_tempo_restante = float('inf')
        
        for smtp_data, ip_proxy in smtps_list:
            smtp_key = smtp_data
            
            # 1. Pula se estiver em uso
            with uso_lock:
                if smtp_key in smtps_em_uso:
                    continue
            
            # 2. NOVO: Pula se estiver em cooldown
            if smtp_esta_em_cooldown(smtp_key):
                continue
            
            # 3. NOVO: Pula se estiver na blacklist do email atual
            if email_atual and smtp_esta_blacklisted_para_email(email_atual, smtp_key):
                continue
            
            # 4. Verifica delay de envio
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
        if menor_tempo_restante < float('inf'):
            tempo_espera = min(menor_tempo_restante + 0.5, 10)  # Espera até 10s por vez
            print(f"{Colors.YELLOW}⏳ Todos os SMTPs em cooldown/ocupados. Esperando {tempo_espera:.1f}s...{Colors.RESET}")
            time.sleep(tempo_espera)
        else:
            time.sleep(2)
    
    print(f"{Colors.RED}❌ ATENÇÃO: Nenhum SMTP disponível após {tentativas} tentativas!{Colors.RESET}")
    return None, None

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
# FUNÇÕES DE PROXY - CORRIGIDAS PARA EVITAR VAZAMENTO
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
        print(f"{Colors.CYAN}✓ DNS Remoto ativado para evitar vazamento de informações{Colors.RESET}")
        return True
    else:
        print(f"{Colors.RED}❌ Credenciais do Proxy Rotativo não configuradas!{Colors.RESET}")
        return False

def obter_ip_real_proxy(proxy_username, proxy_password):
    """Obtém o IP real que está sendo usado através do proxy SOCKS5."""
    try:
        proxies = {
            'http': f'socks5://{proxy_username}:{proxy_password}@{PROXY_HOST}:{PROXY_PORT}',
            'https': f'socks5://{proxy_username}:{proxy_password}@{PROXY_HOST}:{PROXY_PORT}'
        }
        response = requests.get('https://api.ipify.org?format=json', proxies=proxies, timeout=5)
        if response.status_code == 200:
            return response.json().get('ip', 'UNKNOWN')
    except Exception as e:
        print(f"{Colors.YELLOW}⚠️  Erro ao obter IP real: {e}{Colors.RESET}")
    return 'UNKNOWN'

def obter_proximo_proxy():
    """Retorna um objeto proxy para a API rotativa da Oxylabs."""
    session_id = f"{int(time.time() * 1000)}{random.randint(10000, 99999)}"
    username_with_session = f"{PROXY_USER}-session-{session_id}"
    return {
        'host': PROXY_HOST, 'port': PROXY_PORT, 'ip': 'PENDING',
        'username': username_with_session, 'password': PROXY_PASS, 'rdns': True
    }

# ============================================================================
# FUNÇÕES AUXILIARES
# ============================================================================

def get_domain(email: str) -> str:
    """Extrai o domínio de um endereço de email."""
    try:
        return email.split('@')[1]
    except:
        return 'localhost.localdomain'

def test_smtp_login(server: str, port: int, email: str, password: str, 
                   use_ssl: bool, proxy: dict) -> bool:
    """Testa login SMTP através de proxy."""
    original_socket = socket.socket
    try:
        socks.set_default_proxy(socks.SOCKS5, proxy['host'], proxy['port'], rdns=True, username=proxy['username'], password=proxy['password'])
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
        return True
    except: return False
    finally: socket.socket = original_socket

def test_smtp_send(server: str, port: int, email: str, password: str, 
                  use_ssl: bool, proxy: dict) -> bool:
    """Testa envio de email através de proxy."""
    original_socket = socket.socket
    try:
        socks.set_default_proxy(socks.SOCKS5, proxy['host'], proxy['port'], rdns=True, username=proxy['username'], password=proxy['password'])
        socket.socket = socks.socksocket
        msg = MIMEMultipart('alternative')
        msg['Subject'] = "Teste SMTP"
        msg['From'] = formataddr(("Teste", email))
        msg['To'] = TEST_EMAIL_TO
        msg['Date'] = formatdate(localtime=True)
        msg['Message-ID'] = make_msgid(domain=get_domain(email))
        msg.attach(MIMEText("Teste de envio SMTP", 'plain', 'utf-8'))
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
        smtp.sendmail(email, [TEST_EMAIL_TO], msg.as_string())
        smtp.quit()
        return True
    except: return False
    finally: socket.socket = original_socket

def parse_smtp_data(smtp_data: str):
    """Parse de dados SMTP do formato servidor:porta;usuario;senha"""
    try:
        partes = smtp_data.strip().split(';')
        if len(partes) >= 3:
            servidor_porta = partes[0].split(':')
            servidor = servidor_porta[0]
            porta = int(servidor_porta[1]) if len(servidor_porta) > 1 else 0
            usuario = partes[1]
            senha = partes[2]
            return servidor, porta, usuario, senha
        else: return None
    except: return None

def marcar_smtp_erro(smtp_data: str):
    """Marca um SMTP como erro PERMANENTE para não ser mais usado."""
    with write_lock:
        with open(ARQUIVO_SMTP_ERRO, 'a', encoding='utf-8') as f:
            f.write(smtp_data + '\n')
    print(f"{Colors.RED}❌ SMTP marcado como ERRO PERMANENTE: {smtp_data[:50]}...{Colors.RESET}")

def replace_numero_placeholders(text: str) -> str:
    """Substitui placeholders {numero-X} por strings numéricas de X dígitos."""
    pattern = r'\{numero-(\d+)\}'
    def replacement(match):
        try:
            length = int(match.group(1))
            if length <= 0: return match.group(0)
            return ''.join(random.choice(string.digits) for _ in range(length))
        except ValueError: return match.group(0)
    return re.sub(pattern, replacement, text)

def replace_random_placeholders(text: str) -> str:
    """Substitui placeholders {random-X} por strings aleatórias de X caracteres."""
    pattern = r'\{random-(\d+)\}'
    def replacement(match):
        try:
            length = int(match.group(1))
            if length <= 0: return match.group(0)
            characters = string.ascii_uppercase + string.digits
            return ''.join(random.choice(characters) for _ in range(length))
        except ValueError: return match.group(0)
    return re.sub(pattern, replacement, text)

# ============================================================================
# FUNÇÃO DE ENVIO EM MASSA - TOTALMENTE CORRIGIDA COM SUPORTE A PDF
# ============================================================================

def enviar_email_massa(server: str, port: int, email: str, password: str, 
                       to_email_or_data, html_content: str, from_name: str, 
                       subject: str, proxy: dict, max_tentativas: int = 1) -> Tuple[bool, str, bool, str]:
    """Função de envio de email para o modo de envio em massa."""
    original_socket = socket.socket
    for tentativa in range(max_tentativas):
        try:
            socket.socket = original_socket
            socks.set_default_proxy(socks.SOCKS5, proxy['host'], proxy['port'], rdns=True, username=proxy['username'], password=proxy['password'])
            socket.socket = socks.socksocket
            
            to_email = to_email_or_data['EMAIL'] if isinstance(to_email_or_data, dict) else to_email_or_data
            msg = MIMEMultipart()
            
            if MODO_PDF_ATIVO and isinstance(to_email_or_data, dict):
                # --- LÓGICA DE PDF INTEGRADA ---
                cnpj = to_email_or_data.get('CNPJ', 'N/A')
                valor_total = to_email_or_data.get('VALOR_TOTAL', '0,00')
                codigo_barras_raw = to_email_or_data.get('CODIGO_BARRAS', '')
                nome_destinatario = to_email_or_data.get('NOME_DESTINATARIO', 'Destinatário')
                data_pagamento = to_email_or_data.get('DATA', date.today().strftime("%d/%m/%Y"))
                
                mes_referencia = '/'.join(data_pagamento.split('/')[1:3]) if data_pagamento else "MÊS/ANO"
                razao_social = nome_destinatario
                cnpj_formatado = cnpj
                numero_documento_aleatorio = f"{random.randint(1000000000000000, 9999999999999999)}"
                hoje = date.today().strftime("%d/%m/%Y")
                
                subject_pdf = f"Segue DAS - {cnpj_formatado} - {razao_social}"
                
                body_pdf = (html_content
                    .replace("{{EMAIL}}", to_email)
                    .replace("{{NOME}}", nome_destinatario)
                    .replace("{{CNPJ}}", cnpj_formatado)
                    .replace("{{VALOR}}", valor_total)
                    .replace("{{VALOR_TOTAL}}", valor_total)
                    .replace("{{CODIGO}}", ''.join(filter(str.isdigit, codigo_barras_raw)))
                    .replace("{{CODIGO_BARRAS_PONTUADO}}", codigo_barras_raw)
                    .replace("{{CPF}}", cnpj_formatado)
                    .replace("{{RAZAO_SOCIAL}}", razao_social)
                    .replace("{{DATA_PAGAMENTO}}", data_pagamento) 
                    .replace("{{NUMERO_DOCUMENTO_ALEATORIO}}", numero_documento_aleatorio)
                    .replace("{{DATA_DE_HOJE}}", hoje)
                )

                safe_cnpj = ''.join(filter(str.isdigit, cnpj_formatado)) or str(random.randint(1000000,9999997))
                pdf_filename = f"{safe_cnpj}_{random.randint(1000,9999)}.pdf"
                pdf_file_path = convert_html_to_pdf(body_pdf, pdf_filename, to_email)

                if not (pdf_file_path and os.path.exists(pdf_file_path)):
                    return False, "Falha ao gerar PDF", False, 'UNKNOWN'

                local_sender_id = random.randint(100000, 999999)
                local_sender_name = f"{from_name} - {local_sender_id}"

                msg["From"] = f'"{local_sender_name}" <{email}>'
                msg["To"] = to_email
                msg["Subject"] = subject_pdf
                
                simple_body = f"""
                <img src="https://senhorcontabil.com.br/wp-content/uploads/2025/05/O-que-e-o-Simples-Nacional-1536x863.jpg" width="175" height="75"><br>
                Imposto referente a:<br><br>
                RAZÃO SOCIAL: {razao_social}<br>
                CNPJ: {cnpj_formatado}<br><br>
                Informamos que o Documento de arrecadacao do Simples Nacional (DAS) referente ao mes de {mes_referencia} esta disponível para pagamento.<br>
                Data limite para pagamento: {data_pagamento}.<br><br>
                O boleto foi anexado a este e-mail para sua comodidade.<br><br>
                Protocolo de Atendimento: {numero_documento_aleatorio}
                """
                msg.attach(MIMEText(simple_body, "html"))

                with open(pdf_file_path, "rb") as attachment:
                    part = MIMEBase("application", "pdf")
                    part.set_payload(attachment.read())
                encoders.encode_base64(part)
                part.add_header("Content-Disposition", f"attachment; filename= {_safe_filename(os.path.basename(pdf_file_path))}")
                msg.attach(part)
            else:
                # --- LÓGICA ORIGINAL ---
                subject_final = replace_random_placeholders(subject)
                html_final = replace_random_placeholders(html_content)
                subject_final = replace_numero_placeholders(subject_final)
                html_final = replace_numero_placeholders(html_final)
                subject_final = subject_final.replace('{email}', to_email)
                html_final = html_final.replace('{email}', to_email)
                
                msg['Subject'] = subject_final
                msg['From'] = formataddr((from_name, email))
                msg['To'] = to_email
                msg.attach(MIMEText(html_final, 'html', 'utf-8'))
            
            msg['Date'] = formatdate(localtime=True)
            msg['Message-ID'] = make_msgid(domain=email.split('@')[-1])
            
            use_ssl = (port == 465)
            if use_ssl:
                smtp = smtplib.SMTP_SSL(server, port, timeout=TIMEOUT, context=ssl._create_unverified_context())
            else:
                smtp = smtplib.SMTP(server, port, timeout=TIMEOUT)
                if port == 587 or smtp.has_extn('STARTTLS'):
                    smtp.starttls(context=ssl._create_unverified_context())
            
            smtp.login(email, password)
            smtp.sendmail(email, [to_email], msg.as_string())
            smtp.quit()
            return True, "Sucesso", False, obter_ip_real_proxy(proxy['username'], proxy['password'])
        except Exception as e: return False, str(e), True, 'UNKNOWN'
        finally: socket.socket = original_socket
    return False, "Falha após todas as tentativas", False, 'UNKNOWN'

# ============================================================================
# WORKER THREAD PARA ENVIO EM MASSA - TOTALMENTE CORRIGIDO
# ============================================================================

def worker_envio_massa(thread_id: int, queue: Queue, smtps_list: list, html_content: str):
    """Thread worker para envio em massa com controle de taxa RIGOROSO por SMTP."""
    while True:
        smtp_data_original = None
        try:
            try: email = queue.get(timeout=2)
            except Empty: break
            
            email_str = email['EMAIL'] if isinstance(email, dict) else email
            smtp_data_original, _ = obter_proximo_smtp_disponivel(smtps_list, email_atual=email_str)
            if smtp_data_original is None:
                queue.put(email); time.sleep(3); queue.task_done(); continue
            
            partes = smtp_data_original.strip().split(';')
            servidor_porta = partes[0].split(':')
            servidor = servidor_porta[0]
            porta = int(servidor_porta[1]) if len(servidor_porta) > 1 else 587
            usuario, senha = partes[1], partes[2]
            
            proxy_rotativo = obter_proximo_proxy()
            sucesso, msg, is_smtp_error, ip_usado = enviar_email_massa(servidor, porta, usuario, senha, email, html_content, FROM_NAME, ASSUNTO, proxy_rotativo)
            
            if sucesso:
                salvar_last_email(email_str); limpar_blacklist_email(email_str)
                with stats_lock: stats['emails_enviados'] += 1
                print(f"{Colors.GREEN}✓ [{stats['emails_enviados']}] Enviado: {email_str[:40]} | SMTP: {usuario[:30]} | {Colors.CYAN}IP: {ip_usado}{Colors.RESET} | Thread: {thread_id}{Colors.RESET}")
                queue.task_done()
            else:
                adicionar_blacklist_email_smtp(email_str, smtp_data_original); queue.put(email)
                with stats_lock: stats['emails_falhas'] += 1; stats['emails_retry'] += 1
                if is_smtp_error:
                    if "Autenticação" in msg or "Inválido" in msg: marcar_smtp_erro(smtp_data_original)
                    else: adicionar_smtp_cooldown(smtp_data_original, msg)
                queue.task_done()
        except Exception as e:
            if email: queue.put(email); queue.task_done()
        finally:
            if smtp_data_original:
                with uso_lock: smtps_em_uso.discard(smtp_data_original)

# ============================================================================
# FUNÇÃO PRINCIPAL DE ENVIO EM MASSA
# ============================================================================

def enviar_lista_emails():
    """Função principal para enviar lista de emails"""
    global stats, smtp_queue_index, proxy_queue_index
    print("\n" + "="*80)
    print(f"{Colors.BOLD}{Colors.CYAN}📧 ENVIO EM MASSA v3.16 - SISTEMA CORRIGIDO{Colors.RESET}")
    print("="*80)
    if not carregar_proxies(): return
    
    smtps = []
    with open(ARQUIVO_SMTPS_ENVIO, 'r', encoding='utf-8') as f:
        for linha in f:
            linha = linha.strip()
            if linha and not linha.startswith('#'):
                partes = linha.split(';')
                if len(partes) >= 3: smtps.append((f"{partes[0]};{partes[1]};{partes[2]}", None))
    
    if MODO_PDF_ATIVO:
        emails = carregar_destinatarios_pdf()
        if not emails: print(f"\n{Colors.RED}❌ Arquivo '{ARQUIVO_DESTINATARIOS_PDF}' não encontrado ou vazio!{Colors.RESET}"); return
    else:
        with open(ARQUIVO_EMAILS, 'r', encoding='utf-8') as f:
            emails = [linha.strip() for linha in f if linha.strip() and '@' in linha]
    
    with open(ARQUIVO_HTML, 'r', encoding='utf-8') as f: html_content = f.read()
    if not smtps or not emails: print(f"\n{Colors.RED}❌ SMTPs ou Emails não encontrados!{Colors.RESET}"); return
    
    input(f"\n{Colors.YELLOW}⚠️  Pressione ENTER para iniciar o envio...{Colors.RESET}")
    stats['emails_enviados'] = 0; stats['emails_falhas'] = 0; stats['emails_retry'] = 0
    email_smtp_blacklist.clear()
    
    queue = Queue()
    for email in emails: queue.put(email)
    threads = [Thread(target=worker_envio_massa, args=(i + 1, queue, smtps, html_content)) for i in range(MAX_WORKERS)]
    for t in threads: t.start()
    queue.join()
    for t in threads: t.join()
    print(f"\n{Colors.GREEN}✓ Envio finalizado!{Colors.RESET}")

# ============================================================================
# WORKER THREAD PARA VALIDAÇÃO
# ============================================================================

def worker_thread(thread_id: int, queue: Queue):
    """Thread worker para validação de SMTPs."""
    while True:
        smtp_data = queue.get()
        if smtp_data is None: queue.task_done(); break
        proxy = obter_proximo_proxy()
        parsed = parse_smtp_data(smtp_data)
        if not parsed:
            with stats_lock: stats['invalid'] += 1; stats['processed'] += 1
            queue.task_done(); continue
        servidor, porta_inicial, usuario, senha = parsed
        for port, use_ssl in SMTP_PORTS:
            if porta_inicial != 0 and port != porta_inicial: continue
            if test_smtp_login(servidor, port, usuario, senha, use_ssl, proxy):
                with stats_lock: stats['valid_login'] += 1; stats['by_port'][port] = stats['by_port'].get(port, 0) + 1
                if test_smtp_send(servidor, port, usuario, senha, use_ssl, proxy):
                    with stats_lock: stats['valid_send'] += 1
                    with write_lock:
                        with open('smtp_envio.txt', 'a', encoding='utf-8') as f: f.write(f"{servidor}:{port};{usuario};{senha}\n")
                    print(f"{Colors.GREEN}✓ [{stats['processed']}/{stats['total']}] {servidor}:{port};{usuario[:30]}... - ENVIO OK!{Colors.RESET}")
                else:
                    with write_lock:
                        with open('smtp_validos.txt', 'a', encoding='utf-8') as f: f.write(f"{servidor}:{port};{usuario};{senha}\n")
                    print(f"{Colors.BLUE}⚠ [{stats['processed']}/{stats['total']}] {servidor}:{port};{usuario[:30]}... - LOGIN OK (envio falhou){Colors.RESET}")
                break
        else:
            with stats_lock: stats['invalid'] += 1
            print(f"{Colors.RED}❌ [{stats['processed']}/{stats['total']}] {servidor}:{porta_inicial};{usuario[:30]}... - LOGIN FALHOU!{Colors.RESET}")
        with stats_lock: stats['processed'] += 1
        queue.task_done()

def validar_smtps():
    """Função principal para validar SMTPs (login e envio)"""
    print("\n" + "="*80); print(f"{Colors.BOLD}{Colors.CYAN}🔐 VALIDAÇÃO SMTP v3.16{Colors.RESET}"); print("="*80)
    if not carregar_proxies(): return
    credentials = []
    if not os.path.exists("validos_geral.txt"): return
    with open("validos_geral.txt", 'r', encoding='utf-8') as f:
        for linha in f:
            if linha.strip() and ';' in linha: credentials.append(linha.strip())
    stats['total'] = len(credentials); queue = Queue()
    for cred in credentials: queue.put(cred)
    for _ in range(MAX_WORKERS): queue.put(None)
    threads = [Thread(target=worker_thread, args=(i + 1, queue)) for i in range(MAX_WORKERS)]
    for t in threads: t.start()
    for t in threads: t.join()

# ============================================================================
# MENU PRINCIPAL
# ============================================================================

def menu_principal():
    """Menu principal do programa"""
    while True:
        print("\n" + "="*80)
        print(f"{Colors.BOLD}{Colors.CYAN}VALIDADOR E ENVIADOR SMTP v3.16 - CORRIGIDO{Colors.RESET}")
        print("="*80)
        print(f"\n{Colors.YELLOW}Escolha uma opção:{Colors.RESET}\n")
        print(f"  {Colors.GREEN}1{Colors.RESET} - Validar SMTPs (login + envio)")
        print(f"  {Colors.GREEN}2{Colors.RESET} - Enviar lista de emails em massa")
        print(f"  {Colors.GREEN}3{Colors.RESET} - Enviar lista com PDF (destinatarios.txt)")
        print(f"  {Colors.GREEN}4{Colors.RESET} - Limpar arquivos de controle")
        print(f"  {Colors.GREEN}5{Colors.RESET} - Ver estatísticas de cooldown")
        print(f"  {Colors.RED}0{Colors.RESET} - Sair")
        print("\n" + "="*80)
        try:
            opcao = input(f"\n{Colors.CYAN}Digite sua opção: {Colors.RESET}").strip()
            if opcao == '1': validar_smtps()
            elif opcao == '2': enviar_lista_emails()
            elif opcao == '3':
                global MODO_PDF_ATIVO
                MODO_PDF_ATIVO = True
                enviar_lista_emails()
                MODO_PDF_ATIVO = False
            elif opcao == '4': limpar_controles()
            elif opcao == '5': ver_estatisticas_cooldown()
            elif opcao == '0': break
        except KeyboardInterrupt: break

def limpar_controles():
    for f in [ARQUIVO_CONTROLE_JSON, ARQUIVO_COOLDOWN_JSON, ARQUIVO_LAST_EMAIL]:
        if os.path.exists(f): os.remove(f)
    print("Controles limpos.")

def ver_estatisticas_cooldown():
    data = carregar_cooldown_smtp()
    if not data: print("Nenhum SMTP em cooldown."); return
    for k, v in data.items(): print(f"{k}: {v['motivo']}")

if __name__ == "__main__":
    menu_principal()
