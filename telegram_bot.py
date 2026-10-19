"""
Cripdex v2 - Bot de Telegram para el mercado cripto (SOLO informa, nunca compra ni vende).
Corre en GitHub Actions: cada ejecucion escucha mensajes ~4,6 min y se relanza sola.
El archivo de estado (cartera, alertas, usuarios) se guarda CIFRADO con una clave
derivada de tu TELEGRAM_TOKEN, para que no sea legible aunque el repositorio sea publico.
"""
import os, io, re, sys, json, math, time, html, base64, hashlib, signal, threading, unicodedata
import xml.etree.ElementTree as ET
from datetime import datetime, timezone, timedelta
from http.server import BaseHTTPRequestHandler, HTTPServer
from email.utils import parsedate_to_datetime
from concurrent.futures import ThreadPoolExecutor
import requests
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle

try:
    from cryptography.fernet import Fernet
except ImportError:  # se comprueba en main()
    Fernet = None

TOKEN = os.getenv("TELEGRAM_TOKEN", "")
RUN_SECONDS = int(os.getenv("RUN_SECONDS", "270"))   # 0 = funcionar sin parar (para un hosting)
STATE_KEY = os.getenv("STATE_KEY") or TOKEN          # clave que cifra el estado
TZ_H = float(os.getenv("BOT_TZ_OFFSET", "-4"))       # hora de Venezuela (UTC-4)
TZ = timezone(timedelta(hours=TZ_H))
SUPABASE_URL = os.getenv("SUPABASE_URL", "").rstrip("/")   # opcional: guarda el estado fuera del servidor
SUPABASE_KEY = os.getenv("SUPABASE_KEY", "")
REMOTE = bool(SUPABASE_URL and SUPABASE_KEY)
DATA = "https://data-api.binance.vision"      # precios publicos de Binance
DEX = "https://api.dexscreener.com"           # memecoins (publico, sin clave)
TG = f"https://api.telegram.org/bot{TOKEN}"
STATE_FILE = os.getenv("STATE_FILE") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "telegram_state.json")
UA = {"User-Agent": "Mozilla/5.0"}

MOVER_MIN = 3.0            # el bot detecta movimientos desde +-3% (cada usuario elige su umbral)
MOVER_MIN_VOL = 3_000_000  # solo monedas con mas de 3M USDT de volumen diario
VOL_SPIKE = 4.0            # volumen de la ultima hora >= 4 veces su promedio
DAILY_HOUR_UTC = 12        # resumen diario: 12:00 UTC = 8:00 a. m. en Venezuela
FEE = 0.001                # comision Binance 0.1% por operacion
INTERVALS = ["15m", "1h", "4h", "1d"]
STABLES = {"USDC", "FDUSD", "TUSD", "USDP", "DAI", "BUSD", "EUR", "USD1", "USDE", "XUSD", "AEUR"}
USD_NAMES = {"USD", "USDT", "USDC", "DOLAR", "DOLARES"}
DISCLAIMER = "⚠️ Es información, no consejo financiero. Nadie puede garantizar ganancias."
FEEDS = [("CoinDesk", "https://www.coindesk.com/arc/outboundfeeds/rss/"),
         ("Cointelegraph", "https://cointelegraph.com/rss")]
DEFAULT_PREFS = {"mov_on": True, "mov": 5.0, "memes": True, "vol": True, "daily": True}
OWNER_ID = int(os.getenv("OWNER_ID", "0") or 0)   # tu ID de Telegram (usa /miid para verlo)
HEALTH = {"last_ok_save": 0.0, "save_fail_streak": 0, "last_error": "", "task_errors": 0,
          "started": time.time()}
OWNER_SENT = {}
SESSION = requests.Session()   # conexión HTTP reutilizable: más rápido con Binance, Telegram y DexScreener
# OJO: no le pongas un User-Agent de navegador a la Session: Supabase rechaza sus llaves secretas si parece un navegador.
SB_UA = "cripdex-bot/3 (servidor)"
BOT = {"user": os.getenv("BOT_USERNAME", "").lstrip("@")}   # se completa solo con getMe
BINANCE_REF_URL = os.getenv("BINANCE_REF_URL", "")          # tu enlace de referido de Binance (opcional)
DAILY_P2P_FIAT = os.getenv("DAILY_P2P_FIAT", "VES")         # "" = sin línea de dólar P2P en el resumen diario
P2P_URL = "https://p2p.binance.com/bapi/c2c/v2/friendly/c2c/adv/search"
P2P_FIATS = ["VES", "ARS", "COP", "EUR", "MXN", "BRL", "PEN", "CLP", "USD"]
FIAT_SYMBOL = {"VES": "Bs", "ARS": "AR$", "COP": "COL$", "EUR": "€", "MXN": "MX$", "BRL": "R$",
               "PEN": "S/", "CLP": "CL$", "USD": "US$"}
LIMITS = {"free": {"alerts": 10, "watch": 15, "port": 20},
          "pro": {"alerts": 50, "watch": 60, "port": 100}}


# ------------------------- utilidades -------------------------
def _http():
    """Session en el hilo principal; en hilos secundarios (escáner) requests suelto, que es lo más seguro."""
    return SESSION if threading.current_thread() is threading.main_thread() else requests


def get(url, params=None, tries=2):
    for _ in range(tries):
        try:
            r = _http().get(url, params=params, timeout=15, headers=UA)
            if r.status_code == 200:
                return r.json()
        except (requests.RequestException, ValueError):
            pass
        time.sleep(1)
    return None


def get_bytes(url):
    try:
        r = _http().get(url, timeout=15, headers=UA)
        return r.content if r.status_code == 200 else None
    except requests.RequestException:
        return None


def esc(s):
    return html.escape(str(s))


def safe(e):
    """Quita el token de los mensajes de error (los registros pueden ser publicos)."""
    s = str(e)
    for secret in (TOKEN, SUPABASE_KEY):
        if secret:
            s = s.replace(secret, "***")
    return s


def safe_url(u):
    return u if isinstance(u, str) and u.startswith("https://") else "https://dexscreener.com"


def fp(p):
    if p >= 1000:
        return f"{p:,.2f}"
    if p >= 1:
        return f"{p:.4f}"
    if p >= 0.01:
        return f"{p:.5f}"
    return f"{p:.8f}"


def fm(n):
    for u, d in (("B", 1e9), ("M", 1e6), ("K", 1e3)):
        if abs(n) >= d:
            return f"{n / d:.1f}{u}"
    return f"{n:.0f}"


def fq(q):
    return f"{q:,.2f}" if q >= 1000 else f"{q:.6g}"


def pc(x):
    return f"{'🟢' if x >= 0 else '🔴'} {x:+.2f}%"


def num(s):
    return float(str(s).replace(",", ".").replace("$", ""))


def norm_base(s):
    s = re.sub(r"[^A-Za-z0-9]", "", s).upper()
    return s[:-4] if s.endswith("USDT") and len(s) > 4 else s


def norm_sym(s):
    return norm_base(s) + "USDT"


# ------------------------- Telegram -------------------------
def tg(method, timeout=30, **data):
    try:
        return SESSION.post(f"{TG}/{method}", json=data, timeout=timeout).json()
    except Exception as e:
        print("Telegram error:", safe(e))
        return {}


def trim(text, n=3900):
    """Recorta mensajes largos por una linea completa (asi no se rompe el HTML)."""
    if len(text) <= n:
        return text
    cut = text.rfind("\n", 0, n)
    return text[:cut if cut > 0 else n] + "\n…"


def send(chat, text, buttons=None):
    text = trim(text)
    data = {"chat_id": chat, "text": text, "parse_mode": "HTML", "disable_web_page_preview": True}
    if buttons:
        data["reply_markup"] = {"inline_keyboard": buttons}
    r = {}
    for _ in range(3):
        r = tg("sendMessage", **data)
        if r.get("ok") is not False:
            break
        code, desc = r.get("error_code"), str(r.get("description", ""))
        if code == 429:   # Telegram pide esperar un momento
            time.sleep(min(int((r.get("parameters") or {}).get("retry_after", 2)), 10))
        elif code == 400 and "parse entities" in desc and "parse_mode" in data:
            data["text"] = html.unescape(re.sub(r"<[^>]+>", "", text))   # reenviar como texto simple
            data.pop("parse_mode")
        else:
            break
    return r


def dead_chat(r):
    """True solo si el usuario bloqueó el bot o el chat ya no existe."""
    if not r or r.get("ok") is not False:
        return False
    return r.get("error_code") == 403 or "chat not found" in str(r.get("description", "")).lower()


def notify(state, chat, text, buttons=None):
    if dead_chat(send(chat, text, buttons)) and chat in state["subs"]:
        state["subs"].remove(chat)


def photo_id(r):
    """file_id de la foto enviada: sirve para reenviarla a otros sin subirla de nuevo."""
    try:
        return r["result"]["photo"][-1]["file_id"]
    except (KeyError, IndexError, TypeError):
        return None


def send_photo(chat, png, caption="", buttons=None):
    """png puede ser bytes (se sube) o un texto con el file_id de una foto ya subida."""
    data = {"chat_id": chat, "caption": caption[:1000], "parse_mode": "HTML"}
    if buttons:
        data["reply_markup"] = json.dumps({"inline_keyboard": buttons})
    try:
        if isinstance(png, str):
            data["photo"] = png
            return SESSION.post(f"{TG}/sendPhoto", data=data, timeout=30).json()
        return SESSION.post(f"{TG}/sendPhoto", data=data, files={"photo": ("g.png", png, "image/png")},
                            timeout=60).json()
    except Exception as e:
        print("Foto error:", safe(e))
        return {}


def btn(text, cmd=None, url=None):
    return {"text": text, "url": url} if url else {"text": text, "callback_data": f"cmd:{cmd}"}


def binance_buttons(base):
    """Filas de botones hacia Binance. Si configuraste BINANCE_REF_URL, agrega un botón de referido bien marcado."""
    rows = [[btn(f"Ver {base} en Binance", url=f"https://www.binance.com/en/trade/{base}_USDT")]]
    if BINANCE_REF_URL.startswith("https://"):
        rows.append([btn("Crear cuenta (enlace de referido)", url=BINANCE_REF_URL)])
    return rows


MENU = [
    [btn("📈 Top del día", "/top"), btn("🗺 Mapa de calor", "/heatmap")],
    [btn("🐸 Memecoins", "/memes"), btn("📰 Noticias", "/noticias")],
    [btn("₿ Análisis BTC", "/analisis BTC"), btn("🔍 Escáner", "/escaner")],
    [btn("💵 Dólar P2P", "/p2p"), btn("📊 Futuros BTC", "/futuros BTC")],
    [btn("💼 Mi cartera", "/cartera"), btn("⚙️ Mis avisos", "/config")],
    [btn("🧰 Herramientas", "/herramientas"), btn("❓ Ayuda", "/ayuda")],
]

BOT_COMMANDS = [
    ("start", "Menú principal"), ("top", "Monedas que más suben y bajan hoy"),
    ("heatmap", "Mapa de calor del mercado"), ("precio", "Precio de una o varias monedas"),
    ("grafico", "Gráfico con indicadores, soporte y resistencia"), ("analisis", "Análisis técnico en español sencillo"),
    ("comparar", "Compara hasta 4 monedas"), ("escaner", "Sobrecompradas, sobrevendidas y volumen raro"),
    ("p2p", "Dólar en Binance P2P (VES, ARS, COP, EUR, MXN…)"), ("futuros", "Funding y open interest explicados"),
    ("contrato", "Revisión básica de un contrato (antiestafas)"), ("memes", "Memecoins con filtros anti-estafa"),
    ("noticias", "Últimas noticias cripto"), ("mercado", "Ánimo general del mercado"),
    ("cartera", "Tu cartera y ganancias"), ("agregar", "Agregar una moneda a tu cartera"),
    ("meta", "Tu meta de cartera con barra de progreso"), ("tarjeta", "Imagen de tu cartera para compartir"),
    ("lista", "Tu lista de seguimiento"), ("alerta", "Alerta de precio"), ("alertap2p", "Alerta del dólar P2P"),
    ("config", "Configurar tus avisos"), ("glosario", "Qué significa cada término"),
    ("herramientas", "Calculadoras y simulador DCA"), ("pro", "Tu plan y límites"),
    ("terminos", "Términos y privacidad"), ("ayuda", "Todos los comandos"),
]


# ------------------------- estado (cifrado) -------------------------
def _fernet():
    if Fernet is None or not STATE_KEY:
        return None
    key = base64.urlsafe_b64encode(hashlib.sha256(("estado:" + STATE_KEY).encode()).digest())
    return Fernet(key)


def _sb_headers():
    h = {"apikey": SUPABASE_KEY, "Content-Type": "application/json", "User-Agent": SB_UA}
    if not SUPABASE_KEY.startswith("sb_"):   # las llaves nuevas (sb_...) no llevan Authorization
        h["Authorization"] = "Bearer " + SUPABASE_KEY
    return h


def remote_load():
    """(ok, datos). ok=False si no se pudo leer: en ese caso NO se debe arrancar de cero."""
    for _ in range(3):
        try:
            r = SESSION.get(f"{SUPABASE_URL}/rest/v1/bot_state", params={"id": "eq.main", "select": "data"},
                             headers=_sb_headers(), timeout=15)
            if r.status_code == 200:
                rows = r.json()
                return True, (rows[0]["data"].encode() if rows else None)
            print("Supabase leer:", r.status_code, r.text[:120])
        except Exception as e:
            print("Supabase leer error:", safe(e))
        time.sleep(2)
    return False, None


def remote_save(raw):
    try:
        h = _sb_headers()
        h["Prefer"] = "resolution=merge-duplicates"
        r = SESSION.post(f"{SUPABASE_URL}/rest/v1/bot_state", headers=h,
                          json={"id": "main", "data": raw.decode()}, timeout=15)
        if r.status_code in (200, 201, 204):
            HEALTH.update(last_ok_save=time.time(), save_fail_streak=0, last_error="")
            return True
        msg = f"Supabase {r.status_code}: {r.text[:120]}"
    except Exception as e:
        msg = "Supabase error: " + safe(e)
    HEALTH["save_fail_streak"] += 1
    HEALTH["last_error"] = msg[:300]
    print(msg)
    return False


def notify_owner(key, text):
    """Avisa al administrador por Telegram, como mucho una vez cada 30 min por tipo de aviso."""
    if not OWNER_ID:
        return
    now = time.time()
    if now - OWNER_SENT.get(key, 0) < 1800:
        return
    OWNER_SENT[key] = now
    send(OWNER_ID, text)


def load_state():
    base = {"offset": 0, "subs": [], "prefs": {}, "alerts": [], "next_id": 1, "snaps": [], "cool": {},
            "last": {}, "port": {}, "watch": {}, "daily": "",
            "pro": {}, "goals": {}, "stats": {"cmds": {}, "seen": {}}}   # pro = {id_chat: vencimiento}
    raw = None
    if REMOTE:
        ok, raw = remote_load()
        if not ok:
            raise SystemExit("No pude leer el estado de Supabase; no arranco para no borrar tus datos.")
    if raw is None and os.path.exists(STATE_FILE):   # primera vez con Supabase: migra el archivo local
        with open(STATE_FILE, "rb") as f:
            raw = f.read()
    if raw:
        data, fer = None, _fernet()
        if fer:
            try:
                data = json.loads(fer.decrypt(raw))
            except Exception:
                data = None
        if data is None:
            try:
                data = json.loads(raw)   # formato viejo sin cifrar (se cifra al guardar)
            except Exception:
                data = None
        if data is None and raw.strip():   # ilegible (¿clave distinta?): guardar copia antes de empezar de cero
            try:
                with open(STATE_FILE + ".corrupto", "wb") as f:
                    f.write(raw)
            except OSError:
                pass
        if isinstance(data, dict):
            base.update(data)
    base["stats"].setdefault("cmds", {})
    base["stats"].setdefault("seen", {})
    return base


_saved = {"h": None, "t": 0.0}


def save_state(s, force=False):
    """Guarda solo si algo cambió. Con Supabase: máximo una vez cada 10 s (y siempre al apagar)."""
    now = time.time()
    s["cool"] = {k: v for k, v in s["cool"].items() if now - v < 172800}
    h = hashlib.sha256(json.dumps({k: v for k, v in s.items() if k != "last"}, sort_keys=True).encode()).hexdigest()
    if not force and h == _saved["h"]:
        return
    raw = json.dumps(s).encode()
    fer = _fernet()
    if fer:
        raw = fer.encrypt(raw)
    with open(STATE_FILE, "wb") as f:
        f.write(raw)
    if not REMOTE:
        _saved["h"] = h
    elif force or now - _saved["t"] >= 10:
        if remote_save(raw):
            _saved.update(h=h, t=now)
        elif HEALTH["save_fail_streak"] >= 3:
            notify_owner("save", "⚠️ <b>Cripdex no puede guardar en la nube.</b>\n"
                         + esc(HEALTH["last_error"]) + "\nRevisa SUPABASE_URL y SUPABASE_KEY en Render.")


def pref(state, chat):
    p = state["prefs"].setdefault(str(chat), {})
    for k, v in DEFAULT_PREFS.items():
        p.setdefault(k, v)
    return p


def cooled(state, key, hours):
    now = time.time()
    if now - state["cool"].get(key, 0) >= hours * 3600:
        state["cool"][key] = now
        return True
    return False


def broadcast(state, kind, text, buttons=None, photo=None):
    fid = None   # la imagen se sube una sola vez; a los demás se les manda su file_id
    for chat in list(state["subs"]):
        if not pref(state, chat).get(kind, True):
            continue
        if photo:
            r = send_photo(chat, fid or photo, "")
            if fid and r.get("ok") is False:   # el file_id falló: subir de nuevo
                fid = None
                r = send_photo(chat, photo, "")
            if not fid:
                fid = photo_id(r)
        if dead_chat(send(chat, text, buttons)):
            state["subs"].remove(chat)


# ------------------------- datos de mercado -------------------------
_cache = {}


def cached(key, ttl, fn):
    """Guarda el resultado de fn() durante ttl segundos (no guarda resultados vacíos)."""
    now = time.time()
    c = _cache.get(key)
    if c and now - c[0] < ttl:
        return c[1]
    v = fn()
    if v:
        _cache[key] = (now, v)
        if len(_cache) > 80:   # limpieza para que no crezca sin fin
            for k in [k for k, (t, _) in _cache.items() if now - t > 900]:
                _cache.pop(k, None)
    return v


def market(min_vol=5e6):
    c = _cache.get("mkt")
    if c and time.time() - c[0] < 60:
        data = c[1]
    else:
        data = get(f"{DATA}/api/v3/ticker/24hr") or []
        _cache["mkt"] = (time.time(), data)
    out = []
    for x in data:
        s = x["symbol"]
        if not s.endswith("USDT") or s[:-4] in STABLES:
            continue
        try:
            row = dict(sym=s, base=s[:-4], price=float(x["lastPrice"]), chg=float(x["priceChangePercent"]),
                       qv=float(x["quoteVolume"]), hi=float(x["highPrice"]), lo=float(x["lowPrice"]))
        except (KeyError, ValueError):
            continue
        if row["qv"] >= min_vol and row["price"] > 0:
            out.append(row)
    return out


def prices():
    return {x["base"]: x for x in market(0)}


def ticker(sym):
    x = get(f"{DATA}/api/v3/ticker/24hr", {"symbol": sym})
    if not x or "lastPrice" not in x:
        return None
    return dict(sym=sym, base=sym[:-4], price=float(x["lastPrice"]), chg=float(x["priceChangePercent"]),
                qv=float(x["quoteVolume"]), hi=float(x["highPrice"]), lo=float(x["lowPrice"]))


def klines(sym, interval, limit):
    d = get(f"{DATA}/api/v3/klines", {"symbol": sym, "interval": interval, "limit": limit})
    if not isinstance(d, list) or len(d) < 5:
        return None
    return [dict(t=k[0] / 1000, o=float(k[1]), h=float(k[2]), l=float(k[3]), c=float(k[4]), v=float(k[5]))
            for k in d]


def klines_many(syms, interval, limit):
    with ThreadPoolExecutor(6) as ex:
        res = list(ex.map(lambda s: klines(s, interval, limit), syms))
    return dict(zip(syms, res))


# ------------------------- indicadores -------------------------
def ema(vals, n):
    k = 2 / (n + 1)
    out = [vals[0]]
    for v in vals[1:]:
        out.append(v * k + out[-1] * (1 - k))
    return out


def rsi_series(vals, n=14):
    out = [None] * len(vals)
    if len(vals) < n + 1:
        return out
    g = l = 0.0
    for i in range(1, n + 1):
        d = vals[i] - vals[i - 1]
        g += max(d, 0)
        l += max(-d, 0)
    ag, al = g / n, l / n
    out[n] = 100.0 if al == 0 else 100 - 100 / (1 + ag / al)
    for i in range(n + 1, len(vals)):
        d = vals[i] - vals[i - 1]
        ag = (ag * (n - 1) + max(d, 0)) / n
        al = (al * (n - 1) + max(-d, 0)) / n
        out[i] = 100.0 if al == 0 else 100 - 100 / (1 + ag / al)
    return out


def rsi(vals, n=14):
    return rsi_series(vals, n)[-1] if len(vals) >= n + 2 else None


def macd_hist(vals):
    line = [a - b for a, b in zip(ema(vals, 12), ema(vals, 26))]
    sig = ema(line, 9)
    return line[-1] - sig[-1]


def bollinger(vals, n=20, k=2):
    up, lo = [], []
    for i in range(len(vals)):
        w = vals[max(0, i - n + 1):i + 1]
        m = sum(w) / len(w)
        sd = (sum((x - m) ** 2 for x in w) / len(w)) ** 0.5
        up.append(m + k * sd)
        lo.append(m - k * sd)
    return up, lo


# ------------------------- graficos -------------------------
BG, FG = "#0e1621", "#c9d1d9"


def _style(ax):
    ax.set_facecolor(BG)
    ax.tick_params(colors=FG, labelsize=8)
    for sp in ax.spines.values():
        sp.set_color("#2a3441")
    ax.grid(color="#1c2733", linewidth=0.6)


def _labels(ax, kl, interval):
    fmt = "%d/%m" if interval == "1d" else "%d/%m %Hh"
    step = max(1, len(kl) // 6)
    idx = list(range(0, len(kl), step))
    ax.set_xticks(idx)
    ax.set_xticklabels([datetime.fromtimestamp(kl[i]["t"], TZ).strftime(fmt) for i in idx])
    if interval != "1d":
        ax.set_xlabel(f"hora UTC{TZ_H:+g}" + (" (Venezuela)" if TZ_H == -4 else ""), color=FG, fontsize=8)


def watermark_text():
    return "Generado por @" + (BOT["user"] or "Cripdex")


def to_png(fig):
    fig.text(0.99, 0.004, watermark_text(), ha="right", va="bottom", fontsize=8, color=FG, alpha=0.5)
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=110, facecolor=BG, bbox_inches="tight")
    plt.close(fig)
    return buf.getvalue()


def sr_levels(full, price):
    """Soporte y resistencia: el mínimo y el máximo locales recientes más cercanos al precio."""
    seg, w = full[-120:], 4
    highs, lows = [], []
    for i in range(w, len(seg) - w):
        win = seg[i - w:i + w + 1]
        if seg[i]["h"] >= max(k["h"] for k in win):
            highs.append(seg[i]["h"])
        if seg[i]["l"] <= min(k["l"] for k in win):
            lows.append(seg[i]["l"])
    res = min([h for h in highs if h > price * 1.001], default=None)
    sup = max([l for l in lows if l < price * 0.999], default=None)
    if res is None:
        res = max(k["h"] for k in seg)
    if sup is None:
        sup = min(k["l"] for k in seg)
    return sup, res


def chart_candles(sym, kl, interval, full):
    n = len(kl)
    closes = [k["c"] for k in full]
    e20, e50 = ema(closes, 20)[-n:], ema(closes, 50)[-n:]
    up, lo = bollinger(closes)
    up, lo = up[-n:], lo[-n:]
    rs = [float("nan") if v is None else v for v in rsi_series(closes)[-n:]]
    fig, (ax, av, ar) = plt.subplots(3, 1, figsize=(8, 7.5), sharex=True,
                                     gridspec_kw={"height_ratios": [4, 1, 1.4]})
    fig.patch.set_facecolor(BG)
    for i, k in enumerate(kl):
        col = "#2ecc71" if k["c"] >= k["o"] else "#e74c3c"
        ax.vlines(i, k["l"], k["h"], color=col, linewidth=1)
        ax.bar(i, max(abs(k["c"] - k["o"]), k["c"] * 1e-5), bottom=min(k["o"], k["c"]), color=col, width=0.7)
        av.bar(i, k["v"], color=col, width=0.7)
    ax.fill_between(range(n), lo, up, color="#8e44ad", alpha=0.13, label="Bandas de Bollinger")
    ax.plot(e20, color="#f1c40f", linewidth=1.2, label="Promedio 20")
    ax.plot(e50, color="#3498db", linewidth=1.2, label="Promedio 50")
    sup, res = sr_levels(full, kl[-1]["c"])
    for lvl, col, name in ((res, "#e74c3c", "Resistencia"), (sup, "#2ecc71", "Soporte")):
        ax.axhline(lvl, color=col, linestyle=":", linewidth=1.1, alpha=0.9)
        ax.text(0.995, lvl, f"{name} {fp(lvl)}", transform=ax.get_yaxis_transform(), color=col,
                fontsize=8, ha="right", va="bottom")
    ax.legend(facecolor=BG, labelcolor=FG, fontsize=8, loc="upper left")
    ax.set_title(f"{sym[:-4]}/USDT · velas de {interval}", color=FG)
    ar.plot(rs, color="#e67e22", linewidth=1.3)
    ar.axhline(70, color="#e74c3c", linewidth=0.8, linestyle="--")
    ar.axhline(30, color="#2ecc71", linewidth=0.8, linestyle="--")
    ar.set_ylim(0, 100)
    ar.set_ylabel("RSI", color=FG, fontsize=8)
    av.set_ylabel("Volumen", color=FG, fontsize=8)
    for a in (ax, av, ar):
        _style(a)
    _labels(ar, kl, interval)
    return to_png(fig)


def chart_compare(series):
    fig, ax = plt.subplots(figsize=(8, 5))
    fig.patch.set_facecolor(BG)
    for (name, kl), col in zip(series.items(), ["#f1c40f", "#3498db", "#2ecc71", "#e74c3c"]):
        base = kl[0]["c"]
        ax.plot([k["c"] / base * 100 for k in kl], color=col, linewidth=1.8, label=name)
    ax.axhline(100, color="#555", linewidth=0.8, linestyle="--")
    ax.set_title("Comparación (todas empiezan en 100)", color=FG)
    ax.legend(facecolor=BG, labelcolor=FG)
    _style(ax)
    _labels(ax, next(iter(series.values())), "1d")
    return to_png(fig)


def chart_heatmap(rows):
    cols = 6
    nr = math.ceil(len(rows) / cols)
    fig, ax = plt.subplots(figsize=(8, 1.2 * nr + 0.9))
    fig.patch.set_facecolor(BG)
    cmap = plt.get_cmap("RdYlGn")
    for i, x in enumerate(rows):
        r, c = divmod(i, cols)
        val = max(-10, min(10, x["chg"]))
        ax.add_patch(Rectangle((c, -r - 1), 0.96, 0.94, color=cmap((val + 10) / 20)))
        tc = "#ffffff" if abs(val) >= 6 else "#111111"
        ax.text(c + 0.48, -r - 0.36, x["base"], ha="center", va="center", fontsize=11,
                fontweight="bold", color=tc)
        ax.text(c + 0.48, -r - 0.68, f"{x['chg']:+.1f}%", ha="center", va="center", fontsize=9, color=tc)
    ax.set_xlim(0, cols)
    ax.set_ylim(-nr, 0)
    ax.axis("off")
    ax.set_title("Mapa de calor · cambio en 24 h (rojo baja, verde sube)", color=FG, fontsize=11)
    return to_png(fig)


def chart_pie(items):
    items = sorted(items, key=lambda x: x[1], reverse=True)
    if len(items) > 7:
        items = items[:6] + [("Otras", sum(v for _, v in items[6:]))]
    fig, ax = plt.subplots(figsize=(6, 6))
    fig.patch.set_facecolor(BG)
    ax.pie([v for _, v in items], labels=[n for n, _ in items], autopct="%1.0f%%", pctdistance=0.8,
           wedgeprops=dict(width=0.45, edgecolor=BG), textprops={"color": FG})
    ax.set_title("Distribución de tu cartera", color=FG)
    return to_png(fig)


def chart_card(items, total_pnl):
    """Tarjeta para compartir: solo porcentajes, nunca montos. items = [(moneda, % de la cartera, ganancia % o None)]"""
    fig = plt.figure(figsize=(7, 6.2))
    fig.patch.set_facecolor(BG)
    ax = fig.add_axes([0.08, 0.2, 0.84, 0.6])
    ax.pie([a for _, a, _ in items], labels=[f"{b} {a:.0f}%" for b, a, _ in items],
           wedgeprops=dict(width=0.45, edgecolor=BG), textprops={"color": FG, "fontsize": 11})
    fig.text(0.5, 0.945, "Mi cartera cripto", ha="center", color=FG, fontsize=18, fontweight="bold")
    if total_pnl is not None:
        fig.text(0.5, 0.885, f"Resultado total: {total_pnl:+.1f}%", ha="center", fontsize=14,
                 color="#2ecc71" if total_pnl >= 0 else "#e74c3c")
    pnls = [(b, p) for b, _, p in items if p is not None][:8]
    for i, (b, p) in enumerate(pnls):
        fig.text(0.1 + (i % 4) * 0.22, 0.12 - (i // 4) * 0.06, f"{b} {p:+.1f}%", fontsize=11,
                 color="#2ecc71" if p >= 0 else "#e74c3c")
    return to_png(fig)


# ------------------------- comandos: basicos -------------------------
def cmd_start(state, chat, args):
    send(chat, "👋 <b>Hola, soy Cripdex, tu bot de mercado cripto en español.</b>\n\n"
               "Precios, gráficos con soporte y resistencia, análisis fácil, dólar P2P, futuros, escáner, "
               "mapa de calor, noticias, memecoins con filtros anti-estafa, revisión de contratos, tu cartera "
               "y calculadoras. <b>Yo no compro ni vendo por nadie:</b> cada quien decide.\n\n"
               "💡 Atajo: escribe solo <code>btc</code> o <code>sol 1h</code> y te respondo.\n"
               "🔒 Tu cartera y tus alertas se guardan cifradas. Mira /terminos.\n\n" + DISCLAIMER, MENU)


def cmd_ayuda(state, chat, args):
    send(chat, "<b>📈 Mercado</b>\n"
               "/top · /heatmap · /mercado · /noticias · /escaner\n"
               "/precio BTC ETH SOL · o escribe solo <code>btc</code>\n"
               "/memes – memecoins con filtros anti-estafa\n\n"
               "<b>📊 Gráficos y análisis</b>\n"
               "/grafico BTC 1h (15m, 1h, 4h, 1d) · o <code>sol 1h</code>\n"
               "/analisis BTC · /comparar BTC ETH SOL\n"
               "/futuros BTC – funding y open interest\n\n"
               "<b>💵 Dólar y estafas</b>\n"
               "/p2p VES (ARS, COP, EUR, MXN…) · /alertap2p VES 45\n"
               "/contrato DIRECCIÓN – revisión básica de un token\n\n"
               "<b>💼 Lo tuyo</b>\n"
               "/agregar BTC 0.01 65000 · /cartera · /quitar BTC\n"
               "/meta 1000 · /tarjeta (imagen para compartir)\n"
               "/seguir BTC ETH · /lista · /dejar BTC\n"
               "/alerta BTC 70000 o /alerta BTC +5% · /alertas · /borrar 3\n\n"
               "<b>🧰 Aprende y calcula</b>\n"
               "/glosario RSI · /convertir · /ganancia · /riesgo · /dca\n\n"
               "<b>🔔 Avisos y cuenta</b>\n"
               "/suscribir · /config · /umbral 5 · /silenciar\n"
               "/pro · /terminos · /borrar_mis_datos\n"
               "<i>Admin:</i> /estado · /estadisticas · /darpro · /miid\n\n" + DISCLAIMER, MENU)


def cmd_herramientas(state, chat, args):
    send(chat, "🧰 <b>Herramientas</b>\n\n"
               "💱 <b>/convertir 0.5 BTC</b>  o  /convertir 100 USD XRP\n"
               "Convierte entre monedas y dólares.\n\n"
               "💰 <b>/ganancia 100 0.55 0.62</b>\n"
               "Cuánto ganas si inviertes 100 USDT comprando a 0.55 y vendiendo a 0.62 (ya con comisiones).\n\n"
               "🛡 <b>/riesgo 500 2 0.55 0.52</b>\n"
               "Capital 500, arriesgas 2%, entras a 0.55 con stop en 0.52: te dice cuánto comprar.\n\n"
               "📅 <b>/dca BTC 10</b>\n"
               "Simula qué habría pasado comprando 10 USDT de BTC cada semana el último año.\n\n"
               "📖 <b>/glosario</b> explica cada término en palabras simples.\n\n" + DISCLAIMER,
         [[btn("📈 Top del día", "/top"), btn("📖 Glosario", "/glosario")], [btn("🏠 Menú", "/start")]])


def cmd_top(state, chat, args):
    mk = market()
    if not mk:
        return send(chat, "No pude leer el mercado ahora. Intenta en un minuto.")
    mk.sort(key=lambda x: x["chg"], reverse=True)
    lines = ["📈 <b>Más suben (24 h)</b>"]
    for i, x in enumerate(mk[:8], 1):
        lines.append(f"{i}. <b>{x['base']}</b> ${fp(x['price'])} {pc(x['chg'])} · vol {fm(x['qv'])}")
    lines.append("\n📉 <b>Más bajan (24 h)</b>")
    for i, x in enumerate(reversed(mk[-5:]), 1):
        lines.append(f"{i}. <b>{x['base']}</b> ${fp(x['price'])} {pc(x['chg'])} · vol {fm(x['qv'])}")
    lines.append("\nUna moneda que ya subió mucho puede devolverse rápido. " + DISCLAIMER)
    send(chat, "\n".join(lines), [[btn("🗺 Mapa de calor", "/heatmap"), btn("🔍 Escáner", "/escaner")]])


def cmd_heatmap(state, chat, args):
    mk = sorted(market(), key=lambda x: x["qv"], reverse=True)[:30]
    if not mk:
        return send(chat, "No pude leer el mercado ahora.")
    up = sum(1 for x in mk if x["chg"] > 0)
    send_photo(chat, chart_heatmap(mk), f"🗺 Las 30 monedas con más volumen: <b>{up}</b> suben y <b>{len(mk) - up}</b> bajan.",
               [[btn("📈 Top del día", "/top")]])


def cmd_precio(state, chat, args):
    if not args:
        return send(chat, "Escribe la moneda. Ejemplo: /precio BTC  o  /precio BTC ETH SOL")
    if len(args) > 1:
        pr, lines = prices(), []
        for a in args[:10]:
            p = pr.get(norm_base(a))
            lines.append(f"<b>{norm_base(a)}</b> ${fp(p['price'])} {pc(p['chg'])}" if p
                         else f"<b>{norm_base(a)}</b> no encontrada")
        return send(chat, "💰 " + "\n".join(lines))
    t = ticker(norm_sym(args[0]))
    if not t:
        return send(chat, "No encuentro esa moneda en Binance. Prueba con BTC, ETH, SOL, XRP, DOGE…")
    pos = (t["price"] - t["lo"]) / (t["hi"] - t["lo"]) * 100 if t["hi"] > t["lo"] else 50
    send(chat, f"💰 <b>{t['base']}/USDT</b>\nPrecio: <b>${fp(t['price'])}</b>\n24 h: {pc(t['chg'])}\n"
               f"Máximo 24 h: ${fp(t['hi'])}\nMínimo 24 h: ${fp(t['lo'])}\n"
               f"Está al {pos:.0f}% de su rango de hoy (0% = mínimo, 100% = máximo)\n"
               f"Volumen 24 h: ${fm(t['qv'])}",
         [[btn("📊 Gráfico", f"/grafico {t['base']} 1h"), btn("🧠 Análisis", f"/analisis {t['base']}")],
          [btn("➕ Seguir", f"/seguir {t['base']}"), btn("🔔 Alerta +5%", f"/alerta {t['base']} +5%")],
          [btn("📊 Futuros", f"/futuros {t['base']}")]] + binance_buttons(t["base"]))


def chart_pack(sym, iv):
    full = klines(sym, iv, 150)
    if not full:
        return None
    kl = full[-60:]
    return chart_candles(sym, kl, iv, full), kl[-1]["c"], (kl[-1]["c"] / kl[0]["o"] - 1) * 100


def cmd_grafico(state, chat, args):
    if not args:
        return send(chat, "Ejemplo: /grafico BTC 1h  (opciones: 15m, 1h, 4h, 1d)")
    sym = norm_sym(args[0])
    iv = args[1].lower() if len(args) > 1 else "1h"
    if iv not in INTERVALS:
        return send(chat, "Intervalos válidos: 15m, 1h, 4h, 1d")
    pack = cached(f"chart:{sym}:{iv}", 180, lambda: chart_pack(sym, iv))
    if not pack:
        return send(chat, "No encuentro esa moneda en Binance.")
    png, price, chg = pack
    others = [i for i in ("15m", "1h", "4h", "1d") if i != iv][:3]
    send_photo(chat, png, f"<b>{sym[:-4]}</b> ${fp(price)} · en este gráfico {pc(chg)}",
               [[btn(i, f"/grafico {sym[:-4]} {i}") for i in others],
                [btn("🧠 Análisis", f"/analisis {sym[:-4]}")]])


def analysis_pack(sym, iv):
    full = klines(sym, iv, 150)
    if not full or len(full) < 60:
        return None
    closes = [k["c"] for k in full]
    price = closes[-1]
    e20, e50 = ema(closes, 20)[-1], ema(closes, 50)[-1]
    r = rsi(closes)
    mh = macd_hist(closes)
    support, resist = sr_levels(full, price)
    recent = full[-48:]
    vol = sum((k["h"] - k["l"]) / k["c"] for k in recent) / len(recent) * 100
    up, lo = bollinger(closes)
    pb = (price - lo[-1]) / (up[-1] - lo[-1]) * 100 if up[-1] > lo[-1] else 50
    vs = [k["v"] for k in full]
    vratio = (sum(vs[-5:]) / 5) / (sum(vs[-25:-5]) / 20) if sum(vs[-25:-5]) > 0 else 1
    score = (1 if price > e50 else -1) + (1 if e20 > e50 else -1) + (1 if mh > 0 else -1)
    trend = "🟢 alcista" if score >= 2 else "🔴 bajista" if score <= -2 else "🟡 mixta / lateral"
    if r is None:
        rtxt = "sin datos"
    elif r >= 70:
        rtxt = f"{r:.0f} → muy comprada: ya subió mucho y puede corregir"
    elif r <= 30:
        rtxt = f"{r:.0f} → muy vendida: ya cayó mucho, puede rebotar o seguir bajando"
    else:
        rtxt = f"{r:.0f} → normal (sobre 70 = muy comprada, bajo 30 = muy vendida)"
    btxt = ("pegado a la banda alta (estirado hacia arriba)" if pb >= 90 else
            "pegado a la banda baja (estirado hacia abajo)" if pb <= 10 else "dentro de su rango normal")
    voltxt = ("más de lo normal 🔊" if vratio >= 1.5 else "menos de lo normal 🔈" if vratio <= 0.7 else "normal")
    text = (f"🧠 <b>{sym[:-4]}/USDT</b> · velas de {iv}\n"
            f"Precio: <b>${fp(price)}</b>\n"
            f"Tendencia: {trend}\n"
            f"• Precio {'sobre' if price > e50 else 'bajo'} su promedio de 50 velas\n"
            f"• Promedio corto {'sobre' if e20 > e50 else 'bajo'} el largo\n"
            f"• Impulso (MACD): {'positivo' if mh > 0 else 'negativo'}\n"
            f"RSI: {rtxt}\n"
            f"Bandas de Bollinger: {btxt}\n"
            f"Volumen reciente: {voltxt}\n"
            f"Soporte cercano: ${fp(support)} ({max(0.0, (price / support - 1) * 100):.1f}% abajo)\n"
            f"Resistencia cercana: ${fp(resist)} ({max(0.0, (resist / price - 1) * 100):.1f}% arriba)\n"
            f"Movimiento típico por vela: {vol:.2f}%\n\n" + DISCLAIMER)
    return chart_candles(sym, full[-60:], iv, full), text


def cmd_analisis(state, chat, args):
    if not args:
        return send(chat, "Ejemplo: /analisis BTC  (o /analisis ETH 1d)")
    sym = norm_sym(args[0])
    iv = args[1].lower() if len(args) > 1 and args[1].lower() in INTERVALS else "4h"
    pack = cached(f"ana:{sym}:{iv}", 120, lambda: analysis_pack(sym, iv))
    if not pack:
        return send(chat, "No tengo datos suficientes de esa moneda.")
    png, text = pack
    base = sym[:-4]
    send_photo(chat, png, f"🧠 <b>Análisis {base}</b> · velas de {iv}")
    send(chat, text, [[btn("📊 1h", f"/grafico {base} 1h"), btn("📊 1d", f"/grafico {base} 1d"),
                       btn("🔔 Alerta", f"/alerta {base} +5%")],
                      [btn("📊 Futuros", f"/futuros {base}")]] + binance_buttons(base))


def cmd_comparar(state, chat, args):
    syms = [norm_sym(a) for a in args[:4]]
    if len(syms) < 2:
        return send(chat, "Ejemplo: /comparar BTC ETH SOL")
    series, rows = {}, []
    for s in syms:
        kl, t = klines(s, "1d", 30), ticker(s)
        if not kl or not t:
            return send(chat, f"No encuentro {s[:-4]} en Binance.")
        series[s[:-4]] = kl
        c7 = (kl[-1]["c"] / kl[-8]["c"] - 1) * 100 if len(kl) >= 8 else 0
        c30 = (kl[-1]["c"] / kl[0]["c"] - 1) * 100
        rows.append(f"<b>{s[:-4]}</b> ${fp(t['price'])}\n   24 h {pc(t['chg'])} · 7 d {pc(c7)} · 30 d {pc(c30)}")
    best = max(series, key=lambda k: series[k][-1]["c"] / series[k][0]["c"])
    send_photo(chat, chart_compare(series), "⚖️ Rendimiento de los últimos 30 días")
    send(chat, "⚖️ <b>Comparación</b>\n" + "\n".join(rows) +
         f"\n\nMejor en 30 días: <b>{best}</b>. Lo que subió más antes no siempre sigue subiendo.")


def cmd_mercado(state, chat, args):
    send(chat, market_summary() + "\n\n" + DISCLAIMER, [[btn("📈 Top del día", "/top"), btn("🗺 Mapa", "/heatmap")]])


def market_summary():
    lines = ["🌡 <b>Ánimo del mercado</b>"]
    fg = get("https://api.alternative.me/fng/", {"limit": 2})
    names = {"Extreme Fear": "miedo extremo", "Fear": "miedo", "Neutral": "neutral",
             "Greed": "codicia", "Extreme Greed": "codicia extrema"}
    try:
        d = fg["data"]
        lines.append(f"Miedo y codicia: <b>{d[0]['value']}/100</b> ({names.get(d[0]['value_classification'], '')}); "
                     f"ayer {d[1]['value']}. (Bajo 25 = mucho miedo, sobre 75 = mucha euforia)")
    except Exception:
        lines.append("Miedo y codicia: no disponible ahora.")
    g = get("https://api.coingecko.com/api/v3/global")
    try:
        gd = g["data"]
        lines.append(f"Dominio de BTC: {gd['market_cap_percentage']['btc']:.1f}% del mercado total")
        lines.append(f"Mercado total 24 h: {pc(gd['market_cap_change_percentage_24h_usd'])}")
    except Exception:
        pass
    mk = market()
    if mk:
        up = sum(1 for x in mk if x["chg"] > 0)
        lines.append(f"Monedas grandes subiendo hoy: {up} de {len(mk)}")
        for b in ("BTC", "ETH", "SOL"):
            x = next((m for m in mk if m["base"] == b), None)
            if x:
                lines.append(f"{b}: ${fp(x['price'])} {pc(x['chg'])}")
    return "\n".join(lines)


# ------------------------- noticias -------------------------
def news(n=6):
    items = []
    for name, url in FEEDS:
        raw = get_bytes(url)
        if not raw or len(raw) > 2_000_000:
            continue
        try:
            root = ET.fromstring(raw)
        except ET.ParseError:
            continue
        for it in root.iter("item"):
            t = (it.findtext("title") or "").strip()
            link = (it.findtext("link") or "").strip()
            try:
                ts = parsedate_to_datetime(it.findtext("pubDate") or "").timestamp()
            except Exception:
                ts = 0
            if t and link.startswith("http"):
                items.append((ts, name, t, link))
    items.sort(reverse=True)
    seen, out = set(), []
    for ts, name, t, link in items:
        if t.lower() not in seen:
            seen.add(t.lower())
            out.append((ts, name, t, link))
    return out[:n]


def news_lines(items):
    return [f"• <a href=\"{html.escape(link, quote=True)}\">{esc(t)}</a> — {esc(name)}" for _, name, t, link in items]


def cmd_noticias(state, chat, args):
    items = news(6)
    if not items:
        return send(chat, "No pude cargar noticias ahora. Intenta en unos minutos.")
    send(chat, "📰 <b>Últimas noticias cripto</b> (en inglés)\n\n" + "\n".join(news_lines(items)),
         [[btn("🌡 Mercado", "/mercado"), btn("📈 Top", "/top")]])


# ------------------------- escaner -------------------------
def scan_cached():
    c = _cache.get("scan")
    if c and time.time() - c[0] < 300:
        return c[1]
    mk = sorted(market(10e6), key=lambda x: x["qv"], reverse=True)[:40]
    kls = klines_many([x["sym"] for x in mk], "1h", 100)
    out = []
    for x in mk:
        kl = kls.get(x["sym"])
        if not kl or len(kl) < 60:
            continue
        cl = [k["c"] for k in kl]
        e20, e50 = ema(cl, 20), ema(cl, 50)
        cross = None
        for j in (-3, -2, -1):
            prev, cur = e20[j - 1] - e50[j - 1], e20[j] - e50[j]
            if prev <= 0 < cur:
                cross = "up"
            elif prev >= 0 > cur:
                cross = "down"
        vs = [k["v"] for k in kl]
        base_vol = sum(vs[-26:-2]) / 24
        out.append(dict(base=x["base"], price=x["price"], chg=x["chg"], rsi=rsi(cl), cross=cross,
                        ratio=vs[-2] / base_vol if base_vol > 0 else 1))
    _cache["scan"] = (time.time(), out)
    return out


def cmd_escaner(state, chat, args):
    send(chat, "🔍 Escaneando las 40 monedas con más volumen (velas de 1 hora)…")
    res = scan_cached()
    if not res:
        return send(chat, "No pude escanear ahora. Intenta en un minuto.")
    ob = sorted([x for x in res if x["rsi"] and x["rsi"] >= 70], key=lambda x: -x["rsi"])[:5]
    os_ = sorted([x for x in res if x["rsi"] and x["rsi"] <= 30], key=lambda x: x["rsi"])[:5]
    up = [x for x in res if x["cross"] == "up"][:5]
    dn = [x for x in res if x["cross"] == "down"][:5]
    vv = sorted([x for x in res if x["ratio"] >= 3], key=lambda x: -x["ratio"])[:5]

    def fmt(items, f):
        return "\n".join(f(x) for x in items) if items else "Ninguna ahora mismo"
    send(chat, "🔍 <b>Escáner del mercado</b>\n\n"
               "🔥 <b>Sobrecompradas</b> (RSI ≥ 70, subieron mucho, pueden corregir)\n"
               + fmt(ob, lambda x: f"• <b>{x['base']}</b> RSI {x['rsi']:.0f} · {pc(x['chg'])}") +
               "\n\n🧊 <b>Sobrevendidas</b> (RSI ≤ 30, cayeron mucho, pueden rebotar o seguir cayendo)\n"
               + fmt(os_, lambda x: f"• <b>{x['base']}</b> RSI {x['rsi']:.0f} · {pc(x['chg'])}") +
               "\n\n📈 <b>Cruce alcista reciente</b> (el promedio corto pasó sobre el largo)\n"
               + fmt(up, lambda x: f"• <b>{x['base']}</b> ${fp(x['price'])}") +
               "\n\n📉 <b>Cruce bajista reciente</b>\n"
               + fmt(dn, lambda x: f"• <b>{x['base']}</b> ${fp(x['price'])}") +
               "\n\n🔊 <b>Volumen inusual</b> (la última hora movió 3× o más de lo normal)\n"
               + fmt(vv, lambda x: f"• <b>{x['base']}</b> {x['ratio']:.1f}× · {pc(x['chg'])}") +
               "\n\nToca una moneda con /analisis MONEDA. " + DISCLAIMER,
         [[btn("🗺 Mapa de calor", "/heatmap"), btn("🐸 Memecoins", "/memes")]])


# ------------------------- memecoins -------------------------
def meme_flags(p):
    liq = (p.get("liquidity") or {}).get("usd", 0) or 0
    vol = (p.get("volume") or {}).get("h24", 0) or 0
    tx = (p.get("txns") or {}).get("h24") or {}
    buys, sells = tx.get("buys", 0), tx.get("sells", 0)
    created = p.get("pairCreatedAt")
    age_h = (time.time() * 1000 - created) / 3.6e6 if created else None
    ok = (liq >= 30_000 and vol >= 50_000 and buys + sells >= 200 and sells >= 20
          and age_h is not None and age_h >= 6)
    flags = ["💸 Está en 'boosts' de DexScreener: es promoción pagada"]
    if liq < 100_000:
        flags.append("💧 Poca liquidez: difícil vender sin mover el precio")
    if age_h is not None and age_h < 24:
        flags.append("🆕 Menos de 24 h de vida")
    fdv = p.get("fdv") or 0
    if fdv and liq and fdv / liq > 100:
        flags.append("🎈 Valor total muy inflado frente a su liquidez")
    if liq and vol / liq > 20:
        flags.append("🔥 Volumen enorme frente a la liquidez (posible manipulación)")
    if sells and buys / sells > 3:
        flags.append("⚠️ Muchas más compras que ventas (¿trampa?)")
    return ok, flags, age_h


def meme_scan():
    items = []
    for ep in ("/token-boosts/top/v1", "/token-boosts/latest/v1"):
        d = get(DEX + ep)
        if isinstance(d, list):
            items += d
    seen, toks = set(), []
    for it in items:
        key = (it.get("chainId"), it.get("tokenAddress"))
        if key[1] and key not in seen:
            seen.add(key)
            toks.append(key)
    wanted = {a for _, a in toks}
    best = {}
    for i in range(0, len(toks), 30):
        d = get(f"{DEX}/latest/dex/tokens/{','.join(a for _, a in toks[i:i + 30])}")
        for p in (d or {}).get("pairs") or []:
            b = p.get("baseToken") or {}
            if b.get("address") not in wanted:
                continue
            k = (p.get("chainId"), b["address"])
            liq = (p.get("liquidity") or {}).get("usd", 0) or 0
            if k not in best or liq > ((best[k].get("liquidity") or {}).get("usd", 0) or 0):
                best[k] = p
    res = []
    for p in best.values():
        ok, flags, age_h = meme_flags(p)
        if ok:
            res.append((p, flags, age_h))
    res.sort(key=lambda x: (x[0].get("volume") or {}).get("h24", 0), reverse=True)
    return res


def meme_text(p, flags, age_h):
    ch = p.get("priceChange") or {}
    liq = (p.get("liquidity") or {}).get("usd", 0) or 0
    vol = (p.get("volume") or {}).get("h24", 0) or 0
    age = f"{age_h:.0f} h" if age_h < 48 else f"{age_h / 24:.0f} días"
    b = p.get("baseToken") or {}
    return (f"🐸 <b>{esc(b.get('name', '?'))}</b> ({esc(b.get('symbol', '?'))}) · {esc(p.get('chainId', ''))}\n"
            f"💵 ${esc(p.get('priceUsd', '?'))}\n"
            f"1 h {pc(ch.get('h1', 0) or 0)} · 6 h {pc(ch.get('h6', 0) or 0)} · 24 h {pc(ch.get('h24', 0) or 0)}\n"
            f"💧 Liquidez ${fm(liq)} · 📈 Vol 24 h ${fm(vol)} · ⏳ {age}\n" + "\n".join(flags))


def cmd_memes(state, chat, args):
    send(chat, "🔎 Buscando memecoins con actividad real…")
    res = meme_scan()
    if not res:
        return send(chat, "Ninguna memecoin pasó los filtros ahora mismo. Eso es normal: casi todas son riesgo alto.")
    for p, flags, age_h in res[:5]:
        send(chat, meme_text(p, flags, age_h), [[btn("Ver en DexScreener", url=safe_url(p.get("url")))]])
    send(chat, "🛡 Filtros: liquidez ≥ 30K, volumen ≥ 50K, ≥ 200 operaciones, que se pueda vender y ≥ 6 h de vida.\n"
               "Pasar los filtros NO significa que sea segura. Muchas memecoins caen a cero. "
               "Si decides entrar, usa solo dinero que puedas perder.")


# ------------------------- cartera y lista -------------------------
def barra(pct, n=10):
    f = max(0, min(n, int(pct / 100 * n + 0.5)))
    return "█" * f + "░" * (n - f)


def cmd_agregar(state, chat, args):
    if len(args) < 2:
        return send(chat, "Ejemplo: /agregar BTC 0.01 65000\n(moneda, cantidad y, si quieres, el precio al que compraste)")
    base = norm_base(args[0])
    pr = prices()
    if base not in pr:
        return send(chat, "No encuentro esa moneda en Binance.")
    try:
        qty = num(args[1])
        cost = num(args[2]) if len(args) > 2 else 0.0
    except ValueError:
        return send(chat, "La cantidad y el precio deben ser números. Ejemplo: /agregar BTC 0.01 65000")
    if qty <= 0 or cost < 0:
        return send(chat, "La cantidad debe ser mayor que 0.")
    port = state["port"].setdefault(str(chat), {})
    if base not in port and len(port) >= plan_limit(state, chat, "port"):
        return send(chat, limit_msg(state, chat, "port") + " Quita alguna con /quitar.")
    h = port.get(base)
    if h:
        if cost and h.get("cost"):
            h["cost"] = (h["qty"] * h["cost"] + qty * cost) / (h["qty"] + qty)
        elif cost:
            h["cost"] = cost
        h["qty"] += qty
    else:
        port[base] = {"qty": qty, "cost": cost}
    send(chat, f"✅ Agregado: {fq(qty)} {base}. Mira cómo vas con /cartera",
         [[btn("💼 Ver cartera", "/cartera")]])


def cmd_quitar(state, chat, args):
    if not args:
        return send(chat, "Ejemplo: /quitar BTC  (o /quitar BTC 0.005 para quitar solo una parte)")
    base, port = norm_base(args[0]), state["port"].get(str(chat), {})
    if base not in port:
        return send(chat, "Esa moneda no está en tu cartera.")
    if len(args) > 1:
        try:
            port[base]["qty"] -= num(args[1])
        except ValueError:
            return send(chat, "La cantidad debe ser un número.")
        if port[base]["qty"] <= 1e-12:
            del port[base]
    else:
        del port[base]
    send(chat, "✅ Actualizado. Mira /cartera")


def cmd_cartera(state, chat, args):
    hold = state["port"].get(str(chat)) or {}
    if not hold:
        return send(chat, "💼 Tu cartera está vacía. Agrega monedas así:\n/agregar BTC 0.01 65000\n"
                          "(moneda, cantidad y, si quieres, el precio al que compraste)")
    pr = prices()
    rows, total, cost_total, val_with_cost, day = [], 0.0, 0.0, 0.0, 0.0
    for base, h in hold.items():
        p = pr.get(base)
        if not p:
            continue
        val = h["qty"] * p["price"]
        total += val
        if p["chg"] > -99.9:
            day += val - val / (1 + p["chg"] / 100)
        pnl = None
        if h.get("cost"):
            cost_total += h["qty"] * h["cost"]
            val_with_cost += val
            pnl = (p["price"] / h["cost"] - 1) * 100
        rows.append((val, base, h, p, pnl))
    rows.sort(key=lambda r: -r[0])
    lines = ["💼 <b>Tu cartera</b>"]
    for val, base, h, p, pnl in rows:
        s = f"<b>{base}</b> {fq(h['qty'])} × ${fp(p['price'])} = <b>${val:,.2f}</b>"
        if pnl is not None:
            s += f"\n   compra ${fp(h['cost'])} → {pc(pnl)}"
        lines.append(s)
    lines.append(f"\n<b>Total: ${total:,.2f}</b>")
    lines.append(f"Hoy: {'🟢' if day >= 0 else '🔴'} {day:+,.2f} USDT")
    goal = state["goals"].get(str(chat))
    if goal:
        pct = total / goal * 100
        lines.append(f"🎯 Meta ${goal:,.0f}: {barra(pct)} {min(pct, 999):.0f}%")
    if cost_total:
        g = val_with_cost - cost_total
        lines.append(f"Ganancia vs lo que pagaste: {'🟢' if g >= 0 else '🔴'} {g:+,.2f} USDT ({g / cost_total * 100:+.1f}%)")
        if g >= 0:
            lines.append("✅ Vas en positivo. Recuerda: una ganancia en papel solo es real cuando vendes.")
    lines.append("\n" + DISCLAIMER)
    if len(rows) >= 2:
        send_photo(chat, chart_pie([(b, v) for v, b, *_ in rows]), "")
    send(chat, "\n".join(lines), [[btn("➕ Más monedas", "/ayuda"), btn("📈 Top", "/top")]])


def cmd_seguir(state, chat, args):
    if not args:
        return send(chat, "Ejemplo: /seguir BTC ETH SOL")
    w = state["watch"].setdefault(str(chat), [])
    pr, added = prices(), []
    for a in args[:10]:
        b = norm_base(a)
        if b in pr and b not in w and len(w) < plan_limit(state, chat, "watch"):
            w.append(b)
            added.append(b)
    send(chat, f"✅ Siguiendo: {', '.join(added)}. Mira /lista" if added
         else "No agregué nada (no existe, ya estaba o llegaste al límite: " + limit_msg(state, chat, "watch") + ")")


def cmd_dejar(state, chat, args):
    w = state["watch"].setdefault(str(chat), [])
    for a in args:
        if norm_base(a) in w:
            w.remove(norm_base(a))
    send(chat, "✅ Listo. Mira /lista")


def cmd_lista(state, chat, args):
    w = state["watch"].get(str(chat)) or []
    if not w:
        return send(chat, "Tu lista está vacía. Agrega monedas: /seguir BTC ETH SOL")
    pr, lines = prices(), []
    for b in w:
        p = pr.get(b)
        lines.append(f"<b>{b}</b> ${fp(p['price'])} {pc(p['chg'])}" if p else f"<b>{b}</b> sin datos")
    send(chat, "⭐ <b>Tu lista</b>\n" + "\n".join(lines), [[btn("🗺 Mapa de calor", "/heatmap")]])


# ------------------------- herramientas -------------------------
def price_of(name, pr):
    n = name.upper()
    if n in USD_NAMES:
        return 1.0
    p = pr.get(norm_base(n))
    return p["price"] if p else None


def cmd_convertir(state, chat, args):
    if len(args) < 2:
        return send(chat, "Ejemplos:\n/convertir 0.5 BTC  (a dólares)\n/convertir 100 USD XRP\n/convertir 2 ETH BTC")
    try:
        amt = num(args[0])
    except ValueError:
        return send(chat, "La cantidad debe ser un número. Ejemplo: /convertir 0.5 BTC")
    pr = prices()
    a, b = args[1], (args[2] if len(args) > 2 else "USD")
    pa, pb = price_of(a, pr), price_of(b, pr)
    if pa is None or pb is None:
        return send(chat, "No encuentro alguna de las monedas.")
    usd = amt * pa
    res = usd / pb
    shown = f"{res:,.2f}" if res >= 1000 else fp(res)
    send(chat, f"💱 {fq(amt)} <b>{esc(a.upper())}</b> = <b>{shown} {esc(b.upper())}</b>\n"
               f"(≈ ${usd:,.2f}). Precio de referencia de Binance; al operar hay comisiones.")


def cmd_ganancia(state, chat, args):
    if len(args) < 3:
        return send(chat, "Ejemplo: /ganancia 100 0.55 0.62\n(inversión en USDT, precio de compra, precio de venta)")
    try:
        inv, buy, sell = num(args[0]), num(args[1]), num(args[2])
        assert inv > 0 and buy > 0 and sell > 0
    except Exception:
        return send(chat, "Usa números mayores que 0. Ejemplo: /ganancia 100 0.55 0.62")
    units = inv / buy * (1 - FEE)
    got = units * sell * (1 - FEE)
    profit = got - inv
    be = buy * (1 + FEE) / (1 - FEE)
    send(chat, f"💰 <b>Simulación</b>\nCompras con ${inv:,.2f} a ${fp(buy)} → {fq(units)} monedas\n"
               f"Vendes a ${fp(sell)} → recibes ${got:,.2f}\n"
               f"Resultado: {'🟢' if profit >= 0 else '🔴'} <b>{profit:+,.2f} USDT ({profit / inv * 100:+.2f}%)</b>\n"
               f"Comisiones incluidas (0,1% por operación). Para no perder, el precio debe pasar de ${fp(be)}.\n\n"
               + DISCLAIMER)


def cmd_riesgo(state, chat, args):
    if len(args) < 4:
        return send(chat, "Ejemplo: /riesgo 500 2 0.55 0.52\n(capital, % que aceptas perder, precio de entrada, precio de stop)")
    try:
        cap, rp, entry, stop = (num(a) for a in args[:4])
        assert cap > 0 and 0 < rp <= 100 and entry > 0 and stop > 0 and entry != stop
    except Exception:
        return send(chat, "Revisa los números. Ejemplo: /riesgo 500 2 0.55 0.52")
    risk = cap * rp / 100
    dist = abs(entry - stop)
    units = risk / dist
    pos = units * entry
    long_ = stop < entry
    t2, t3 = entry + (2 if long_ else -2) * dist, entry + (3 if long_ else -3) * dist
    extra = (f"\n⚠️ Esa posición (${pos:,.2f}) es mayor que tu capital: baja el riesgo o acerca el stop."
             if pos > cap else "")
    send(chat, f"🛡 <b>Tamaño de la posición</b> ({'compra' if long_ else 'venta en corto'})\n"
               f"Arriesgas ${risk:,.2f} ({rp:g}% de ${cap:,.2f}). Si el precio toca el stop (${fp(stop)}), pierdes eso.\n"
               f"Cantidad: <b>{fq(units)}</b> monedas ≈ <b>${pos:,.2f}</b>\n"
               f"Metas de referencia: 2× el riesgo en ${fp(t2)} · 3× en ${fp(t3)}{extra}\n\n" + DISCLAIMER)


def cmd_dca(state, chat, args):
    if len(args) < 2:
        return send(chat, "Ejemplo: /dca BTC 10  (compras 10 USDT cada semana durante el último año)")
    try:
        amt = num(args[1])
        assert amt > 0
    except Exception:
        return send(chat, "El monto debe ser un número mayor que 0. Ejemplo: /dca BTC 10")
    sym = norm_sym(args[0])
    kl = klines(sym, "1w", 52)
    if not kl:
        return send(chat, "No encuentro esa moneda en Binance.")
    units = sum(amt / k["o"] for k in kl)
    invested = amt * len(kl)
    last = kl[-1]["c"]
    value = units * last
    lump = invested / kl[0]["o"] * last
    avg = invested / units
    send(chat, f"📅 <b>Simulación DCA de {sym[:-4]}</b>\n"
               f"Comprando ${amt:,.2f} cada semana durante {len(kl)} semanas:\n"
               f"Invertido: ${invested:,.2f}\nHoy valdría: <b>${value:,.2f}</b> ({(value / invested - 1) * 100:+.1f}%)\n"
               f"Precio promedio de compra: ${fp(avg)} (hoy ${fp(last)})\n"
               f"Si hubieras puesto todo al inicio: ${lump:,.2f} ({(lump / invested - 1) * 100:+.1f}%)\n\n"
               "Es el pasado: no promete nada del futuro. Comprar poco y seguido reduce el riesgo de entrar justo en un pico.\n\n"
               + DISCLAIMER)


# ------------------------- alertas y avisos -------------------------
def alert_label(a):
    return f"USDT en {a['sym'][4:]} (P2P)" if a["sym"].startswith("P2P:") else a["sym"][:-4]


def alert_price(a, x):
    return f"{x:,.2f}" if a["sym"].startswith("P2P:") else fp(x)


def cmd_alerta(state, chat, args):
    if len(args) < 2:
        return send(chat, "Ejemplos:\n/alerta BTC 70000  (cuando llegue a ese precio)\n"
                          "/alerta BTC +5%  (cuando suba 5% desde ahora)\n/alerta ETH -8%")
    sym = norm_sym(args[0])
    t = ticker(sym)
    if not t:
        return send(chat, "No encuentro esa moneda en Binance.")
    try:
        a = args[1]
        target = t["price"] * (1 + num(a[:-1]) / 100) if a.endswith("%") else num(a)
        assert target > 0
    except Exception:
        return send(chat, "El precio debe ser un número. Ejemplo: /alerta BTC 70000 o /alerta BTC +5%")
    if sum(1 for x in state["alerts"] if x["chat"] == chat) >= plan_limit(state, chat, "alerts"):
        return send(chat, limit_msg(state, chat, "alerts") + " Borra alguna con /borrar número.")
    d = "up" if target > t["price"] else "down"
    state["alerts"].append({"id": state["next_id"], "chat": chat, "sym": sym, "price": target, "dir": d})
    send(chat, f"🔔 Alerta #{state['next_id']} lista: te aviso cuando {t['base']} "
               f"{'suba hasta' if d == 'up' else 'baje hasta'} ${fp(target)} (ahora ${fp(t['price'])}).")
    state["next_id"] += 1


def cmd_alertap2p(state, chat, args):
    if len(args) < 2:
        return send(chat, "Ejemplos:\n/alertap2p VES 45.5  (cuando el USDT llegue a ese precio)\n"
                          "/alertap2p VES +3%  (cuando suba 3% desde ahora)\n/alertap2p ARS -2%")
    fiat = args[0].upper()
    if fiat not in P2P_FIATS:
        return send(chat, "Moneda no disponible. Opciones: " + ", ".join(P2P_FIATS))
    mid = p2p_mid(fiat)
    if not mid:
        return send(chat, "No pude leer el dólar P2P ahora. Intenta en un minuto.")
    try:
        a = args[1]
        target = mid * (1 + num(a[:-1]) / 100) if a.endswith("%") else num(a)
        assert target > 0
    except Exception:
        return send(chat, "El precio debe ser un número. Ejemplo: /alertap2p VES 45.5 o /alertap2p VES +3%")
    if sum(1 for x in state["alerts"] if x["chat"] == chat) >= plan_limit(state, chat, "alerts"):
        return send(chat, limit_msg(state, chat, "alerts") + " Borra alguna con /borrar número.")
    d = "up" if target > mid else "down"
    state["alerts"].append({"id": state["next_id"], "chat": chat, "sym": f"P2P:{fiat}", "price": target, "dir": d})
    send(chat, f"🔔 Alerta #{state['next_id']} lista: te aviso cuando el USDT en {fiat} "
               f"{'suba hasta' if d == 'up' else 'baje hasta'} {target:,.2f} (ahora {mid:,.2f}).")
    state["next_id"] += 1


def cmd_alertas(state, chat, args):
    mine = [a for a in state["alerts"] if a["chat"] == chat]
    if not mine:
        return send(chat, "No tienes alertas. Crea una: /alerta BTC 70000 o /alertap2p VES +3%")
    send(chat, "🔔 <b>Tus alertas</b>\n" + "\n".join(
        f"#{a['id']} {alert_label(a)} {'≥' if a['dir'] == 'up' else '≤'} {alert_price(a, a['price'])}" for a in mine)
         + f"\nBorrar: /borrar número · Usas {len(mine)} de {plan_limit(state, chat, 'alerts')}")


def cmd_borrar(state, chat, args):
    try:
        n = int(args[0])
    except (IndexError, ValueError):
        return send(chat, "Ejemplo: /borrar 3")
    before = len(state["alerts"])
    state["alerts"] = [a for a in state["alerts"] if not (a["id"] == n and a["chat"] == chat)]
    send(chat, "✅ Alerta borrada." if len(state["alerts"]) < before else "No encontré esa alerta.")


def cmd_suscribir(state, chat, args):
    if chat not in state["subs"]:
        state["subs"].append(chat)
    pref(state, chat)
    send(chat, "✅ <b>Avisos activados.</b> Recibirás:\n"
               "⚡ movimientos fuertes de monedas grandes\n🔊 volumen inusual\n🐸 memecoins que pasen los filtros\n"
               "🌅 resumen diario a las 8:00 a. m. (hora de Venezuela)\n\n"
               "Elige cuáles quieres con /config. Para apagar todo: /silenciar",
         [[btn("⚙️ Configurar", "/config")]])


def cmd_silenciar(state, chat, args):
    if chat in state["subs"]:
        state["subs"].remove(chat)
    send(chat, "🔕 Avisos apagados. Puedes volver a activarlos con /suscribir")


def config_view(state, chat):
    p = pref(state, chat)
    on = chat in state["subs"]

    def mark(k):
        return "✅" if p[k] else "❌"
    text = ("⚙️ <b>Tus avisos</b>" + ("" if on else " (apagados: toca un botón para activarlos)") + "\n"
            f"{mark('mov_on')} Movimientos fuertes (desde ±{p['mov']:g}% en ~1 h)\n"
            f"{mark('vol')} Volumen inusual\n{mark('memes')} Memecoins\n{mark('daily')} Resumen diario 8:00 a. m.\n\n"
            "Cambia el umbral con /umbral 8 (entre 3 y 20).")
    kb = [[btn(f"{mark('mov_on')} Movimientos", "/toggle mov_on"), btn(f"{mark('vol')} Volumen", "/toggle vol")],
          [btn(f"{mark('memes')} Memecoins", "/toggle memes"), btn(f"{mark('daily')} Resumen", "/toggle daily")],
          [btn("🔕 Apagar todo", "/silenciar")]]
    return text, kb


def cmd_config(state, chat, args):
    text, kb = config_view(state, chat)
    send(chat, text, kb)


def cmd_toggle(state, chat, args):
    if not args or args[0] not in ("mov_on", "vol", "memes", "daily"):
        return
    if chat not in state["subs"]:
        state["subs"].append(chat)
    p = pref(state, chat)
    p[args[0]] = not p[args[0]]
    cmd_config(state, chat, [])


def cmd_umbral(state, chat, args):
    try:
        v = num(args[0])
        assert 3 <= v <= 20
    except Exception:
        return send(chat, "Ejemplo: /umbral 8  (un número entre 3 y 20: avisa cuando una moneda se mueva ese % en ~1 hora)")
    pref(state, chat)["mov"] = v
    if chat not in state["subs"]:
        state["subs"].append(chat)
    send(chat, f"✅ Te avisaré de movimientos desde ±{v:g}% en ~1 hora.")


# ------------------------- plan Pro y límites -------------------------
def is_pro(state, chat):
    return chat == OWNER_ID or state["pro"].get(str(chat), 0) > time.time()


def plan_limit(state, chat, what):
    return LIMITS["pro" if is_pro(state, chat) else "free"][what]


def limit_msg(state, chat, what):
    n = plan_limit(state, chat, what)
    if is_pro(state, chat):
        return f"Llegaste al límite de tu plan Pro ({n})."
    return f"Llegaste al límite del plan gratis ({n}). El plan Pro lo sube a {LIMITS['pro'][what]}: mira /pro."


def cmd_pro(state, chat, args):
    exp = state["pro"].get(str(chat), 0)
    if chat == OWNER_ID:
        status = "👑 Eres el administrador: todo desbloqueado."
    elif exp > time.time():
        status = "✅ <b>Plan Pro activo</b> hasta " + datetime.fromtimestamp(exp, TZ).strftime("%d/%m/%Y")
    else:
        status = "Tu plan: <b>Gratis</b>"
    f, p_ = LIMITS["free"], LIMITS["pro"]
    send(chat, f"⭐ <b>Cripdex Pro</b>\n{status}\n\n"
               f"<b>Gratis:</b> {f['alerts']} alertas · {f['watch']} monedas en tu lista · {f['port']} en tu cartera\n"
               f"<b>Pro:</b> {p_['alerts']} alertas · {p_['watch']} en tu lista · {p_['port']} en tu cartera\n\n"
               "Todo lo demás (precios, gráficos, análisis, escáner, P2P, futuros, memecoins, avisos) es gratis.\n"
               "El pago automático todavía no está activo. Si quieres Pro, escríbele al administrador de este bot.")


def cmd_darpro(state, chat, args):
    if not OWNER_ID or chat != OWNER_ID:
        return send(chat, "Este comando es solo para el administrador.")
    try:
        uid, days = int(args[0]), int(args[1])
        assert 0 <= days <= 3650
    except Exception:
        return send(chat, "Uso: /darpro ID DÍAS  (DÍAS = 0 quita el plan Pro). El ID lo ve la persona con /miid.")
    k = str(uid)
    if days == 0:
        state["pro"].pop(k, None)
        return send(chat, f"✅ Pro quitado a {uid}.")
    state["pro"][k] = max(time.time(), state["pro"].get(k, 0)) + days * 86400
    until = datetime.fromtimestamp(state["pro"][k], TZ).strftime("%d/%m/%Y")
    send(chat, f"✅ Pro para {uid} hasta {until}.")
    send(uid, f"⭐ Tu plan <b>Pro</b> está activo hasta {until}. ¡Gracias por apoyar a Cripdex!")


def cmd_terminos(state, chat, args):
    send(chat, "📜 <b>Términos y privacidad</b>\n\n"
               "• Cripdex <b>solo informa</b>. No es asesoría financiera ni garantiza ganancias. Invierte solo lo que puedas perder.\n"
               "• Los datos vienen de terceros (Binance, DexScreener, GoPlus, RugCheck, DolarAPI, OKX y otros) y pueden tardar, fallar o ser inexactos.\n"
               "• Guardo, cifrados: tu ID de chat, tus avisos, tu cartera, tu lista, tus alertas, tu meta y la fecha de tu última visita.\n"
               "• No guardo contraseñas ni claves de ningún exchange. Nunca las compartas con nadie.\n"
               "• Algunos enlaces pueden ser de referido: el botón lo dice, y a ti no te cuesta más.\n"
               "• Puedes borrar todo cuando quieras con /borrar_mis_datos.")


def cmd_borrar_mis_datos(state, chat, args):
    if not args or args[0].lower() != "si":
        return send(chat, "⚠️ Esto borra <b>todo</b> lo tuyo: cartera, lista, alertas, meta, avisos y plan Pro. No se puede deshacer.",
                    [[btn("🗑 Sí, borrar todo", "/borrar_mis_datos si"), btn("Cancelar", "/start")]])
    k = str(chat)
    for key in ("prefs", "port", "watch", "goals", "pro"):
        state[key].pop(k, None)
    state["stats"]["seen"].pop(k, None)
    if chat in state["subs"]:
        state["subs"].remove(chat)
    state["alerts"] = [a for a in state["alerts"] if a["chat"] != chat]
    send(chat, "✅ Listo, borré todos tus datos. Puedes volver cuando quieras con /start.")


def cmd_estadisticas(state, chat, args):
    if not OWNER_ID or chat != OWNER_ID:
        return send(chat, "Este comando es solo para el administrador.")
    st, now = state["stats"], time.time()
    seen = list(st["seen"].values())
    top = sorted(st["cmds"].items(), key=lambda kv: -kv[1])[:8]
    send(chat, "📊 <b>Estadísticas</b>\n"
               f"Personas que han escrito: {len(seen)}\n"
               f"Activas en 24 h: {sum(1 for t in seen if now - t < 86400)} · en 7 días: {sum(1 for t in seen if now - t < 604800)}\n"
               f"Suscritas a avisos: {len(state['subs'])}\n"
               f"Con cartera: {len(state['port'])} · Con alertas: {len({a['chat'] for a in state['alerts']})}\n"
               f"Con plan Pro: {sum(1 for t in state['pro'].values() if t > now)}\n\n"
               "<b>Comandos más usados</b>\n" + ("\n".join(f"{c} · {n}" for c, n in top) or "aún nada"))


# ------------------------- dólar P2P -------------------------
def p2p_side(fiat, side):
    """Mejores anuncios de USDT en Binance P2P. side: BUY (tú compras USDT) o SELL (tú vendes USDT)."""
    key = f"p2p:{fiat}:{side}"
    c = _cache.get(key)
    if c and time.time() - c[0] < 120:
        return c[1]
    body = {"fiat": fiat, "page": 1, "rows": 10, "tradeType": side, "asset": "USDT", "countries": [],
            "proMerchantAds": False, "shieldMerchantAds": False, "publisherType": None, "payTypes": []}
    rows = []
    try:
        r = SESSION.post(P2P_URL, json=body, timeout=15, headers=UA)
        if r.status_code == 200:
            rows = r.json().get("data") or []
        else:
            print("P2P respondió", r.status_code)
    except Exception as e:
        print("P2P error:", safe(e))
    vals = []
    for it in rows:
        try:
            vals.append(float(it["adv"]["price"]))
        except (KeyError, TypeError, ValueError):
            pass
    if not vals:
        return None
    top = vals[:5]
    out = {"avg": sum(top) / len(top), "best": vals[0], "n": len(vals)}
    _cache[key] = (time.time(), out)
    return out


def p2p_mid(fiat):
    buy, sell = p2p_side(fiat, "BUY"), p2p_side(fiat, "SELL")
    if buy and sell:
        return (buy["avg"] + sell["avg"]) / 2
    return (buy or sell or {}).get("avg")


def official_rate(fiat):
    """Referencia oficial (solo VES y ARS) con DolarAPI: (oficial, paralelo o blue)."""
    ofi = par = None
    if fiat == "VES":
        for x in get("https://ve.dolarapi.com/v1/dolares", tries=1) or []:
            if x.get("fuente") == "oficial":
                ofi = x.get("promedio") or x.get("venta")
            elif x.get("fuente") == "paralelo":
                par = x.get("promedio") or x.get("venta")
    elif fiat == "ARS":
        for x in get("https://dolarapi.com/v1/dolares", tries=1) or []:
            if x.get("casa") == "oficial":
                ofi = x.get("venta")
            elif x.get("casa") == "blue":
                par = x.get("venta")
    return (ofi, par) if (ofi or par) else None


def p2p_line(fiat):
    buy, sell = p2p_side(fiat, "BUY"), p2p_side(fiat, "SELL")
    if not (buy and sell):
        return ""
    sym = FIAT_SYMBOL.get(fiat, fiat)
    return f"💵 USDT en {fiat} (P2P): compra {sym} {buy['avg']:,.2f} · venta {sym} {sell['avg']:,.2f}"


def cmd_p2p(state, chat, args):
    fiat = args[0].upper() if args else ""
    if fiat not in P2P_FIATS:
        return send(chat, "💵 <b>Dólar (USDT) en Binance P2P</b>\nElige tu moneda o escribe por ejemplo <code>/p2p VES</code>.",
                    [[btn(f, f"/p2p {f}") for f in ("VES", "ARS", "COP")],
                     [btn(f, f"/p2p {f}") for f in ("EUR", "MXN", "BRL")],
                     [btn(f, f"/p2p {f}") for f in ("PEN", "CLP", "USD")]])
    buy, sell = p2p_side(fiat, "BUY"), p2p_side(fiat, "SELL")
    off = cached(f"off:{fiat}", 300, lambda: official_rate(fiat))
    ofi, par = off if off else (None, None)
    sym = FIAT_SYMBOL.get(fiat, fiat)
    lines = [f"💵 <b>USDT en Binance P2P · {fiat}</b>"]
    if buy:
        lines.append(f"🟢 Comprar USDT (tú pagas): <b>{sym} {buy['avg']:,.2f}</b>\n   promedio de los 5 mejores anuncios · el mejor {buy['best']:,.2f}")
    if sell:
        lines.append(f"🔴 Vender USDT (tú recibes): <b>{sym} {sell['avg']:,.2f}</b>\n   promedio de los 5 mejores anuncios · el mejor {sell['best']:,.2f}")
    if buy and sell:
        lines.append(f"↔️ Diferencia entre comprar y vender: {(buy['avg'] / sell['avg'] - 1) * 100:.1f}%")
    mid = p2p_mid(fiat)
    if ofi:
        lines.append(f"🏛 Dólar oficial (referencia): {sym} {ofi:,.2f}")
        if mid:
            lines.append(f"📐 Brecha del USDT P2P frente al oficial: {(mid / ofi - 1) * 100:+.1f}%")
    if par:
        lines.append(f"🌆 {'Blue' if fiat == 'ARS' else 'Paralelo'} (DolarAPI): {sym} {par:,.2f}")
    if not (buy or sell or ofi):
        return send(chat, "No pude consultar el dólar P2P ahora (la fuente no respondió). Intenta en unos minutos.")
    lines.append("\n⚠️ Son referencias que cambian rápido. En P2P <b>nunca liberes los USDT hasta ver el dinero en tu cuenta</b>. " + DISCLAIMER)
    send(chat, "\n".join(lines),
         [[btn(f, f"/p2p {f}") for f in P2P_FIATS if f != fiat][:4],
          [btn("🔔 Avisarme si cambia", f"/alertap2p {fiat} +3%"),
           btn("Abrir P2P", url=f"https://p2p.binance.com/es/trade/all-payments/USDT?fiat={fiat}")]])


# ------------------------- futuros -------------------------
def futures_data(base):
    """Funding rate y open interest. Prueba Binance, luego OKX y luego Bybit (algunos bloquean servidores de EE. UU.)."""
    sym = base + "USDT"
    d = get("https://fapi.binance.com/fapi/v1/premiumIndex", {"symbol": sym}, tries=1)
    if isinstance(d, dict) and d.get("lastFundingRate") is not None:
        o = get("https://fapi.binance.com/fapi/v1/openInterest", {"symbol": sym}, tries=1)
        try:
            mark = float(d.get("markPrice") or 0)
            oi_usd = float(o["openInterest"]) * mark if mark else None
        except (KeyError, TypeError, ValueError):
            oi_usd = None
        return {"source": "Binance", "funding": float(d["lastFundingRate"]), "oi_usd": oi_usd,
                "next_ms": int(d.get("nextFundingTime") or 0)}
    inst = f"{base}-USDT-SWAP"
    f = get("https://www.okx.com/api/v5/public/funding-rate", {"instId": inst}, tries=1)
    try:
        row = f["data"][0]
        funding, nxt = float(row["fundingRate"]), int(row.get("nextFundingTime") or 0)
    except (KeyError, IndexError, TypeError, ValueError):
        row = None
    if row:
        o = get("https://www.okx.com/api/v5/public/open-interest", {"instType": "SWAP", "instId": inst}, tries=1)
        oi_usd = None
        try:
            od = o["data"][0]
            oi_usd = float(od.get("oiUsd") or 0) or (float(od["oiCcy"]) * prices()[base]["price"])
        except (KeyError, IndexError, TypeError, ValueError):
            pass
        return {"source": "OKX", "funding": funding, "oi_usd": oi_usd, "next_ms": nxt}
    b = get("https://api.bybit.com/v5/market/tickers", {"category": "linear", "symbol": sym}, tries=1)
    try:
        row = b["result"]["list"][0]
        return {"source": "Bybit", "funding": float(row["fundingRate"]),
                "oi_usd": float(row.get("openInterestValue") or 0) or None,
                "next_ms": int(row.get("nextFundingTime") or 0)}
    except (KeyError, IndexError, TypeError, ValueError):
        return None


def cmd_futuros(state, chat, args):
    base = norm_base(args[0]) if args else "BTC"
    d = cached(f"fut:{base}", 120, lambda: futures_data(base))
    if not d:
        return send(chat, f"No pude leer los futuros de {esc(base)} ahora. Puede que no tenga futuros o que la fuente no responda.")
    f = d["funding"]
    if f >= 0.0005:
        mood = "🔥 <b>Muy positiva</b>: demasiada gente apostando a que sube, y con deuda. Si el precio se frena, esas apuestas se cierran a la fuerza y puede haber una caída brusca."
    elif f >= 0.00025:
        mood = "🟠 <b>Elevada</b>: hay más apuestas a subir que a bajar. El mercado está optimista; ojo con los excesos."
    elif f >= -0.00005:
        mood = "⚪ <b>Normal</b> (cerca de 0,01%): el mercado está equilibrado."
    elif f >= -0.0003:
        mood = "🔵 <b>Ligeramente negativa</b>: hay algo más de apuestas a la baja. Suele indicar cautela."
    else:
        mood = "🧊 <b>Muy negativa</b>: mucha gente apuesta a que baja. Puede seguir cayendo, o rebotar fuerte si esas apuestas se cierran."
    lines = [f"📊 <b>Futuros de {esc(base)}</b> (fuente: {d['source']})",
             f"Tasa de financiación: <b>{f * 100:+.4f}%</b> cada 8 h (≈ {f * 3 * 365 * 100:+.0f}% al año)", mood]
    if d.get("oi_usd"):
        lines.append(f"\nInterés abierto: <b>${fm(d['oi_usd'])}</b> en apuestas abiertas. Más interés abierto = más apalancamiento "
                     "en el mercado = movimientos más bruscos.")
    if d.get("next_ms"):
        lines.append("Próximo cobro de la tasa: " + datetime.fromtimestamp(d["next_ms"] / 1000, TZ).strftime("%H:%M") + f" (UTC{TZ_H:+g})")
    lines.append("\n📖 La tasa la pagan los que apuestan a subir a los que apuestan a bajar (o al revés). "
                 "No es una señal de compra ni de venta. " + DISCLAIMER)
    send(chat, "\n".join(lines),
         [[btn("📊 Gráfico", f"/grafico {base} 1h"), btn("🧠 Análisis", f"/analisis {base}")],
          [btn(c, f"/futuros {c}") for c in ("BTC", "ETH", "SOL") if c != base]])


# ------------------------- revisión de contratos -------------------------
EVM_RE = re.compile(r"^0x[a-fA-F0-9]{40}$")
SOL_RE = re.compile(r"^[1-9A-HJ-NP-Za-km-z]{32,44}$")
GOPLUS_CHAIN = {"ethereum": "1", "bsc": "56", "base": "8453", "arbitrum": "42161", "polygon": "137",
                "optimism": "10", "avalanche": "43114"}
RUG_ES = {"Mint Authority still enabled": "El creador todavía puede crear más monedas (inflar la oferta)",
          "Freeze Authority still enabled": "El creador puede congelar tus monedas",
          "Low Liquidity": "Liquidez baja", "Low amount of LP Providers": "Muy pocos aportan liquidez",
          "Large Amount of LP Unlocked": "Gran parte de la liquidez no está bloqueada (se puede retirar)",
          "Top 10 holders high ownership": "Los 10 mayores dueños concentran muchas monedas",
          "Single holder ownership": "Una sola cartera tiene una parte enorme",
          "High ownership": "Pocos dueños concentran la oferta", "Mutable metadata": "Los datos del token pueden cambiarse",
          "Copycat token": "Parece una copia de otro token", "No social media": "Sin redes sociales"}


def _f(x, default=0.0):
    try:
        return float(x)
    except (TypeError, ValueError):
        return default


def dex_risk_flags(p):
    liq = (p.get("liquidity") or {}).get("usd", 0) or 0
    vol = (p.get("volume") or {}).get("h24", 0) or 0
    tx = (p.get("txns") or {}).get("h24") or {}
    buys, sells = tx.get("buys", 0), tx.get("sells", 0)
    created = p.get("pairCreatedAt")
    age_h = (time.time() * 1000 - created) / 3.6e6 if created else None
    fl = []
    if liq < 10_000:
        fl.append(("danger", f"Riesgo alto: liquidez de solo ${fm(liq)} (menos de $10K). Vender puede ser imposible o muy caro"))
    elif liq < 30_000:
        fl.append(("warn", f"Poca liquidez (${fm(liq)})"))
    if age_h is not None:
        if age_h < 6:
            fl.append(("danger", "Muy nueva: menos de 6 horas de vida"))
        elif age_h < 24:
            fl.append(("warn", "Menos de 24 horas de vida"))
    fdv = p.get("fdv") or 0
    if fdv and liq and fdv / liq > 100:
        fl.append(("warn", "Valor total muy inflado frente a su liquidez"))
    if liq and vol / liq > 20:
        fl.append(("warn", "Volumen enorme frente a la liquidez (posible manipulación)"))
    if sells == 0 and buys > 20:
        fl.append(("danger", "Nadie ha vendido: podría no dejar vender"))
    elif sells and buys / sells > 3:
        fl.append(("warn", "Muchas más compras que ventas"))
    if not (p.get("info") or {}).get("websites") and not (p.get("info") or {}).get("socials"):
        fl.append(("info", "Sin web ni redes en DexScreener"))
    return fl, liq, vol, age_h


def goplus_flags(chain, addr):
    cid = GOPLUS_CHAIN.get(chain)
    if not cid:
        return None, [], None
    g = get(f"https://api.gopluslabs.io/api/v1/token_security/{cid}", {"contract_addresses": addr.lower()}, tries=1)
    info = ((g or {}).get("result") or {}).get(addr.lower())
    if not isinstance(info, dict):
        return None, [], None
    fl = []
    if info.get("is_honeypot") == "1":
        fl.append(("danger", "HONEYPOT: no podrás vender"))
    for k, name in (("buy_tax", "compra"), ("sell_tax", "venta")):
        t = _f(info.get(k))
        if t > 0.10:
            fl.append(("danger", f"Impuesto de {name} de {t * 100:.0f}%"))
        elif t > 0.05:
            fl.append(("warn", f"Impuesto de {name} de {t * 100:.0f}%"))
    for k, level, text in (("cannot_sell_all", "danger", "No deja vender todas tus monedas"),
                           ("hidden_owner", "danger", "Tiene un dueño oculto"),
                           ("is_open_source", None, "El código no está verificado"),
                           ("is_mintable", "warn", "El dueño puede crear más monedas"),
                           ("can_take_back_ownership", "warn", "El dueño puede recuperar el control"),
                           ("transfer_pausable", "warn", "El dueño puede pausar las transferencias"),
                           ("is_blacklisted", "warn", "Tiene lista negra: el dueño puede bloquear carteras"),
                           ("is_proxy", "warn", "Contrato actualizable: las reglas pueden cambiar")):
        v = info.get(k)
        if k == "is_open_source":
            if v == "0":
                fl.append(("warn", text))
        elif v == "1":
            fl.append((level, text))
    if _f(info.get("owner_percent")) > 0.10:
        fl.append(("warn", f"El dueño tiene {_f(info.get('owner_percent')) * 100:.0f}% de las monedas"))
    holders = int(_f(info.get("holder_count")))
    if 0 < holders < 100:
        fl.append(("warn", f"Solo {holders} personas tienen este token"))
    return True, fl, holders or None


def rugcheck_flags(addr):
    rc = get(f"https://api.rugcheck.xyz/v1/tokens/{addr}/report/summary", tries=1)
    if not isinstance(rc, dict) or ("risks" not in rc and "score_normalised" not in rc):
        return None, [], None
    fl = []
    for r in (rc.get("risks") or [])[:8]:
        lvl = {"danger": "danger", "warn": "warn"}.get(r.get("level"), "info")
        fl.append((lvl, RUG_ES.get(r.get("name"), str(r.get("name", "Riesgo"))[:80])))
    lp = rc.get("lpLockedPct")
    if lp is not None and _f(lp) < 50:
        fl.append(("warn", f"Solo el {_f(lp):.0f}% de la liquidez está bloqueada"))
    score = rc.get("score_normalised")
    return True, fl, (int(_f(score)) if score is not None else None)


def contract_report(addr):
    """Texto y botones de la revisión básica de un contrato. Devuelve (texto, botones)."""
    kind = "evm" if EVM_RE.match(addr) else "sol" if SOL_RE.match(addr) else None
    if not kind:
        return "Esa dirección no parece válida. Pega la dirección completa del contrato (empieza con 0x en Ethereum/BSC/Base, o es una cadena larga en Solana).", None
    d = get(f"{DEX}/latest/dex/tokens/{addr}")
    same = (lambda a: a.lower() == addr.lower()) if kind == "evm" else (lambda a: a == addr)
    pairs = [x for x in (d or {}).get("pairs") or [] if same((x.get("baseToken") or {}).get("address", ""))]
    if not pairs:
        return ("No encontré ese contrato con pares de trading en DexScreener. Si es un token que te ofrecen para comprar, "
                "que no tenga mercado visible ya es una razón para desconfiar."), None
    p = max(pairs, key=lambda x: (x.get("liquidity") or {}).get("usd", 0) or 0)
    flags, liq, vol, age_h = dex_risk_flags(p)
    checked, extra, info = None, [], None
    if kind == "evm":
        checked, extra, info = goplus_flags(p.get("chainId"), addr)
    else:
        checked, extra, info = rugcheck_flags(addr)
    flags = extra + flags
    order = {"danger": 0, "warn": 1, "info": 2}
    flags.sort(key=lambda f_: order[f_[0]])
    nd = sum(1 for f_ in flags if f_[0] == "danger")
    nw = sum(1 for f_ in flags if f_[0] == "warn")
    if nd >= 2 or (nd >= 1 and liq < 10_000):
        verdict = "🔴 <b>Riesgo MUY ALTO</b>"
    elif nd == 1:
        verdict = "🔴 <b>Riesgo ALTO</b>"
    elif nw >= 3:
        verdict = "🟠 <b>Riesgo medio-alto</b>"
    elif nw >= 1:
        verdict = "🟡 <b>Riesgo medio</b>"
    elif checked:
        verdict = "🟢 <b>Sin alertas graves en lo que revisé</b> (eso no significa que sea seguro)"
    else:
        verdict = "⚪ <b>Revisión incompleta</b>: no pude consultar el análisis de seguridad"
    b = p.get("baseToken") or {}
    age = "?" if age_h is None else (f"{age_h:.0f} h" if age_h < 48 else f"{age_h / 24:.0f} días")
    icon = {"danger": "🚨", "warn": "⚠️", "info": "ℹ️"}
    lines = ["🔎 <b>Revisión básica de contrato</b>",
             f"<b>{esc(b.get('name', '?'))}</b> ({esc(b.get('symbol', '?'))}) · {esc(p.get('chainId', ''))}",
             f"💧 Liquidez ${fm(liq)} · 📈 Vol 24 h ${fm(vol)} · ⏳ {age}"
             + (f" · 👥 {info:,} dueños" if kind == "evm" and info else ""),
             "", verdict]
    if kind == "sol" and info is not None:
        lines.append(f"Puntaje RugCheck: {info}/100 (más alto = más riesgo)")
    lines += [f"{icon[lv]} {esc(tx_)}" for lv, tx_ in flags[:10]]
    lines.append("\nFuentes: DexScreener + " + (("GoPlus" if kind == "evm" else "RugCheck") if checked else
                                                  ("GoPlus" if kind == "evm" else "RugCheck") + " (no disponible ahora)"))
    lines.append("⚠️ Es una revisión automática y básica: no detecta todo (dueños que cambian reglas después, estafas por redes, "
                 "etc.). Nunca inviertas dinero que no puedas perder. " + DISCLAIMER)
    rows = [[btn("Ver en DexScreener", url=safe_url(p.get("url")))]]
    if kind == "sol":
        rows.append([btn("Ver en RugCheck", url=f"https://rugcheck.xyz/tokens/{addr}")])
    return "\n".join(lines), rows


def cmd_contrato(state, chat, args):
    if not args:
        return send(chat, "🔎 <b>Revisión básica de contratos</b>\nPega la dirección del token. Ejemplo:\n"
                          "<code>/contrato 0x1234…</code>  (Ethereum, BSC, Base…)\n<code>/contrato So11…</code>  (Solana)\n\n"
                          "Te digo liquidez, antigüedad y señales de estafa conocidas. No reemplaza tu propia investigación.")
    text, rows = contract_report(args[0].strip())
    send(chat, text, rows)


# ------------------------- glosario -------------------------
GLOSARIO = {
    "rsi": ("RSI", "Mide de 0 a 100 qué tan rápido subió o bajó una moneda. Sobre 70: subió mucho y puede corregir. Bajo 30: cayó mucho y puede rebotar. No predice: solo avisa que está estirada."),
    "macd": ("MACD", "Compara dos promedios para medir el impulso. Positivo = impulso alcista; negativo = bajista."),
    "promedio movil ema": ("Promedio móvil (EMA)", "El precio promedio de las últimas N velas. Si el precio está sobre su promedio, la tendencia suele ser alcista; si está debajo, bajista."),
    "bollinger": ("Bandas de Bollinger", "Una franja alrededor del precio que se ensancha cuando hay más movimiento. Tocar la banda alta o baja indica que el precio está estirado, no que vaya a revertirse seguro."),
    "soporte": ("Soporte", "Nivel de precio donde la moneda ya frenó caídas antes. Si lo rompe hacia abajo, puede seguir cayendo."),
    "resistencia": ("Resistencia", "Nivel donde la moneda ya frenó subidas antes. Si lo rompe hacia arriba, puede seguir subiendo."),
    "volumen": ("Volumen", "Cuánto dinero se movió en un periodo. Un movimiento con mucho volumen es más creíble que uno con poco."),
    "liquidez": ("Liquidez", "Qué tan fácil es comprar o vender sin mover el precio. Poca liquidez = difícil salir de una moneda."),
    "capitalizacion market cap": ("Capitalización de mercado", "Precio × monedas en circulación. Sirve para comparar el tamaño de dos monedas; el precio solo no dice si es barata."),
    "fdv": ("FDV (valor totalmente diluido)", "Lo que valdría la moneda si ya circularan todas las que existirán. Si es enorme frente a la liquidez, es señal de cuidado."),
    "dca": ("DCA", "Comprar una cantidad fija cada cierto tiempo sin importar el precio. Reduce el riesgo de entrar justo en un pico. Puedes simularlo con /dca."),
    "stop loss": ("Stop loss", "Un precio de salida que decides antes de entrar para limitar la pérdida si sale mal. Usa /riesgo para calcular cuánto comprar."),
    "take profit": ("Take profit", "Un precio objetivo donde decides vender para asegurar ganancia."),
    "apalancamiento": ("Apalancamiento", "Operar con dinero prestado para ganar más con menos capital. También multiplica las pérdidas: con mucho apalancamiento, un movimiento pequeño puede borrarte todo."),
    "liquidacion": ("Liquidación", "Cuando una posición apalancada pierde tanto que el exchange la cierra a la fuerza y pierdes lo apostado."),
    "funding financiacion": ("Funding rate (tasa de financiación)", "Pago periódico entre quienes apuestan a subir y quienes apuestan a bajar en futuros. Muy positiva: exceso de apuestas alcistas con deuda, riesgo de caída brusca. Mira /futuros."),
    "open interest interes abierto": ("Open interest (interés abierto)", "Cuánto dinero hay apostado en contratos de futuros abiertos. Más interés abierto = más apalancamiento en el mercado y movimientos más bruscos."),
    "p2p": ("P2P", "Comprar o vender cripto directamente con otra persona, pagando con tu banco o app local. Nunca liberes los USDT hasta ver el dinero en tu cuenta. Mira /p2p."),
    "stablecoin": ("Stablecoin", "Moneda que busca valer siempre 1 dólar, como USDT o USDC. No es 100% segura: puede perder su paridad."),
    "usdt tether": ("USDT", "La stablecoin más usada. Se usa como dólar digital para comprar y vender otras monedas."),
    "halving": ("Halving", "Evento de Bitcoin, aproximadamente cada cuatro años, donde se reduce a la mitad la recompensa de los mineros. Reduce la emisión nueva."),
    "ballena whale": ("Ballena", "Persona o entidad con tantas monedas que sus compras o ventas pueden mover el precio."),
    "rug pull": ("Rug pull", "Estafa donde los creadores de una moneda retiran la liquidez o venden todo y dejan a los demás con monedas sin valor."),
    "honeypot": ("Honeypot", "Moneda que deja comprar pero no vender. Ves que sube, pero no puedes sacar tu dinero. Usa /contrato para una revisión básica."),
    "slippage deslizamiento": ("Slippage (deslizamiento)", "La diferencia entre el precio que esperabas y el que obtienes al operar. Es mayor en monedas con poca liquidez."),
    "spread": ("Spread", "Diferencia entre el precio de compra y el de venta. Un spread grande es un costo oculto."),
    "fomo": ("FOMO", "Miedo a quedarte fuera: comprar solo porque algo sube mucho. Suele terminar en comprar caro."),
    "hodl": ("HODL", "Mantener tus monedas a largo plazo sin vender por los vaivenes. Nació de un error al escribir hold."),
    "airdrop": ("Airdrop", "Regalo de monedas de un proyecto a ciertos usuarios. Cuidado con los falsos que piden tus claves."),
    "gas comision de red": ("Gas (comisión de red)", "Lo que pagas a la red (como Ethereum) para procesar tu transacción. Cambia según qué tan ocupada esté."),
    "wallet billetera": ("Wallet (billetera)", "App o dispositivo donde guardas tus claves y monedas. Si no controlas las claves, no controlas las monedas."),
    "frase semilla seed": ("Frase semilla", "Las 12 o 24 palabras que recuperan tu wallet. Quien las tenga se queda con tu dinero: nunca las compartas, ni con soporte, ni con este bot."),
    "dyor": ("DYOR", "Haz tu propia investigación. Verifica por tu cuenta antes de invertir; no confíes en un solo mensaje ni en una sola fuente."),
    "long short": ("Long y short", "Long: apuestas a que el precio sube. Short: apuestas a que baja."),
    "bull bear alcista bajista": ("Mercado alcista y bajista (bull / bear)", "Bull: tendencia general al alza. Bear: tendencia general a la baja."),
    "pump and dump": ("Pump and dump", "Grupo que infla el precio de una moneda para vender caro a los que llegan tarde. Muchas memecoins nacen así."),
    "ath maximo historico": ("ATH (máximo histórico)", "El precio más alto que alcanzó una moneda. Comprar cerca del ATH no es bueno ni malo por sí solo: depende del contexto."),
    "memecoin": ("Memecoin", "Moneda creada como broma o moda, sin un uso real detrás. Muy volátil y de altísimo riesgo."),
    "brecha cambiaria": ("Brecha cambiaria", "Diferencia entre el dólar oficial y el dólar del mercado paralelo. Mira /p2p para ver la del USDT."),
    "cruce": ("Cruce alcista / bajista", "Cuando un promedio corto cruza por encima (alcista) o por debajo (bajista) de uno largo. Es una señal de tendencia que llega con retraso."),
}


def _plain(t):
    return "".join(c for c in unicodedata.normalize("NFD", t.lower()) if unicodedata.category(c) != "Mn").strip()


def find_term(q):
    q = _plain(q)
    if not q:
        return None
    for key, val in GLOSARIO.items():
        if q in key.split() or q == key or q == _plain(val[0]):
            return val
    for key, val in GLOSARIO.items():
        if q in key or q in _plain(val[0]):
            return val
    return None


def term_of_day():
    vals = list(GLOSARIO.values())
    return vals[datetime.now(TZ).toordinal() % len(vals)]


def cmd_glosario(state, chat, args):
    if not args:
        names = " · ".join(v[0].split(" (")[0] for v in GLOSARIO.values())
        t = term_of_day()
        return send(chat, "📖 <b>Glosario cripto</b>\nEscribe <code>/glosario RSI</code> (o cualquier término).\n\n" + esc(names) +
                    f"\n\n💡 <b>Término del día: {esc(t[0])}</b>\n{esc(t[1])}",
                    [[btn("RSI", "/glosario rsi"), btn("Soporte", "/glosario soporte"), btn("P2P", "/glosario p2p")],
                     [btn("Honeypot", "/glosario honeypot"), btn("DCA", "/glosario dca")]])
    t = find_term(" ".join(args))
    if not t:
        return send(chat, "No tengo ese término todavía. Prueba con /glosario para ver la lista.")
    send(chat, f"📖 <b>{esc(t[0])}</b>\n{esc(t[1])}\n\n" + DISCLAIMER)


# ------------------------- meta y tarjeta -------------------------
def cmd_meta(state, chat, args):
    k = str(chat)
    if args and args[0].lower() in ("borrar", "quitar", "0"):
        state["goals"].pop(k, None)
        return send(chat, "✅ Meta borrada.")
    if args:
        try:
            v = num(args[0])
            assert 1 <= v <= 1e9
        except Exception:
            return send(chat, "Ejemplo: /meta 1000  (cuánto quieres que valga tu cartera, en dólares)")
        state["goals"][k] = v
    goal = state["goals"].get(k)
    if not goal:
        return send(chat, "🎯 Pon una meta para tu cartera y verás tu progreso.\nEjemplo: /meta 1000  (dólares). Para quitarla: /meta borrar")
    pr, hold = prices(), state["port"].get(k) or {}
    total = sum(h["qty"] * pr[b]["price"] for b, h in hold.items() if b in pr)
    pct = total / goal * 100
    falta = max(0.0, goal - total)
    send(chat, f"🎯 <b>Tu meta: ${goal:,.0f}</b>\n{barra(pct)} {min(pct, 999):.0f}%\nTu cartera hoy: ${total:,.2f}\n"
               + (f"Te faltan ${falta:,.2f}." if falta else "¡Llegaste a tu meta! 🎉 Decide con calma si vendes o fijas una nueva.")
               + "\n\nLas metas ayudan a tener un plan; no garantizan que el precio llegue.", [[btn("💼 Mi cartera", "/cartera")]])


def cmd_tarjeta(state, chat, args):
    hold = state["port"].get(str(chat)) or {}
    pr, rows, total, cost_total, val_cost = prices(), [], 0.0, 0.0, 0.0
    for b, h in hold.items():
        p = pr.get(b)
        if not p:
            continue
        val = h["qty"] * p["price"]
        total += val
        pnl = None
        if h.get("cost"):
            cost_total += h["qty"] * h["cost"]
            val_cost += val
            pnl = (p["price"] / h["cost"] - 1) * 100
        rows.append((b, val, pnl))
    if not rows or total <= 0:
        return send(chat, "Tu cartera está vacía. Agrega monedas con /agregar BTC 0.01 65000 y luego pide tu /tarjeta.")
    rows.sort(key=lambda r: -r[1])
    items = [(b, v / total * 100, pnl) for b, v, pnl in rows][:7]
    total_pnl = (val_cost / cost_total - 1) * 100 if cost_total else None
    send_photo(chat, chart_card(items, total_pnl),
               "💼 Mi cartera (sin montos, solo porcentajes). Hecha con " + ("@" + BOT["user"] if BOT["user"] else "Cripdex") +
               "\n⚠️ No es consejo financiero.")


def cmd_miid(state, chat, args):
    send(chat, f"Tu ID de Telegram es <code>{chat}</code>.\nPónlo en Render como OWNER_ID para recibir avisos de salud.")


def cmd_estado(state, chat, args):
    if not OWNER_ID:
        return send(chat, "Aún no hay administrador. Usa /miid, copia tu ID y ponlo en Render como OWNER_ID.")
    if chat != OWNER_ID:
        return send(chat, "Este comando es solo para el administrador.")
    last = HEALTH["last_ok_save"]
    ago = f"hace {int((time.time() - last) / 60)} min" if last else "nunca"
    up = int((time.time() - HEALTH["started"]) / 60)
    send(chat, "🩺 <b>Estado de Cripdex</b>\n"
               f"Encendido hace {up} min\n"
               f"Suscriptores: {len(state['subs'])}\n"
               f"Carteras guardadas: {len(state['port'])}\n"
               f"Alertas de precio: {len(state['alerts'])}\n"
               f"Último guardado en la nube: {ago}\n"
               f"Fallos de guardado seguidos: {HEALTH['save_fail_streak']}\n"
               f"Último error: {esc(HEALTH['last_error']) or 'ninguno'}\n"
               f"Errores en tareas automáticas: {HEALTH['task_errors']}")


COMMANDS = {"/start": cmd_start, "/menu": cmd_start, "/ayuda": cmd_ayuda, "/help": cmd_ayuda,
            "/herramientas": cmd_herramientas, "/top": cmd_top, "/heatmap": cmd_heatmap,
            "/precio": cmd_precio, "/grafico": cmd_grafico, "/analisis": cmd_analisis,
            "/comparar": cmd_comparar, "/mercado": cmd_mercado, "/noticias": cmd_noticias,
            "/escaner": cmd_escaner, "/memes": cmd_memes, "/agregar": cmd_agregar,
            "/quitar": cmd_quitar, "/cartera": cmd_cartera, "/seguir": cmd_seguir,
            "/dejar": cmd_dejar, "/lista": cmd_lista, "/convertir": cmd_convertir,
            "/ganancia": cmd_ganancia, "/riesgo": cmd_riesgo, "/dca": cmd_dca,
            "/alerta": cmd_alerta, "/alertap2p": cmd_alertap2p, "/alertas": cmd_alertas, "/borrar": cmd_borrar,
            "/suscribir": cmd_suscribir, "/silenciar": cmd_silenciar, "/config": cmd_config,
            "/toggle": cmd_toggle, "/umbral": cmd_umbral, "/estado": cmd_estado, "/miid": cmd_miid,
            "/p2p": cmd_p2p, "/futuros": cmd_futuros, "/contrato": cmd_contrato, "/glosario": cmd_glosario,
            "/meta": cmd_meta, "/tarjeta": cmd_tarjeta, "/pro": cmd_pro, "/darpro": cmd_darpro,
            "/terminos": cmd_terminos, "/borrar_mis_datos": cmd_borrar_mis_datos,
            "/estadisticas": cmd_estadisticas}

NATURAL = {"precio": "/precio", "grafico": "/grafico", "gráfico": "/grafico", "analisis": "/analisis",
           "análisis": "/analisis", "comparar": "/comparar", "top": "/top", "mercado": "/mercado",
           "noticias": "/noticias", "memes": "/memes", "cartera": "/cartera", "ayuda": "/ayuda",
           "menu": "/start", "menú": "/start", "p2p": "/p2p", "futuros": "/futuros", "glosario": "/glosario",
           "heatmap": "/heatmap", "escaner": "/escaner", "escáner": "/escaner", "contrato": "/contrato"}

_hits = {}


def natural(chat, text):
    """Atajos sin barra: 'btc' -> /precio btc, 'sol 1h' -> /grafico sol 1h. Solo en chats privados."""
    if chat < 0:
        return None
    parts = text.split()
    if not parts or len(parts) > 6:
        return None
    w = parts[0].lower()
    if w in NATURAL:
        return " ".join([NATURAL[w]] + parts[1:])
    if len(parts) <= 2 and re.fullmatch(r"[a-z0-9]{2,10}", w):
        if len(parts) == 2 and parts[1].lower() not in INTERVALS:
            return None
        if norm_base(w) in prices():
            return f"/grafico {w} {parts[1].lower()}" if len(parts) == 2 else f"/precio {w}"
    return None


def handle(state, chat, text):
    text = text.strip()
    if not text:
        return
    now = time.time()
    _hits[chat] = [t for t in _hits.get(chat, []) if now - t < 60] + [now]
    if len(_hits[chat]) > 15:
        return
    if not text.startswith("/"):
        try:
            text = natural(chat, text) or ""
        except Exception as e:
            print("Error en atajo:", repr(e))
            text = ""
        if not text:
            return
    parts = text.split()
    cmd = parts[0].lower().split("@")[0]
    fn = COMMANDS.get(cmd)
    if not fn:
        if cmd.startswith("/"):
            send(chat, "No conozco ese comando. Mira /ayuda", MENU)
        return
    st = state.setdefault("stats", {"cmds": {}, "seen": {}})
    st["cmds"][cmd] = st["cmds"].get(cmd, 0) + 1
    st["seen"][str(chat)] = int(now)
    if len(st["seen"]) > 5000:   # que no crezca sin fin
        for k in sorted(st["seen"], key=st["seen"].get)[:500]:
            st["seen"].pop(k, None)
    try:
        fn(state, chat, parts[1:])
    except Exception as e:
        print("Error en", cmd, repr(e))
        send(chat, "Ups, algo falló. Intenta de nuevo en un momento.")


# ------------------------- tareas automaticas -------------------------
def task_alerts(state):
    if not state["alerts"]:
        return
    pr = {}
    if any(not a["sym"].startswith("P2P:") for a in state["alerts"]):
        d = get(f"{DATA}/api/v3/ticker/price")
        if d:
            pr = {x["symbol"]: float(x["price"]) for x in d}
    mids, keep = {}, []
    for a in state["alerts"]:
        if a["sym"].startswith("P2P:"):
            fiat = a["sym"][4:]
            if fiat not in mids:
                mids[fiat] = p2p_mid(fiat)
            p = mids[fiat]
        else:
            p = pr.get(a["sym"])
        hit = p is not None and ((a["dir"] == "up" and p >= a["price"]) or (a["dir"] == "down" and p <= a["price"]))
        if hit:
            if a["sym"].startswith("P2P:"):
                send(a["chat"], f"🔔 <b>USDT en {a['sym'][4:]}</b> (P2P) llegó a {p:,.2f} (tu alerta: {a['price']:,.2f})",
                     [[btn("💵 Ver P2P", f"/p2p {a['sym'][4:]}")]])
            else:
                send(a["chat"], f"🔔 <b>{a['sym'][:-4]}</b> llegó a ${fp(p)} (tu alerta: ${fp(a['price'])})",
                     [[btn("📊 Gráfico", f"/grafico {a['sym'][:-4]} 1h")]])
        else:
            keep.append(a)
    state["alerts"] = keep


def task_movers(state):
    mk = market(MOVER_MIN_VOL)
    if not mk:
        return
    now = time.time()
    snaps = state["snaps"]
    ref = None
    for s in snaps:
        if 2700 <= now - s["t"] <= 5400:
            ref = s
    if ref and state["subs"]:
        mins = int((now - ref["t"]) / 60)
        found = []
        for x in mk:
            old = ref["p"].get(x["sym"])
            if old:
                ch = (x["price"] / old - 1) * 100
                if abs(ch) >= MOVER_MIN:
                    found.append((ch, x))
        found.sort(key=lambda z: abs(z[0]), reverse=True)
        per = {}
        for ch, x in found[:12]:
            targets = [c for c in state["subs"] if pref(state, c)["mov_on"] and abs(ch) >= pref(state, c)["mov"]]
            if targets and cooled(state, f"mv:{x['sym']}:{'u' if ch > 0 else 'd'}", 3):
                line = (f"{'🚀' if ch > 0 else '💥'} <b>{x['base']}</b> ${fp(x['price'])} "
                        f"{pc(ch)} en ~{mins} min · vol 24 h ${fm(x['qv'])}")
                for c in targets:
                    per.setdefault(c, []).append(line)
        for c, lines in per.items():
            notify(state, c, "⚡ <b>Movimientos fuertes</b>\n" + "\n".join(lines[:5]) +
                   "\n\nVer gráfico: /grafico MONEDA. " + DISCLAIMER)
    if not snaps or now - snaps[-1]["t"] >= 900:
        top = sorted(mk, key=lambda x: x["qv"], reverse=True)[:200]
        snaps.append({"t": now, "p": {x["sym"]: x["price"] for x in top}})
        state["snaps"] = snaps[-6:]


def task_volumen(state):
    if not any(pref(state, c)["vol"] for c in state["subs"]):
        return
    lines = []
    for x in sorted(scan_cached(), key=lambda x: -x["ratio"]):
        if x["ratio"] >= VOL_SPIKE and cooled(state, f"vol:{x['base']}", 6):
            lines.append(f"🔊 <b>{x['base']}</b> ${fp(x['price'])} · volumen {x['ratio']:.1f}× lo normal · {pc(x['chg'])}")
    if lines:
        broadcast(state, "vol", "📊 <b>Volumen inusual</b>\n" + "\n".join(lines[:5]) +
                  "\n\nMucho volumen = algo está pasando, pero no dice hacia dónde irá. " + DISCLAIMER)


def task_memes(state):
    if not any(pref(state, c)["memes"] for c in state["subs"]):
        return
    sent = 0
    for p, flags, age_h in meme_scan():
        b = p.get("baseToken") or {}
        if sent < 3 and cooled(state, f"meme:{p.get('chainId')}:{b.get('address')}", 24):
            broadcast(state, "memes", "🐸 <b>Memecoin con actividad</b>\n" + meme_text(p, flags, age_h) +
                      "\n\n🛡 Pasó los filtros básicos, pero eso NO la hace segura.",
                      [[btn("Ver en DexScreener", url=safe_url(p.get("url")))]])
            sent += 1


def task_daily(state):
    now = datetime.now(timezone.utc)
    today = now.strftime("%Y-%m-%d")
    if not (DAILY_HOUR_UTC <= now.hour < 23) or state.get("daily") == today:
        return
    if not any(pref(state, c)["daily"] for c in state["subs"]):
        state["daily"] = today
        return
    mk = market()
    parts = ["🌅 <b>Resumen del día</b>\n", market_summary()]
    if DAILY_P2P_FIAT:
        try:
            line = p2p_line(DAILY_P2P_FIAT)
        except Exception as e:
            print("Error en línea P2P:", repr(e))
            line = ""
        if line:
            parts.append(line)
    if mk:
        s_ = sorted(mk, key=lambda x: x["chg"], reverse=True)
        parts.append("\n🚀 Lideran: " + " · ".join(f"<b>{x['base']}</b> {x['chg']:+.1f}%" for x in s_[:3]))
        parts.append("💥 Más caen: " + " · ".join(f"<b>{x['base']}</b> {x['chg']:+.1f}%" for x in s_[-3:][::-1]))
    items = news(3)
    if items:
        parts.append("\n📰 <b>Titulares</b> (en inglés)\n" + "\n".join(news_lines(items)))
    t = term_of_day()
    parts.append(f"\n💡 <b>Término del día: {esc(t[0])}</b>\n{esc(t[1])}")
    parts.append("\n" + DISCLAIMER)
    png = chart_heatmap(sorted(mk, key=lambda x: x["qv"], reverse=True)[:30]) if mk else None
    broadcast(state, "daily", "\n".join(parts), [[btn("📈 Top", "/top"), btn("🔍 Escáner", "/escaner")]], photo=png)
    state["daily"] = today


def run_tasks(state):
    now = time.time()
    for name, every, fn in (("alerts", 30, task_alerts), ("movers", 120, task_movers),
                            ("memes", 300, task_memes), ("vol", 600, task_volumen),
                            ("daily", 300, task_daily)):
        if now - state["last"].get(name, 0) >= every:
            state["last"][name] = now
            try:
                fn(state)
            except Exception as e:
                HEALTH["task_errors"] += 1
                print("Error en tarea", name, repr(e))


# ------------------------- bucle principal -------------------------
def poll(state, timeout):
    try:
        r = SESSION.post(f"{TG}/getUpdates", json={"offset": state["offset"], "timeout": timeout,
                          "allowed_updates": ["message", "callback_query"]}, timeout=timeout + 15).json()
    except Exception as e:
        print("getUpdates error:", safe(e))
        time.sleep(3)
        return
    if not r.get("ok"):   # p. ej. 409 (otra copia del bot activa) o 429: esperar, no martillar
        print("getUpdates no ok:", r.get("error_code"), str(r.get("description"))[:120])
        time.sleep(min(int((r.get("parameters") or {}).get("retry_after", 5)), 30))
        return
    for u in r.get("result", []):
        state["offset"] = u["update_id"] + 1
        msg, cq = u.get("message"), u.get("callback_query")
        if msg and msg.get("text"):
            handle(state, msg["chat"]["id"], msg["text"])
        elif cq:
            tg("answerCallbackQuery", callback_query_id=cq["id"])
            data = cq.get("data", "")
            if data.startswith("cmd:") and cq.get("message"):
                handle(state, cq["message"]["chat"]["id"], data[4:])


_beat = {"t": time.time()}   # última vez que el bucle principal dio señales de vida


class _Health(BaseHTTPRequestHandler):
    def do_GET(self):
        ok = time.time() - _beat["t"] < 300 and HEALTH["save_fail_streak"] < 10   # 503 = algo va mal
        self.send_response(200 if ok else 503)
        self.end_headers()
        self.wfile.write(b"Cripdex activo" if ok else b"Cripdex sin respuesta")

    def log_message(self, *a):
        pass


def _watchdog():
    """Si el bucle principal lleva 10 min sin moverse, cierra el programa: el hosting lo reinicia solo."""
    while True:
        time.sleep(30)
        if time.time() - _beat["t"] > 600:
            print("Watchdog: el bot se congeló; reiniciando")
            os._exit(1)


def start_health():
    """Algunos hostings exigen que el programa responda en un puerto (variable PORT)."""
    port = os.getenv("PORT")
    if port:
        srv = HTTPServer(("0.0.0.0", int(port)), _Health)
        threading.Thread(target=srv.serve_forever, daemon=True).start()


def main():
    if not TOKEN:
        raise SystemExit("Falta el secreto TELEGRAM_TOKEN.")
    if Fernet is None:
        raise SystemExit("Falta instalar 'cryptography' (revisa el paso pip install del workflow).")
    signal.signal(signal.SIGTERM, lambda *a: sys.exit(0))   # asi el estado se guarda al detenerlo
    start_health()
    try:
        state = load_state()
    except SystemExit as e:
        notify_owner("load", f"🛑 Cripdex no pudo arrancar: {e}")
        raise
    me = (tg("getMe") or {}).get("result") or {}
    if me.get("username") and not BOT["user"]:
        BOT["user"] = me["username"]
    if not OWNER_ID:
        print("Aviso: falta OWNER_ID en Render (usa /miid para verlo)")
    notify_owner("start", f"✅ Cripdex arrancó. Suscriptores: {len(state['subs'])}.")
    tg("setMyCommands", commands=[{"command": c, "description": d} for c, d in BOT_COMMANDS])
    forever = RUN_SECONDS <= 0
    if forever:
        threading.Thread(target=_watchdog, daemon=True).start()
    end = float("inf") if forever else time.time() + RUN_SECONDS
    try:
        while time.time() < end:
            _beat["t"] = time.time()
            run_tasks(state)
            left = 20 if forever else int(end - time.time())
            poll(state, max(1, min(20, left)))
            save_state(state)
    finally:
        save_state(state, force=True)


if __name__ == "__main__":
    main()
