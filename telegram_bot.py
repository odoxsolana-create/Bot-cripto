"""
Bot de Telegram para el mercado cripto (SOLO informa, nunca compra ni vende).
Comandos: /top /precio /grafico /analisis /comparar /mercado /memes /alerta /suscribir
Corre en GitHub Actions: cada ejecucion escucha mensajes ~4,5 min y se relanza sola.
"""
import os, io, re, json, time, html
from datetime import datetime, timezone
import requests
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

TOKEN = os.getenv("TELEGRAM_TOKEN", "")
RUN_SECONDS = int(os.getenv("RUN_SECONDS", "270"))
DATA = "https://data-api.binance.vision"      # precios publicos de Binance
DEX = "https://api.dexscreener.com"           # memecoins (publico, sin clave)
TG = f"https://api.telegram.org/bot{TOKEN}"
STATE_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "telegram_state.json")

MOVER_PCT = 5.0            # aviso si una moneda se mueve +-5% en ~1 hora
MOVER_MIN_VOL = 3_000_000  # solo monedas con mas de 3M USDT de volumen diario
INTERVALS = ["15m", "1h", "4h", "1d"]
STABLES = {"USDC", "FDUSD", "TUSD", "USDP", "DAI", "BUSD", "EUR", "USD1", "USDE", "XUSD", "AEUR"}
DISCLAIMER = "⚠️ Es información, no consejo financiero. Nadie puede garantizar ganancias."


# ------------------------- utilidades -------------------------
def get(url, params=None, tries=2):
    for _ in range(tries):
        try:
            r = requests.get(url, params=params, timeout=15, headers={"User-Agent": "Mozilla/5.0"})
            if r.status_code == 200:
                return r.json()
        except (requests.RequestException, ValueError):
            pass
        time.sleep(1)
    return None


def esc(s):
    return html.escape(str(s))


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


def pc(x):
    return f"{'🟢' if x >= 0 else '🔴'} {x:+.2f}%"


def norm_sym(s):
    s = re.sub(r"[^A-Za-z0-9]", "", s).upper()
    return s if s.endswith("USDT") else s + "USDT"


# ------------------------- Telegram -------------------------
def tg(method, timeout=30, **data):
    try:
        return requests.post(f"{TG}/{method}", json=data, timeout=timeout).json()
    except Exception as e:
        print("Telegram error:", e)
        return {}


def send(chat, text, buttons=None):
    data = {"chat_id": chat, "text": text, "parse_mode": "HTML", "disable_web_page_preview": True}
    if buttons:
        data["reply_markup"] = {"inline_keyboard": buttons}
    return tg("sendMessage", **data)


def send_photo(chat, png, caption="", buttons=None):
    data = {"chat_id": chat, "caption": caption, "parse_mode": "HTML"}
    if buttons:
        data["reply_markup"] = json.dumps({"inline_keyboard": buttons})
    try:
        return requests.post(f"{TG}/sendPhoto", data=data, files={"photo": ("g.png", png, "image/png")},
                             timeout=60).json()
    except Exception as e:
        print("Foto error:", e)
        return {}


def btn(text, cmd=None, url=None):
    return {"text": text, "url": url} if url else {"text": text, "callback_data": f"cmd:{cmd}"}


MENU = [
    [btn("📈 Top del día", "/top"), btn("🐸 Memecoins", "/memes")],
    [btn("₿ Análisis BTC", "/analisis BTC"), btn("🌡 Mercado", "/mercado")],
    [btn("🔔 Activar avisos", "/suscribir"), btn("❓ Ayuda", "/ayuda")],
]


# ------------------------- estado -------------------------
def load_state():
    base = {"offset": 0, "subs": [], "alerts": [], "next_id": 1, "snaps": [], "cool": {}, "last": {}}
    if os.path.exists(STATE_FILE):
        with open(STATE_FILE) as f:
            base.update(json.load(f))
    return base


def save_state(s):
    now = time.time()
    s["cool"] = {k: v for k, v in s["cool"].items() if now - v < 172800}
    with open(STATE_FILE, "w") as f:
        json.dump(s, f)


def cooled(state, key, hours):
    """True si ya paso el tiempo de espera para volver a avisar de 'key'."""
    now = time.time()
    if now - state["cool"].get(key, 0) >= hours * 3600:
        state["cool"][key] = now
        return True
    return False


def broadcast(state, text, buttons=None):
    for chat in list(state["subs"]):
        r = send(chat, text, buttons)
        if r and r.get("ok") is False and r.get("error_code") in (400, 403):
            state["subs"].remove(chat)


# ------------------------- datos de mercado -------------------------
_cache = {}


def market(min_vol=5e6):
    """Lista de monedas USDT de Binance con su movimiento de 24 h (cache 60 s)."""
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


# ------------------------- indicadores -------------------------
def ema(vals, n):
    k = 2 / (n + 1)
    out = [vals[0]]
    for v in vals[1:]:
        out.append(v * k + out[-1] * (1 - k))
    return out


def rsi(vals, n=14):
    if len(vals) < n + 2:
        return None
    g = l = 0.0
    for i in range(1, n + 1):
        d = vals[i] - vals[i - 1]
        g += max(d, 0)
        l += max(-d, 0)
    ag, al = g / n, l / n
    for i in range(n + 1, len(vals)):
        d = vals[i] - vals[i - 1]
        ag = (ag * (n - 1) + max(d, 0)) / n
        al = (al * (n - 1) + max(-d, 0)) / n
    return 100.0 if al == 0 else 100 - 100 / (1 + ag / al)


def macd_hist(vals):
    line = [a - b for a, b in zip(ema(vals, 12), ema(vals, 26))]
    sig = ema(line, 9)
    return line[-1] - sig[-1]


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
    ax.set_xticklabels([datetime.fromtimestamp(kl[i]["t"], timezone.utc).strftime(fmt) for i in idx])


def to_png(fig):
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=110, facecolor=BG, bbox_inches="tight")
    plt.close(fig)
    return buf.getvalue()


def chart_candles(sym, kl, interval, full):
    closes = [k["c"] for k in full]
    e20, e50 = ema(closes, 20)[-len(kl):], ema(closes, 50)[-len(kl):]
    fig, (ax, av) = plt.subplots(2, 1, figsize=(8, 6), sharex=True, gridspec_kw={"height_ratios": [4, 1]})
    fig.patch.set_facecolor(BG)
    for i, k in enumerate(kl):
        col = "#2ecc71" if k["c"] >= k["o"] else "#e74c3c"
        ax.vlines(i, k["l"], k["h"], color=col, linewidth=1)
        ax.bar(i, max(abs(k["c"] - k["o"]), k["c"] * 1e-5), bottom=min(k["o"], k["c"]), color=col, width=0.7)
        av.bar(i, k["v"], color=col, width=0.7)
    ax.plot(e20, color="#f1c40f", linewidth=1.2, label="Promedio 20")
    ax.plot(e50, color="#3498db", linewidth=1.2, label="Promedio 50")
    ax.legend(facecolor=BG, labelcolor=FG, fontsize=8, loc="upper left")
    ax.set_title(f"{sym[:-4]}/USDT · velas de {interval}", color=FG)
    for a in (ax, av):
        _style(a)
    av.set_ylabel("Volumen", color=FG, fontsize=8)
    _labels(av, kl, interval)
    return to_png(fig)


def chart_compare(series):
    fig, ax = plt.subplots(figsize=(8, 5))
    fig.patch.set_facecolor(BG)
    colors = ["#f1c40f", "#3498db", "#2ecc71", "#e74c3c"]
    for (name, kl), col in zip(series.items(), colors):
        base = kl[0]["c"]
        ax.plot([k["c"] / base * 100 for k in kl], color=col, linewidth=1.8, label=name)
    ax.axhline(100, color="#555", linewidth=0.8, linestyle="--")
    ax.set_title("Comparación (todas empiezan en 100)", color=FG)
    ax.legend(facecolor=BG, labelcolor=FG)
    _style(ax)
    first = next(iter(series.values()))
    _labels(ax, first, "1d")
    return to_png(fig)


# ------------------------- comandos -------------------------
def cmd_start(state, chat, args):
    send(chat, "👋 <b>Hola, soy tu bot de mercado cripto.</b>\n\n"
               "Te muestro precios, las monedas que más se mueven, gráficos, análisis, comparaciones "
               "y memecoins con filtros anti-estafa. <b>Yo no compro ni vendo por nadie:</b> cada quien "
               "decide si invierte y cuánto.\n\n" + DISCLAIMER, MENU)


def cmd_ayuda(state, chat, args):
    send(chat, "<b>Comandos</b>\n"
               "/top – monedas que más suben y bajan hoy\n"
               "/precio BTC – precio y movimiento del día\n"
               "/grafico BTC 1h – gráfico (15m, 1h, 4h, 1d)\n"
               "/analisis BTC – tendencia, RSI, soporte y resistencia\n"
               "/comparar BTC ETH SOL – compara hasta 4 monedas\n"
               "/mercado – ánimo del mercado (miedo/codicia)\n"
               "/memes – memecoins que suenan, con alertas de riesgo\n"
               "/alerta BTC 70000 – te aviso cuando llegue a ese precio\n"
               "/alertas – ver tus alertas · /borrar 3 – quitar una\n"
               "/suscribir – avisos automáticos (movimientos fuertes y memecoins)\n"
               "/silenciar – apagar los avisos\n\n" + DISCLAIMER, MENU)


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
    send(chat, "\n".join(lines), [[btn("🐸 Memecoins", "/memes"), btn("🌡 Mercado", "/mercado")]])


def cmd_precio(state, chat, args):
    if not args:
        return send(chat, "Escribe la moneda. Ejemplo: /precio BTC")
    t = ticker(norm_sym(args[0]))
    if not t:
        return send(chat, "No encuentro esa moneda en Binance. Prueba con BTC, ETH, SOL, XRP, DOGE…")
    pos = (t["price"] - t["lo"]) / (t["hi"] - t["lo"]) * 100 if t["hi"] > t["lo"] else 50
    send(chat, f"💰 <b>{t['base']}/USDT</b>\nPrecio: <b>${fp(t['price'])}</b>\n24 h: {pc(t['chg'])}\n"
               f"Máximo 24 h: ${fp(t['hi'])}\nMínimo 24 h: ${fp(t['lo'])}\n"
               f"Está al {pos:.0f}% de su rango de hoy (0% = mínimo, 100% = máximo)\n"
               f"Volumen 24 h: ${fm(t['qv'])}",
         [[btn("📊 Gráfico", f"/grafico {t['base']} 1h"), btn("🧠 Análisis", f"/analisis {t['base']}")],
          [btn("Abrir en Binance", url=f"https://www.binance.com/en/trade/{t['base']}_USDT")]])


def cmd_grafico(state, chat, args):
    if not args:
        return send(chat, "Ejemplo: /grafico BTC 1h  (opciones: 15m, 1h, 4h, 1d)")
    sym = norm_sym(args[0])
    iv = args[1].lower() if len(args) > 1 else "1h"
    if iv not in INTERVALS:
        return send(chat, "Intervalos válidos: 15m, 1h, 4h, 1d")
    full = klines(sym, iv, 120)
    if not full:
        return send(chat, "No encuentro esa moneda en Binance.")
    kl = full[-60:]
    chg = (kl[-1]["c"] / kl[0]["o"] - 1) * 100
    send_photo(chat, chart_candles(sym, kl, iv, full),
               f"<b>{sym[:-4]}</b> ${fp(kl[-1]['c'])} · en este gráfico {pc(chg)}",
               [[btn("🧠 Análisis", f"/analisis {sym[:-4]}")]])


def cmd_analisis(state, chat, args):
    if not args:
        return send(chat, "Ejemplo: /analisis BTC  (o /analisis ETH 1d)")
    sym = norm_sym(args[0])
    iv = args[1].lower() if len(args) > 1 and args[1].lower() in INTERVALS else "4h"
    full = klines(sym, iv, 150)
    if not full or len(full) < 60:
        return send(chat, "No tengo datos suficientes de esa moneda.")
    closes = [k["c"] for k in full]
    price = closes[-1]
    e20, e50 = ema(closes, 20)[-1], ema(closes, 50)[-1]
    r = rsi(closes)
    mh = macd_hist(closes)
    recent = full[-48:]
    support, resist = min(k["l"] for k in recent), max(k["h"] for k in recent)
    vol = sum((k["h"] - k["l"]) / k["c"] for k in recent) / len(recent) * 100
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
    dist_s, dist_r = (price / support - 1) * 100, (resist / price - 1) * 100
    send_photo(chat, chart_candles(sym, full[-60:], iv, full), f"🧠 <b>Análisis {sym[:-4]}</b> · velas de {iv}")
    send(chat, f"🧠 <b>{sym[:-4]}/USDT</b> · velas de {iv}\n"
               f"Precio: <b>${fp(price)}</b>\n"
               f"Tendencia: {trend}\n"
               f"• Precio {'sobre' if price > e50 else 'bajo'} su promedio de 50 velas\n"
               f"• Promedio corto {'sobre' if e20 > e50 else 'bajo'} el largo\n"
               f"• Impulso (MACD): {'positivo' if mh > 0 else 'negativo'}\n"
               f"RSI: {rtxt}\n"
               f"Soporte cercano: ${fp(support)} ({dist_s:.1f}% abajo)\n"
               f"Resistencia cercana: ${fp(resist)} ({dist_r:.1f}% arriba)\n"
               f"Movimiento típico por vela: {vol:.2f}%\n\n" + DISCLAIMER,
         [[btn("Abrir en Binance", url=f"https://www.binance.com/en/trade/{sym[:-4]}_USDT")]])


def cmd_comparar(state, chat, args):
    syms = [norm_sym(a) for a in args[:4]]
    if len(syms) < 2:
        return send(chat, "Ejemplo: /comparar BTC ETH SOL")
    series, rows = {}, []
    for s in syms:
        kl = klines(s, "1d", 30)
        t = ticker(s)
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
    send(chat, "\n".join(lines) + "\n\n" + DISCLAIMER, [[btn("📈 Top del día", "/top")]])


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
        addrs = ",".join(a for _, a in toks[i:i + 30])
        d = get(f"{DEX}/latest/dex/tokens/{addrs}")
        for p in (d or {}).get("pairs") or []:
            b = (p.get("baseToken") or {})
            if b.get("address") not in wanted:
                continue
            k = (p.get("chainId"), b["address"])
            liq = (p.get("liquidity") or {}).get("usd", 0) or 0
            if k not in best or liq > ((best[k].get("liquidity") or {}).get("usd", 0) or 0):
                best[k] = p
    res = []
    for k, p in best.items():
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
            f"💧 Liquidez ${fm(liq)} · 📈 Vol 24 h ${fm(vol)} · ⏳ {age}\n"
            + "\n".join(flags))


def cmd_memes(state, chat, args):
    send(chat, "🔎 Buscando memecoins con actividad real…")
    res = meme_scan()
    if not res:
        return send(chat, "Ninguna memecoin pasó los filtros ahora mismo. Eso es normal: casi todas son riesgo alto.")
    for p, flags, age_h in res[:5]:
        send(chat, meme_text(p, flags, age_h), [[btn("Ver en DexScreener", url=p.get("url", "https://dexscreener.com"))]])
    send(chat, "🛡 Filtros: liquidez ≥ 30K, volumen ≥ 50K, ≥ 200 operaciones, que se pueda vender y ≥ 6 h de vida.\n"
               "Pasar los filtros NO significa que sea segura. Muchas memecoins caen a cero. "
               "Si decides entrar, usa solo dinero que puedas perder.")


# ------------------------- alertas del usuario -------------------------
def cmd_alerta(state, chat, args):
    if len(args) < 2:
        return send(chat, "Ejemplo: /alerta BTC 70000")
    sym = norm_sym(args[0])
    try:
        target = float(args[1].replace(",", "."))
    except ValueError:
        return send(chat, "El precio debe ser un número. Ejemplo: /alerta BTC 70000")
    t = ticker(sym)
    if not t:
        return send(chat, "No encuentro esa moneda en Binance.")
    if sum(1 for a in state["alerts"] if a["chat"] == chat) >= 10:
        return send(chat, "Máximo 10 alertas. Borra alguna con /borrar número.")
    d = "up" if target > t["price"] else "down"
    state["alerts"].append({"id": state["next_id"], "chat": chat, "sym": sym, "price": target, "dir": d})
    send(chat, f"🔔 Alerta #{state['next_id']} lista: te aviso cuando {t['base']} "
               f"{'suba hasta' if d == 'up' else 'baje hasta'} ${fp(target)} (ahora ${fp(t['price'])}).")
    state["next_id"] += 1


def cmd_alertas(state, chat, args):
    mine = [a for a in state["alerts"] if a["chat"] == chat]
    if not mine:
        return send(chat, "No tienes alertas. Crea una: /alerta BTC 70000")
    send(chat, "🔔 <b>Tus alertas</b>\n" + "\n".join(
        f"#{a['id']} {a['sym'][:-4]} {'≥' if a['dir'] == 'up' else '≤'} ${fp(a['price'])}" for a in mine)
         + "\nBorrar: /borrar número")


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
    send(chat, "✅ Avisos activados. Te escribiré cuando una moneda grande se mueva ±5% en una hora "
               "o aparezca una memecoin que pase los filtros. Para apagarlos: /silenciar")


def cmd_silenciar(state, chat, args):
    if chat in state["subs"]:
        state["subs"].remove(chat)
    send(chat, "🔕 Avisos apagados. Puedes volver a activarlos con /suscribir")


COMMANDS = {"/start": cmd_start, "/ayuda": cmd_ayuda, "/help": cmd_ayuda, "/top": cmd_top,
            "/precio": cmd_precio, "/grafico": cmd_grafico, "/analisis": cmd_analisis,
            "/comparar": cmd_comparar, "/mercado": cmd_mercado, "/memes": cmd_memes,
            "/alerta": cmd_alerta, "/alertas": cmd_alertas, "/borrar": cmd_borrar,
            "/suscribir": cmd_suscribir, "/silenciar": cmd_silenciar}

_hits = {}


def handle(state, chat, text):
    parts = text.strip().split()
    if not parts:
        return
    now = time.time()
    _hits[chat] = [t for t in _hits.get(chat, []) if now - t < 60] + [now]
    if len(_hits[chat]) > 15:
        return
    cmd = parts[0].lower().split("@")[0]
    fn = COMMANDS.get(cmd)
    if not fn:
        if cmd.startswith("/"):
            send(chat, "No conozco ese comando. Mira /ayuda", MENU)
        return
    try:
        fn(state, chat, parts[1:])
    except Exception as e:
        print("Error en", cmd, e)
        send(chat, "Ups, algo falló. Intenta de nuevo en un momento.")


# ------------------------- tareas automaticas -------------------------
def task_alerts(state):
    if not state["alerts"]:
        return
    d = get(f"{DATA}/api/v3/ticker/price")
    if not d:
        return
    prices = {x["symbol"]: float(x["price"]) for x in d}
    keep = []
    for a in state["alerts"]:
        p = prices.get(a["sym"])
        hit = p is not None and ((a["dir"] == "up" and p >= a["price"]) or (a["dir"] == "down" and p <= a["price"]))
        if hit:
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
        if now - s["t"] >= 2700:
            ref = s
    if ref and state["subs"]:
        mins = int((now - ref["t"]) / 60)
        found = []
        for x in mk:
            old = ref["p"].get(x["sym"])
            if old:
                ch = (x["price"] / old - 1) * 100
                if abs(ch) >= MOVER_PCT:
                    found.append((ch, x))
        found.sort(key=lambda z: abs(z[0]), reverse=True)
        lines = []
        for ch, x in found[:5]:
            if cooled(state, f"mv:{x['sym']}:{'u' if ch > 0 else 'd'}", 3):
                lines.append(f"{'🚀' if ch > 0 else '💥'} <b>{x['base']}</b> ${fp(x['price'])} "
                             f"{pc(ch)} en ~{mins} min · vol 24 h ${fm(x['qv'])}")
        if lines:
            broadcast(state, "⚡ <b>Movimientos fuertes</b>\n" + "\n".join(lines) +
                      "\n\nVer gráfico: /grafico MONEDA. " + DISCLAIMER)
    if not snaps or now - snaps[-1]["t"] >= 900:
        top = sorted(mk, key=lambda x: x["qv"], reverse=True)[:200]
        snaps.append({"t": now, "p": {x["sym"]: x["price"] for x in top}})
        state["snaps"] = snaps[-6:]


def task_memes(state):
    if not state["subs"]:
        return
    sent = 0
    for p, flags, age_h in meme_scan():
        b = p.get("baseToken") or {}
        if sent < 3 and cooled(state, f"meme:{p.get('chainId')}:{b.get('address')}", 24):
            broadcast(state, "🐸 <b>Memecoin con actividad</b>\n" + meme_text(p, flags, age_h) +
                      "\n\n🛡 Pasó los filtros básicos, pero eso NO la hace segura.",
                      [[btn("Ver en DexScreener", url=p.get("url", "https://dexscreener.com"))]])
            sent += 1


def run_tasks(state):
    now = time.time()
    for name, every, fn in (("alerts", 30, task_alerts), ("movers", 120, task_movers), ("memes", 300, task_memes)):
        if now - state["last"].get(name, 0) >= every:
            state["last"][name] = now
            try:
                fn(state)
            except Exception as e:
                print("Error en tarea", name, e)


# ------------------------- bucle principal -------------------------
def poll(state, timeout):
    try:
        r = requests.post(f"{TG}/getUpdates", json={"offset": state["offset"], "timeout": timeout,
                          "allowed_updates": ["message", "callback_query"]}, timeout=timeout + 15).json()
    except Exception as e:
        print("getUpdates error:", e)
        time.sleep(3)
        return
    for u in r.get("result", []):
        state["offset"] = u["update_id"] + 1
        msg = u.get("message")
        cq = u.get("callback_query")
        if msg and msg.get("text"):
            handle(state, msg["chat"]["id"], msg["text"])
        elif cq:
            tg("answerCallbackQuery", callback_query_id=cq["id"])
            data = cq.get("data", "")
            if data.startswith("cmd:") and cq.get("message"):
                handle(state, cq["message"]["chat"]["id"], data[4:])


def main():
    if not TOKEN:
        raise SystemExit("Falta el secreto TELEGRAM_TOKEN.")
    state = load_state()
    end = time.time() + RUN_SECONDS
    try:
        while time.time() < end:
            run_tasks(state)
            poll(state, max(1, min(20, int(end - time.time()))))
    finally:
        save_state(state)


if __name__ == "__main__":
    main()
