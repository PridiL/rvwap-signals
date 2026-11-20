"""Rolling VWAP Signals - cloud build, runs every hour on GitHub Actions.

Publishes https://pridil.github.io/rvwap-signals/ with two tabs:

  Hourly   every symbol's last closed 1H price against its Daily VWAP and its 1H Rolling
           VWAP, plus the 1H closes that crossed the 1H RVWAP this hour
           (cross up = LONG, cross down = SHORT).
  Record   recommendations.json / .csv: day by day (Bangkok date), every 1H cross of every pair
           (repeats included), with the distance from the cross rate to the current rate. Kept forever.
           recommendations_4h.json / .csv: the same for 4H crosses (own tab).
           recommendations_1d.json / .csv: daily candles crossing the Daily RVWAP at the US close
           (17:00 New York), dated by the US trading day (own tab).
  Slope    every symbol's 1H, 4H and Daily RVWAP slope on the last closed candle (RVWAP now minus one
           candle earlier: positive / negative), how long it has kept that sign (slopes.json too).
  4-hour   the original rule: the 4H close crossing the 4H Rolling VWAP.

VWAPs are TradingView's own, as saved in the Pridi chart template:
  * Rolling VWAP (RVWAP): hlc3, tick-volume weighted, automatic period = 1 day on a 1H chart
    and 3 days on a 4H chart, never fewer than 10 bars.
  * Daily VWAP: TradingView's VWAP with anchor "Session", seen on a 1H chart: hlc3 x tick
    volume from the open of the current daily bar (17:00 New York for FX) to the last closed
    1H bar.
A feed without volume (FOREXCOM:EU50) falls back to equal weights; TradingView itself would
draw nothing there.

Every cross is logged once and scored later (1H: after 4 / 12 / 24 bars; 4H: after 6 / 18 /
30 bars). The logs live on the published site (signals_1h.json, signals_4h.json) and are read
back at the start of each run: 404 -> start from seed/, any other error -> abort, so a network
blip can never wipe the history. Crosses on bars a skipped run missed are back-filled (up to
48 bars), so the log does not depend on every hourly run happening.

    python build.py                       fetch bars, build site/
    python build.py --bars bars.json      reuse a bars file (local testing)
    python build.py --out DIR             write the site somewhere else
"""
from __future__ import annotations

import html
import json
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path
from zoneinfo import ZoneInfo

ROOT = Path(__file__).resolve().parent
SITE = "https://pridil.github.io/rvwap-signals/"
DESK = "https://pridil.github.io/ai-trade-desk/"
UTC = timezone.utc
BKK = ZoneInfo("Asia/Bangkok")
NY = ZoneInfo("America/New_York")

# ---------------------------------------------------------------- universe
# "Pridi Forex" TradingView watchlist: the 28 OANDA pairs and one CFD per index
# (same list as the AI Trade Desk).
FX = ["EURUSD", "GBPUSD", "USDJPY", "USDCHF", "USDCAD", "AUDUSD", "NZDUSD",
      "EURGBP", "EURJPY", "EURCHF", "EURCAD", "EURAUD", "EURNZD",
      "GBPJPY", "GBPCHF", "GBPCAD", "GBPAUD", "GBPNZD",
      "AUDJPY", "AUDCHF", "AUDCAD", "AUDNZD",
      "NZDJPY", "NZDCHF", "NZDCAD", "CADJPY", "CADCHF", "CHFJPY"]
INDICES = {
    "US500": "CAPITALCOM:SPX500", "US100": "OANDA:NAS100USD", "US30": "OANDA:US30USD",
    "GER40": "OANDA:DE30EUR", "EU50": "FOREXCOM:EU50", "UK100": "OANDA:UK100GBP",
    "JP225": "OANDA:JP225USD", "HK50": "CAPITALCOM:HK50", "CN50": "OANDA:CN50USD",
}
TV = {**{p: "OANDA:" + p for p in FX}, **INDICES}
CLOCK = "EURUSD"          # its last closed bar defines "this hour" / "this 4H bar"
FETCH = "240:450,60:500,1D:300"

TF = {
    "1H": {"res": "60", "secs": 3600, "window": 86400,
           "horizons": {"4h": 4, "12h": 12, "24h": 24}, "keep": 3000},
    "4H": {"res": "240", "secs": 4 * 3600, "window": 3 * 86400,
           "horizons": {"1d": 6, "3d": 18, "5d": 30}, "keep": 600},
    # daily candle = one US trading day, closing 17:00 New York (all 37 feeds); RVWAP auto period 30.4375 days
    "1D": {"res": "1D", "secs": 86400, "window": 30.4375 * 86400,
           "horizons": {"1d": 1, "3d": 3, "5d": 5}, "keep": 600},
}
MIN_BARS = 10        # the 'Bars' input of the template's RVWAP
BACKFILL = 48        # bars back to look for crosses a skipped run missed
REC_FILE = "recommendations.json"   # day-by-day record of every 1H cross, by Bangkok day
REC_FILE_4H = "recommendations_4h.json"   # the same for 4H crosses
REC_FILE_1D = "recommendations_1d.json"   # the same for daily crosses at the US close (New York date)
DAILY_START = "2026-11-02"   # first US trading day the daily record back-fills to


def pip_size(sym):
    return 1.0 if sym in INDICES else 0.01 if sym.endswith("JPY") else 0.0001


def decimals(sym):
    return 1 if sym in INDICES else 3 if sym.endswith("JPY") else 5


def unit(sym):
    return "pts" if sym in INDICES else "pips"


def utc_str(ts):
    return datetime.fromtimestamp(ts, UTC).strftime("%Y-%m-%d %H:%M")


def bkk_str(ts, year=True):
    return datetime.fromtimestamp(ts, BKK).strftime("%a %d %b %Y %H:%M" if year else "%a %d %b %H:%M")


def ny_close(open_ts):
    """Close of the daily candle that opened at open_ts: the next 17:00 New York after the open."""
    o = datetime.fromtimestamp(open_ts, NY)
    c = datetime(o.year, o.month, o.day, 17, tzinfo=NY)
    if c <= o:
        d = o.date() + timedelta(days=1)
        c = datetime(d.year, d.month, d.day, 17, tzinfo=NY)
    return c.timestamp()


def parse_utc(s):
    return datetime.strptime(s, "%Y-%m-%d %H:%M").replace(tzinfo=UTC).timestamp()


# ---------------------------------------------------------------- maths
def sma(xs, n):
    out, s = [None] * len(xs), 0.0
    for i, x in enumerate(xs):
        s += x
        if i >= n:
            s -= xs[i - n]
        if i >= n - 1:
            out[i] = s / n
    return out


def atr(h, l, c, n=14):   # Wilder RMA, as TradingView
    tr = [h[0] - l[0]] + [max(h[i] - l[i], abs(h[i] - c[i - 1]), abs(l[i] - c[i - 1])) for i in range(1, len(c))]
    out = [None] * len(c)
    if len(c) < n:
        return out
    a = sum(tr[:n]) / n
    out[n - 1] = a
    for i in range(n, len(c)):
        a = (a * (n - 1) + tr[i]) / n
        out[i] = a
    return out


def rvwap_series(bars, window, min_bars=MIN_BARS):
    """TradingView 'Rolling VWAP': sum over bars whose open time lies within `window` seconds of
    the current bar's, never fewer than `min_bars` bars. Verified equal to TradingView on 4H."""
    t = [b[0] for b in bars]
    vols = [b[5] or 0 for b in bars]
    use_vol = sum(vols) > 0
    w = vols if use_vol else [1.0] * len(bars)
    pv, vv = [0.0], [0.0]
    for b, x in zip(bars, w):
        pv.append(pv[-1] + (b[2] + b[3] + b[4]) / 3 * x)
        vv.append(vv[-1] + x)
    out, j = [], 0
    for i in range(len(bars)):
        while t[i] - t[j] >= window:
            j += 1
        s = min(j, max(0, i - min_bars + 1))
        vol = vv[i + 1] - vv[s]
        out.append((pv[i + 1] - pv[s]) / vol if vol > 0 else None)
    return out, use_vol


class Series:
    """One symbol on one timeframe (closed bars only): RVWAP, ATR, SMA200 and every close cross."""

    def __init__(self, sym, bars, tf):
        self.sym, self.bars, self.tf = sym, bars, tf
        cfg = TF[tf]
        self.secs, self.horizons = cfg["secs"], cfg["horizons"]
        self.c = c = [b[4] for b in bars]
        self.h = [b[2] for b in bars]
        self.l = [b[3] for b in bars]
        self.rv, self.use_vol = rvwap_series(bars, cfg["window"])
        self.a = atr(self.h, self.l, c)
        self.s200 = sma(c, 200)
        rv, n = self.rv, len(c)
        ok = [j > 0 and rv[j] is not None and rv[j - 1] is not None for j in range(n)]
        self.ups = [j for j in range(1, n) if ok[j] and c[j - 1] <= rv[j - 1] and c[j] > rv[j]]
        self.dns = [j for j in range(1, n) if ok[j] and c[j - 1] >= rv[j - 1] and c[j] < rv[j]]
        self._up, self._dn = set(self.ups), set(self.dns)
        self.dp, self.pip, self.unit = decimals(sym), pip_size(sym), unit(sym)
        self.last = n - 1

    def close_ts(self, i=None):
        o = self.bars[self.last if i is None else i][0]
        return ny_close(o) if self.tf == "1D" else o + self.secs

    def cross_at(self, i):
        return "LONG" if i in self._up else "SHORT" if i in self._dn else None

    def state(self, i=None):
        i = self.last if i is None else i
        c, rv, A = self.c[i], self.rv[i], self.a[i]
        recent = sum(1 for j in self.ups + self.dns if i - 30 < j <= i)
        s2 = self.s200[i]
        return {
            "close": c, "rvwap": rv, "atr": A,
            "dist_atr": (c - rv) / A if rv is not None and A else None,
            "dist_native": (c - rv) / self.pip if rv is not None else None,
            "side": "n/a" if rv is None else "above" if c > rv else "below",
            "slope": (rv - self.rv[i - 3]) / A if rv is not None and i >= 3 and self.rv[i - 3] is not None and A else None,
            "whips": recent,
            "vs_sma200": None if s2 is None else "above" if c > s2 else "below",
        }

    def since(self, idx):
        return (self.last - idx[-1]) if idx else None

    def run_len(self):
        side = lambda j: None if self.rv[j] is None else self.c[j] > self.rv[j]
        k, s0 = 0, side(self.last)
        for j in range(self.last, -1, -1):
            if side(j) != s0:
                break
            k += 1
        return k

    def stop_ref(self, i, sgn):
        """Far side of RVWAP and of the signal bar, a little beyond; never inside 0.7 x ATR."""
        A, c, rv = self.a[i], self.c[i], self.rv[i]
        if sgn > 0:
            s = min(min(self.l[i], rv) - 0.1 * A, c - 0.7 * A)
        else:
            s = max(max(self.h[i], rv) + 0.1 * A, c + 0.7 * A)
        return round(s, self.dp)

    def history(self, direction):
        """Past crosses on this symbol (the current bar's excluded): close k bars later vs the
        cross close, in the cross direction, in ATR at the cross."""
        sgn = 1 if direction == "LONG" else -1
        idx = [j for j in (self.ups if sgn > 0 else self.dns) if j != self.last]
        res = {}
        for h, k in self.horizons.items():
            xs = [sgn * (self.c[j + k] - self.c[j]) / self.a[j] for j in idx if j + k <= self.last and self.a[j]]
            if xs:
                res[h] = {"n": len(xs), "wins": sum(1 for x in xs if x > 0), "sum": sum(xs)}
        return res


def grade(st, sgn):
    """A = clean cross with the trend and little chop; B = acceptable; C = hair-thin / whipsaw."""
    d = abs(st["dist_atr"] or 0)
    if d < 0.15 or st["whips"] >= 6:
        return "C"
    pts = sum([
        (st["slope"] or 0) * sgn >= 0,                               # RVWAP already sloping the cross's way
        st["vs_sma200"] == ("above" if sgn > 0 else "below"),        # with the SMA200 trend
        st["whips"] <= 2,                                            # a real regime change, not chop
        0.3 <= d <= 2.0,                                             # clean, not stretched
    ])
    return "A" if pts == 4 else "B" if pts >= 2 else "C"


def daily_vwap(b1h, b1d):
    """Session VWAP on the 1H chart, anchored at the open of the daily bar holding the last 1H bar."""
    last_open = b1h[-1][0]
    starts = [d[0] for d in b1d if d[0] <= last_open]
    if starts:
        anchor = starts[-1]
    else:   # no daily bars: FX session open, 17:00 New York
        ny = datetime.fromtimestamp(last_open, NY)
        s = ny.replace(hour=17, minute=0, second=0, microsecond=0)
        anchor = (s if ny >= s else s - timedelta(days=1)).timestamp()
    seg = [b for b in b1h if b[0] >= anchor]
    vols = [b[5] or 0 for b in seg]
    w = vols if sum(vols) > 0 else [1.0] * len(seg)
    W = sum(w)
    if not seg or W <= 0:
        return None, anchor, 0
    return sum((b[2] + b[3] + b[4]) / 3 * x for b, x in zip(seg, w)) / W, anchor, len(seg)


# ---------------------------------------------------------------- data
def fetch(path):
    node = os.environ.get("NODE_EXE") or shutil.which("node") or r"C:\Program Files\nodejs\node.exe"
    p = subprocess.run([node, str(ROOT / "fetch_ohlcv_ws.mjs"), str(path), FETCH, *TV.values()],
                       capture_output=True, text=True, timeout=900)
    for line in p.stdout.splitlines():
        if "FAILED" in line or line.startswith("wrote"):
            print("fetch:", line)
    if p.returncode or not path.exists():
        raise SystemExit(f"FATAL: fetcher exit {p.returncode}: {p.stderr[-400:]}")
    return json.loads(path.read_text())


def load_state(name):
    """The signal log as published on the live site; seed/ when the site has none yet."""
    url = f"{SITE}{name}?v={int(time.time())}"
    err = None
    for _ in range(3):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers={"Cache-Control": "no-cache"}), timeout=30) as r:
                data = json.loads(r.read().decode("utf-8"))
            n = len(data["signals"]) if "signals" in data else sum(len(v) for v in data.get("days", {}).values())
            print(f"state {name}: {n} entries from the live site, through {data.get('through')}")
            return data
        except urllib.error.HTTPError as e:
            if e.code == 404:
                seed = ROOT / "seed" / name
                empty = {"through": None, "days": {}} if name in (REC_FILE, REC_FILE_4H, REC_FILE_1D) else {"through": None, "signals": []}
                data = json.loads(seed.read_text(encoding="utf-8")) if seed.exists() else empty
                print(f"state {name}: not on the site yet - starting from {'seed' if seed.exists() else 'empty'}")
                return data
            err = e
        except Exception as e:   # noqa: BLE001 - any other failure must stop the build
            err = e
        time.sleep(5)
    raise SystemExit(f"FATAL: could not read {name} from the live site ({err}); not building, so the log is not lost")


# ---------------------------------------------------------------- log + scoring
def update_log(state, series, tf, clock_close):
    keep = TF[tf]["keep"]
    through = parse_utc(state["through"]) if state.get("through") else None
    have = {(x["bar_close_utc"], x["symbol"]) for x in state["signals"]}
    added = []
    for sym, s in series.items():
        for i in range(max(1, s.last - BACKFILL + 1), s.last + 1):
            ct = s.close_ts(i)
            if ct > clock_close or (through is None and ct != clock_close) or (through is not None and ct <= through):
                continue
            d = s.cross_at(i)
            if not d or (utc_str(ct), sym) in have:
                continue
            sgn = 1 if d == "LONG" else -1
            st = s.state(i)
            x = {"bar_close_utc": utc_str(ct), "bar_close_bkk": bkk_str(ct), "symbol": sym, "direction": d,
                 "grade": grade(st, sgn), "entry": s.c[i], "rvwap": round(st["rvwap"], s.dp),
                 "atr": round(st["atr"], s.dp + 1), "stop": s.stop_ref(i, sgn), "decimals": s.dp, "pip": s.pip,
                 "unit": s.unit, "dist_atr": round(st["dist_atr"], 2), "outcomes": {}}
            state["signals"].append(x)
            added.append(x)
    for x in state["signals"]:
        s = series.get(x["symbol"])
        if s:
            score(x, s)
    state["signals"] = sorted(state["signals"], key=lambda x: (x["bar_close_utc"], x["symbol"]))[-keep:]
    if through is None or clock_close > through:
        state["through"] = utc_str(clock_close)
    return added


def score(x, s):
    t0 = parse_utc(x["bar_close_utc"])
    if s.bars[0][0] > t0:
        return   # the entry bar has left the fetched window; keep what was scored before
    after = [b for b in s.bars if b[0] >= t0]
    sgn = 1 if x["direction"] == "LONG" else -1
    for h, n in s.horizons.items():
        if x["outcomes"].get(h, {}).get("final"):
            continue
        seg = after[:n]
        if not seg:
            continue
        hit = any((b[3] <= x["stop"]) if sgn > 0 else (b[2] >= x["stop"]) for b in seg)
        move = (seg[-1][4] - x["entry"]) * sgn
        x["outcomes"][h] = {"final": len(seg) >= n, "bars": len(seg), "atr": round(move / x["atr"], 2),
                            "native": round(move / x["pip"], 1), "stop_hit": hit}


def update_recs(rec, series, clock_close, tz=BKK, start_default=None):
    """Recommendation record: EVERY close crossing the RVWAP, under its Bangkok date, repeats included
    (a pair crossing back the same day is recorded again). Each run re-scans the last BACKFILL bars and
    adds any cross not yet in the record, so skipped runs fill in. Never trimmed."""
    if not rec.get("start"):   # the record's first day, 00:00 Bangkok; nothing earlier is added
        first = min(rec.get("days") or {}, default=None)
        d0 = (datetime.strptime(first or start_default, "%Y-%m-%d").replace(tzinfo=tz) if first or start_default else
              datetime.fromtimestamp(clock_close, tz).replace(hour=0, minute=0, second=0, microsecond=0))
        rec["start"] = d0.strftime("%Y-%m-%d")
    start = datetime.strptime(rec["start"], "%Y-%m-%d").replace(tzinfo=tz).timestamp()
    days = rec.setdefault("days", {})
    have = {(x["symbol"], x["bar_close_utc"]) for lst in days.values() for x in lst}
    found = []
    for sym, s in series.items():
        for i in range(max(1, s.last - BACKFILL + 1), s.last + 1):
            ct = s.close_ts(i)
            d = s.cross_at(i)
            if d and start < ct <= clock_close and (sym, utc_str(ct)) not in have:
                found.append((ct, sym, i, d))
    added = []
    for ct, sym, i, d in sorted(found):
        day = datetime.fromtimestamp(ct, tz).strftime("%Y-%m-%d")
        lst = days.setdefault(day, [])
        s = series[sym]
        st = s.state(i)
        x = {"date": day, "time_bkk": datetime.fromtimestamp(ct, BKK).strftime("%H:%M"), "bar_close_utc": utc_str(ct),
             "symbol": sym, "direction": d, "cross_rate": s.c[i], "rvwap": round(st["rvwap"], s.dp),
             "atr": round(st["atr"], s.dp + 1), "grade": grade(st, 1 if d == "LONG" else -1),
             "decimals": s.dp, "pip": s.pip, "unit": s.unit}
        lst.append(x)
        added.append(x)
    rec["days"] = dict(sorted(days.items()))
    if rec.get("through") is None or clock_close > parse_utc(rec["through"]):
        rec["through"] = utc_str(clock_close)
    return added


def rec_distance(x, series):
    s = series.get(x["symbol"])
    if not s:
        return None, None, None
    sgn = 1 if x["direction"] == "LONG" else -1
    cur = s.c[-1]
    move = (cur - x["cross_rate"]) * sgn
    return cur, move / x["pip"], (move / x["atr"] if x["atr"] else None)


def rec_csv(rec, series):
    lines = ["date,time_bkk,pair,direction,cross_rate,current_rate,distance,unit,distance_atr,grade"]
    for day in sorted(rec["days"]):   # chronological: earliest signal first
        for x in sorted(rec["days"][day], key=lambda x: (x["time_bkk"], x["symbol"])):
            cur, nat, a = rec_distance(x, series)
            dp = x["decimals"]
            lines.append(",".join([day, x["time_bkk"], x["symbol"], x["direction"], f"{x['cross_rate']:.{dp}f}",
                                   "" if cur is None else f"{cur:.{dp}f}", "" if nat is None else f"{nat:+.1f}",
                                   x["unit"], "" if a is None else f"{a:+.2f}", x["grade"]]))
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- render helpers
def esc(s):
    return html.escape(str(s if s is not None else ""), quote=True)


def fmt(x, dp):
    return f"{x:.{dp}f}" if isinstance(x, (int, float)) else "–"


def sgn_fmt(x, dp=2, cls=True):
    if x is None:
        return "<td class='mut'>–</td>"
    c = " class='above'" if cls and x > 0 else " class='below'" if cls and x < 0 else ""
    return f"<td{c}>{x:+.{dp}f}</td>"


def bars_ago(n):
    return "this bar" if n == 0 else f"{n} bar{'s' if n != 1 else ''} ago"


def hist_cell(h):
    if not h:
        return '<span class="mut">no past crosses</span>'
    return " · ".join(f"{k} {round(100 * v['wins'] / v['n'])}%/{v['sum'] / v['n']:+.2f}" for k, v in h.items())


def pooled(series_map, tf):
    pool = {}
    for s in series_map.values():
        for d in ("LONG", "SHORT"):
            for h, v in s.history(d).items():
                a = pool.setdefault((d, h), [0, 0, 0.0])
                a[0] += v["n"]; a[1] += v["wins"]; a[2] += v["sum"]
    tiles = []
    for d, lbl in (("LONG", "Cross up → long"), ("SHORT", "Cross down → short")):
        for h in TF[tf]["horizons"]:
            a = pool.get((d, h))
            if a and a[0]:
                tiles.append(f'<div class="stat"><b>{100 * a[1] / a[0]:.0f}% · {a[2] / a[0]:+.2f} ATR</b>'
                             f'<span>{lbl}, {h} hold (n={a[0]})</span></div>')
    return f'<div class="stats">{"".join(tiles)}</div>'


def record(state, tf, since):
    hz = TF[tf]["horizons"]
    log = state["signals"]
    tiles = []
    for h in hz:
        lst = [x["outcomes"][h] for x in log if x["outcomes"].get(h, {}).get("final")]
        if lst:
            w = sum(1 for o in lst if o["atr"] > 0)
            tiles.append(f'<div class="stat"><b>{100 * w / len(lst):.0f}% · {sum(o["atr"] for o in lst) / len(lst):+.2f} ATR</b>'
                         f'<span>{h} hold: win rate · avg ({len(lst)} closed)</span></div>')
        else:
            tiles.append(f'<div class="stat"><b>–</b><span>{h} hold: no closed signals yet</span></div>')
    rows = []
    for x in sorted(log, key=lambda x: (x["bar_close_utc"], x["symbol"]), reverse=True)[:150]:
        cells = []
        for h in hz:
            o = x["outcomes"].get(h)
            if not o:
                cells.append('<td class="mut">–</td>')
                continue
            cls = "pos" if o["atr"] > 0 else "neg" if o["atr"] < 0 else "mut"
            cells.append(f'<td class="{cls}">{o["native"]:+} {x["unit"]} ({o["atr"]:+}A){"" if o["final"] else " …"}'
                         f'{" <span class=mut>S</span>" if o["stop_hit"] else ""}</td>')
        dp = x["decimals"]
        rows.append(f"<tr><td class='l'>{esc(x['bar_close_bkk'])}</td><td class='l'><b>{esc(x['symbol'])}</b></td>"
                    f"<td class='l'><span class='dir {x['direction']}'>{x['direction']}</span> <span class='grade g{x['grade']}'>{x['grade']}</span></td>"
                    f"<td>{x['entry']:.{dp}f}</td><td>{x['stop']:.{dp}f}</td>{''.join(cells)}</tr>")
    body = "".join(rows) or f'<tr><td colspan="{5 + len(hz)}" class="l mut">No signals logged yet.</td></tr>'
    heads = "".join(f"<th>{h}</th>" for h in hz)
    bars_txt = " / ".join(str(n) for n in hz.values())
    return (f'<div class="stats">{"".join(tiles)}</div><div class="hist box"><table><thead><tr><th class="l">Bar close (BKK)</th>'
            f'<th class="l">Symbol</th><th class="l">Signal</th><th>Entry (close)</th><th>Stop ref</th>{heads}'
            f'</tr></thead><tbody>{body}</tbody></table></div>'
            f'<p class="small mut">Result = close {bars_txt} {tf} bars after the signal vs the signal close, in the signal direction; '
            f'A = multiples of the {tf} ATR at entry. S = the stop ref was touched inside that window. "…" = still open. '
            f'Logged from {since}. Showing the latest 150.</p>')


def by_candle(series_map, tf, clock, n):
    """Every RVWAP cross on each of the last `n` closed candles, all symbols, nothing filtered.
    Worked out from the bars themselves, so an hour the cloud run skipped still shows up."""
    secs = TF[tf]["secs"]
    lo = clock - n * secs
    rows = {}
    for sym, s in series_map.items():
        for i in range(max(1, s.last - n - 2), s.last + 1):
            ct = s.close_ts(i)
            if not lo < ct <= clock:
                continue
            slot = rows.setdefault(ct, {"LONG": [], "SHORT": [], "bars": 0})
            slot["bars"] += 1
            d = s.cross_at(i)
            if d:
                st = s.state(i)
                slot[d].append((sym, grade(st, 1 if d == "LONG" else -1), st, s.dp))
    out = []
    for ct in sorted(rows, reverse=True):
        slot = rows[ct]
        if slot["bars"] < 3 and not (slot["LONG"] or slot["SHORT"]):
            continue   # market shut, not a real candle for the board

        def chips(lst, d):
            if not lst:
                return '<span class="mut">–</span>'
            return "".join(
                f"<span class='chip {d}' title='close {fmt(st['close'], dp)} · RVWAP {fmt(st['rvwap'], dp)} · "
                f"{(st['dist_atr'] or 0):+.2f} ATR · grade {g}'>{esc(sym)}<i>{g}</i></span>"
                for sym, g, st, dp in sorted(lst))
        cur = " class='now'" if ct == clock else ""
        n_all = len(slot["LONG"]) + len(slot["SHORT"])
        out.append(f"<tr{cur}><td class='l'>{bkk_str(ct, False)}</td><td>{n_all}</td>"
                   f"<td class='l wrapc'>{chips(slot['LONG'], 'LONG')}</td><td class='l wrapc'>{chips(slot['SHORT'], 'SHORT')}</td></tr>")
    head = ("<tr><th class='l'>Candle closed (BKK)</th><th>Crosses</th><th class='l'>Crossed up → LONG</th>"
            "<th class='l'>Crossed down → SHORT</th></tr>")
    return table(head, out, "No candles in this window.")


def table(head, rows, empty):
    if not rows:
        return f'<div class="box small">{empty}</div>'
    return f'<div class="hist box"><table><thead>{head}</thead><tbody>{"".join(rows)}</tbody></table></div>'


# ---------------------------------------------------------------- hourly tab
H1_HEAD = ("<tr><th class='l'>Symbol</th><th class='l'>Signal</th><th>Grade</th><th>Close</th><th>1H RVWAP</th>"
           "<th>vs 1H RVWAP (ATR)</th><th>Daily VWAP</th><th>vs Daily VWAP</th><th class='l'>4H RVWAP</th><th>Stop ref</th>"
           "<th class='l'>This symbol's past 1H crosses: win % / avg ATR</th></tr>")
BOARD_HEAD = ("<tr><th class='l'>Symbol</th><th>Close</th><th>Daily VWAP</th><th>vs Daily VWAP</th><th>(1H ATR)</th>"
              "<th>1H RVWAP</th><th>vs 1H RVWAP</th><th>(1H ATR)</th><th class='l'>Last 1H RVWAP cross</th>"
              "<th class='l'>4H RVWAP</th><th class='l'>Price is</th></tr>")


def hourly_tab(view, h1, h4, clock1, state1):
    syms = list(view)
    fresh = [s for s in syms if h1[s].close_ts() == clock1 and h1[s].cross_at(h1[s].last)]
    fresh.sort(key=lambda s: ("ABC".index(view[s]["grade"]), s))
    up = sum(1 for s in fresh if view[s]["signal"] == "LONG")

    fr = []
    for s in fresh:
        v, S = view[s], h1[s]
        sgn = 1 if v["signal"] == "LONG" else -1
        dv = v["dvwap"]
        fr.append(f"<tr><td class='l'><b>{esc(s)}</b>{v['eqw']}</td><td class='l'><span class='dir {v['signal']}'>{v['signal']}</span></td>"
                  f"<td><span class='grade g{v['grade']}'>{v['grade']}</span></td><td>{fmt(S.c[-1], S.dp)}</td>"
                  f"<td>{fmt(v['st']['rvwap'], S.dp)}</td>{sgn_fmt(v['st']['dist_atr'])}<td>{fmt(dv, S.dp)}</td>"
                  f"{sgn_fmt(v['d_native'], 1)}<td class='l {v['side4']}'>{esc(v['side4'])}</td>"
                  f"<td>{fmt(S.stop_ref(S.last, sgn), S.dp)}</td><td class='l'>{hist_cell(S.history(v['signal']))}</td></tr>")

    board = []
    order = sorted(syms, key=lambda s: -(view[s]["st"]["dist_atr"] or 0))
    for s in order:
        v, S = view[s], h1[s]
        stale = "" if S.close_ts() == clock1 else f" <span class='mut'>(last bar {datetime.fromtimestamp(S.close_ts(), BKK):%H:%M})</span>"
        lc = v["last_cross"]
        lc_txt = ("<span class='mut'>none in window</span>" if lc is None else
                  f"<span class='{'above' if lc[0] == 'up' else 'below'}'>{'↑ up' if lc[0] == 'up' else '↓ down'}</span> "
                  f"<span class='mut'>{bars_ago(lc[1])}</span>")
        board.append(f"<tr><td class='l'><b>{esc(s)}</b>{v['eqw']}{stale}</td><td>{fmt(S.c[-1], S.dp)}</td>"
                     f"<td>{fmt(v['dvwap'], S.dp)}</td>{sgn_fmt(v['d_native'], 1)}{sgn_fmt(v['d_atr'], 2, False)}"
                     f"<td>{fmt(v['st']['rvwap'], S.dp)}</td>{sgn_fmt(v['st']['dist_native'], 1)}{sgn_fmt(v['st']['dist_atr'], 2, False)}"
                     f"<td class='l'>{lc_txt}</td><td class='l {v['side4']}'>{esc(v['side4'])}</td>"
                     f"<td class='l {v['align_cls']}'>{v['align']}</td></tr>")

    n = len(syms)
    a_d = sum(1 for s in syms if (view[s]["d_native"] or 0) > 0)
    a_r = sum(1 for s in syms if view[s]["st"]["side"] == "above")
    both_up = sum(1 for s in syms if view[s]["align"] == "above both")
    both_dn = sum(1 for s in syms if view[s]["align"] == "below both")
    tiles = (f'<div class="stats"><div class="stat"><b>{a_d} / {n}</b><span>above their Daily VWAP</span></div>'
             f'<div class="stat"><b>{a_r} / {n}</b><span>above their 1H RVWAP</span></div>'
             f'<div class="stat"><b class="above">{both_up}</b><span>above both</span></div>'
             f'<div class="stat"><b class="below">{both_dn}</b><span>below both</span></div></div>')
    since = state1["signals"][0]["bar_close_bkk"].rsplit(" ", 1)[0] if state1["signals"] else "now"
    return f"""
<div class="headline">{len(fresh)} cross{'es' if len(fresh) != 1 else ''} of the 1H Rolling VWAP on the 1H candle that closed {datetime.fromtimestamp(clock1, BKK):%H:%M}: {up} up, {len(fresh) - up} down.</div>
<p class="rule">Price = the last closed 1-hour candle. <b>Daily VWAP</b> = TradingView&rsquo;s VWAP anchored to the session, on the 1H chart:
from the open of today&rsquo;s daily bar (17:00 New York for FX) to the last closed 1H candle. <b>1H RVWAP</b> = the Pridi template&rsquo;s
Rolling VWAP on the 1H chart (hlc3, automatic 1-day period, minimum 10 bars, tick-volume weighted). A 1H candle <b>closing</b> across
its 1H RVWAP = a cross: up (previous close at or below, this close above) = <b>LONG</b>, down = <b>SHORT</b>.
Grades and stop refs work as on the 4-hour tab, measured in 1H ATR. Distances are in pips (FX) or index points; + = price above.</p>
{tiles}
<section><h3>1H crosses this hour</h3>{table(H1_HEAD, fr, 'No 1H close crossed its 1H Rolling VWAP this hour.')}</section>
<section><h3>Every 1H candle, last 24 hours - all symbols that crossed</h3>{by_candle(h1, '1H', clock1, 24)}
<p class="small mut">Every cross is listed, whatever its grade - nothing is filtered out. The letter after each symbol is its grade (a label for your own screening);
hover a symbol for its close, RVWAP and distance. Built from the bars each hour, so it is complete even if an hourly run was skipped. Weekend hours are left out.</p></section>
<section><h3>Whole board - price against Daily VWAP and 1H RVWAP</h3>{table(BOARD_HEAD, board, 'No data.')}
<p class="small mut">Sorted by distance from the 1H RVWAP in 1H ATR. "Last bar" = that market has not printed a new 1H candle this hour (closed or on a break).</p></section>
<section><h3>History of the 1H rule (last ~500 1H bars per symbol, all symbols pooled)</h3>{pooled(h1, '1H')}
<p class="small mut">Close 4 / 12 / 24 bars after every past 1H cross, in the cross direction: win % · average move in 1H ATR. A hint, not proof.</p></section>
<section><h3>Track record of 1H signals shown on this page</h3>{record(state1, '1H', since)}</section>"""


# ---------------------------------------------------------------- slope tab
def slope_info(S):
    """Slope of the RVWAP on the last closed candle: RVWAP now minus RVWAP one candle earlier,
    plus how many candles in a row it has kept that sign."""
    rv, i = S.rv, S.last
    if i < 1 or rv[i] is None or rv[i - 1] is None:
        return None
    d = rv[i] - rv[i - 1]
    sg = (d > 0) - (d < 0)
    run = 0
    for j in range(i, 0, -1):
        if rv[j] is None or rv[j - 1] is None or ((rv[j] - rv[j - 1] > 0) - (rv[j] - rv[j - 1] < 0)) != sg:
            break
        run += 1
    A = S.a[i]
    return {"sign": sg, "native": d / S.pip, "atr": d / A if A else None, "run": run,
            "rvwap": rv[i], "unit": S.unit, "dp": S.dp, "close_ts": S.close_ts()}


def slope_cells(x, word):
    if x is None:
        return "<td class='mut'>–</td>" * 4
    cls, txt = ("above", "&#9650; Positive") if x["sign"] > 0 else ("below", "&#9660; Negative") if x["sign"] < 0 else ("mut", "Flat")
    return (f"<td class='l {cls}'><b>{txt}</b></td>{sgn_fmt(x['native'], 1)}{sgn_fmt(x['atr'], 3)}"
            f"<td>{x['run']} {word}{'s' if x['run'] != 1 else ''}</td>")


SLOPE_HEAD = ("<tr><th class='l'>Symbol</th><th class='l'>1H RVWAP slope</th><th>Change (pips/pts)</th><th>(1H ATR)</th><th>Same sign for</th>"
              "<th class='l'>4H RVWAP slope</th><th>Change (pips/pts)</th><th>(4H ATR)</th><th>Same sign for</th>"
              "<th class='l'>Daily RVWAP slope</th><th>Change (pips/pts)</th><th>(daily ATR)</th><th>Same sign for</th>"
              "<th class='l'>1H · 4H · Daily</th></tr>")


def slopes(h1, h4, hd):
    return {s: {"1H": slope_info(h1[s]) if s in h1 else None, "4H": slope_info(h4[s]) if s in h4 else None,
                "1D": slope_info(hd[s]) if s in hd else None}
            for s in TV if s in h1 or s in h4 or s in hd}


def slope_tab(sl, clock1, clock4, clockd):
    def both(v):
        sg = [(v[k] or {}).get("sign", 0) for k in ("1H", "4H", "1D")]
        return ("all positive", "above", 0) if all(x > 0 for x in sg) else ("all negative", "below", 2) if all(x < 0 for x in sg)             else ("mixed", "mixed", 1)
    rows = []
    for s in sorted(sl, key=lambda s: (both(sl[s])[2], s)):
        v = sl[s]
        txt, cls, _ = both(v)
        rows.append(f"<tr><td class='l'><b>{esc(s)}</b></td>{slope_cells(v['1H'], 'candle')}{slope_cells(v['4H'], 'candle')}{slope_cells(v['1D'], 'day')}"
                    f"<td class='l {cls}'>{txt}</td></tr>")
    n = len(sl)
    p1 = sum(1 for v in sl.values() if (v["1H"] or {}).get("sign", 0) > 0)
    p4 = sum(1 for v in sl.values() if (v["4H"] or {}).get("sign", 0) > 0)
    pd = sum(1 for v in sl.values() if (v["1D"] or {}).get("sign", 0) > 0)
    bu = sum(1 for v in sl.values() if both(v)[2] == 0)
    bd = sum(1 for v in sl.values() if both(v)[2] == 2)
    tiles = (f'<div class="stats"><div class="stat"><b>{p1} / {n}</b><span>1H RVWAP sloping up</span></div>'
             f'<div class="stat"><b>{p4} / {n}</b><span>4H RVWAP sloping up</span></div>'
             f'<div class="stat"><b>{pd} / {n}</b><span>Daily RVWAP sloping up</span></div>'
             f'<div class="stat"><b class="above">{bu}</b><span>all three positive</span></div>'
             f'<div class="stat"><b class="below">{bd}</b><span>all three negative</span></div></div>')
    dtxt = (datetime.fromtimestamp(clockd, NY).strftime("%a %d %b") + " (US close, " +
            datetime.fromtimestamp(clockd, BKK).strftime("%H:%M") + " Bangkok)") if clockd else "–"
    return f"""
<div class="headline">Slope of the Rolling VWAP - 1H candle closed {datetime.fromtimestamp(clock1, BKK):%H:%M} · 4H candle closed {bkk_str(clock4, False)} · daily candle closed {dtxt}</div>
<p class="rule"><b>Slope</b> = the Rolling VWAP on the last closed candle minus the Rolling VWAP one candle earlier: <b>Positive</b> = rising,
<b>Negative</b> = falling. 1H uses the template&rsquo;s 1H RVWAP (automatic 1-day period); 4H the 4H RVWAP (automatic 3-day period); Daily uses the Daily RVWAP (automatic 30.4375-day period),
both hlc3, tick-volume weighted, minimum 10 bars. The change is shown in pips (FX) or index points and as a share of that timeframe&rsquo;s ATR.
<b>Same sign for</b> = how many candles in a row the slope has had this sign. Recalculated automatically: the 1H columns change every hour, the 4H columns when a 4H candle closes,
the Daily columns when the daily candle closes at the US close (17:00 New York).</p>
{tiles}
{table(SLOPE_HEAD, rows, 'No data.')}
<p class="small mut">Sorted: all three positive first, then mixed, then all three negative.</p>"""


# ---------------------------------------------------------------- recommendation record tab
REC_HEAD = ("<tr><th class='l'>Time (BKK)</th><th class='l'>Pair</th><th class='l'>Signal</th><th>Grade</th><th>Cross rate</th>"
            "<th>Current rate</th><th>Distance</th><th>Distance (ATR)</th></tr>")
REC_DAYS_SHOWN = 60
DAILY_NOTE = ("The daily candle closes at the <b>US close, 17:00 New York</b> (05:00 Bangkok; 04:00 while the US is on summer time) "
              "and the date is the US trading day that closed. Daily RVWAP = the template&rsquo;s Rolling VWAP on the Daily chart "
              "(hlc3, automatic 30.4375-day period, minimum 10 bars, tick-volume weighted). ")


def rec_tab(rec, h1, clock1, tf="1H"):
    stem = {"1H": "recommendations", "4H": "recommendations_4h", "1D": "recommendations_1d"}[tf]
    cand = {"1H": "1-hour", "4H": "4-hour", "1D": "daily"}[tf]
    name = "Daily (US close)" if tf == "1D" else tf
    tfl = "Daily" if tf == "1D" else tf
    days = sorted(rec["days"], reverse=True)
    blocks = []
    for k, day in enumerate(days[:REC_DAYS_SHOWN]):
        lst = sorted(rec["days"][day], key=lambda x: (x["time_bkk"], x["symbol"]))   # earliest first
        rows, fav, tot = [], 0, 0
        for x in lst:
            cur, nat, a = rec_distance(x, h1)
            dp = x["decimals"]
            if nat is not None:
                tot += 1
                fav += nat > 0
            dist = "<td class='mut'>–</td>" if nat is None else \
                f"<td class='{'pos' if nat > 0 else 'neg' if nat < 0 else 'mut'}'>{nat:+.1f} {x['unit']}</td>"
            rows.append(f"<tr><td class='l'>{esc(x['time_bkk'])}</td><td class='l'><b>{esc(x['symbol'])}</b></td>"
                        f"<td class='l'><span class='dir {x['direction']}'>{x['direction']}</span></td>"
                        f"<td><span class='grade g{x['grade']}'>{x['grade']}</span></td><td>{x['cross_rate']:.{dp}f}</td>"
                        f"<td>{fmt(cur, dp)}</td>{dist}{sgn_fmt(a, 2)}</tr>")
        n_long = sum(1 for x in lst if x["direction"] == "LONG")
        title = datetime.strptime(day, "%Y-%m-%d").strftime("%a %d %b %Y")
        summ = (f"<b>{title}</b> <span class='mut'>· {len(lst)} recommendation{'s' if len(lst) != 1 else ''}: "
                f"{n_long} long, {len(lst) - n_long} short · {fav} of {tot} in profit now</span>")
        blocks.append(f"<details class='day'{' open' if k == 0 else ''}><summary>{summ}</summary>"
                      f"{table(REC_HEAD, rows, 'No crosses this day.')}</details>")
    body = "".join(blocks) or '<div class="box small">No recommendations recorded yet.</div>'
    older = (f'<p class="small mut">Showing the latest {REC_DAYS_SHOWN} days; older days are in the download.</p>'
             if len(days) > REC_DAYS_SHOWN else "")
    return f"""
<div class="headline">{name} recommendation record - {tfl} Rolling VWAP crosses, day by day</div>
<p class="rule">{DAILY_NOTE if tf == "1D" else ""}Every pair whose {cand} candle <b>closed</b> across its {tfl} Rolling VWAP is recorded with the date and the time the candle
closed (Bangkok): cross up = <b>LONG</b>, cross down = <b>SHORT</b>. <b>Every cross is recorded</b>, including a pair crossing back
again later the same day, so a pair can appear several times in a day{" (a daily candle can cross only once a day)" if tf == "1D" else ""}.
<b>Cross rate</b> = the close of the candle that crossed. <b>Distance</b> = current rate (the last closed 1H candle, {bkk_str(clock1, False)})
minus the cross rate, in the signal&rsquo;s direction: + = moving the recommended way, &minus; = against it. Pips for FX, points for indices;
ATR = the {tfl} ATR when the cross happened. Every cross is listed, whatever its grade. The record is kept permanently and updated every hour.</p>
<p class="small"><a href="{stem}.csv" download>Download the full {name} record (CSV)</a> · <a href="{stem}.json">raw data (JSON)</a></p>
{body}{older}"""


# ---------------------------------------------------------------- 4-hour tab
SIG_HEAD = ("<tr><th class='l'>Symbol</th><th class='l'>Signal</th><th>Grade</th><th>Close</th><th>RVWAP</th><th>Close vs RVWAP (ATR)</th>"
            "<th>RVWAP slope 3 bars (ATR)</th><th>Crosses last 30</th><th>vs SMA200</th><th>Stop ref</th>"
            "<th class='l'>This symbol's past crosses: win % / avg ATR</th></tr>")


def four_tab(h4, clock4, state4):
    def row(sym, fresh):
        S = h4[sym]
        st = S.state()
        if fresh:
            d, ago = S.cross_at(S.last), 0
        else:
            d = "LONG" if st["side"] == "above" else "SHORT"
            ago = S.since(S.ups if d == "LONG" else S.dns)
        sgn = 1 if d == "LONG" else -1
        g = grade(st, sgn)
        eqw = "" if S.use_vol else ' <span class="mut">equal-wt</span>'
        when = "" if fresh else f" <span class=mut>{bars_ago(ago)}</span>"
        return (g, f"<tr><td class='l'><b>{esc(sym)}</b>{eqw}</td><td class='l'><span class='dir {d}'>{d}</span>{when}</td>"
                f"<td><span class='grade g{g}'>{g}</span></td><td>{fmt(st['close'], S.dp)}</td><td>{fmt(st['rvwap'], S.dp)}</td>"
                f"{sgn_fmt(st['dist_atr'], 2, False)}{sgn_fmt(st['slope'], 2, False)}<td>{st['whips']}</td>"
                f"<td>{esc(st['vs_sma200'])}</td><td>{fmt(S.stop_ref(S.last, sgn), S.dp)}</td>"
                f"<td class='l'>{hist_cell(S.history(d))}</td></tr>")

    fresh = [s for s in h4 if h4[s].close_ts() == clock4 and h4[s].cross_at(h4[s].last)]
    live = []
    for s, S in h4.items():
        if s in fresh or S.rv[S.last] is None:
            continue
        side = S.state()["side"]
        k = S.since(S.ups if side == "above" else S.dns)
        if k is not None and 1 <= k <= 3:
            live.append(s)
    fr = sorted((row(s, True) for s in fresh), key=lambda gr: "ABC".index(gr[0]))
    lv = sorted((row(s, False) for s in live), key=lambda gr: "ABC".index(gr[0]))
    n_long = sum(1 for s in fresh if h4[s].cross_at(h4[s].last) == "LONG")

    board = []
    for s, S in sorted(h4.items(), key=lambda kv: -(kv[1].state()["dist_atr"] or 0)):
        st = S.state()
        if st["rvwap"] is None:
            continue
        last = min([x for x in (S.since(S.ups), S.since(S.dns)) if x is not None], default=None)
        board.append(f"<tr><td class='l'><b>{esc(s)}</b></td><td class='l {st['side']}'>{esc(st['side'])}</td>"
                     f"<td class='{st['side']}'>{(st['dist_atr'] or 0):+.2f}</td><td>{S.run_len()}</td>"
                     f"<td>{'–' if last is None else last}</td>{sgn_fmt(st['slope'], 2, False)}"
                     f"<td>{st['whips']}</td><td>{fmt(st['close'], S.dp)}</td><td>{fmt(st['rvwap'], S.dp)}</td></tr>")
    bhead = ("<tr><th class='l'>Symbol</th><th class='l'>Side</th><th>Close vs RVWAP (ATR)</th><th>Closes on this side</th>"
             "<th>Bars since last cross</th><th>Slope 3 bars (ATR)</th><th>Crosses last 30</th><th>Close</th><th>RVWAP</th></tr>")
    return f"""
<div class="headline">{len(fresh)} fresh cross{'es' if len(fresh) != 1 else ''} on the 4H candle that closed {bkk_str(clock4, False)}: {n_long} long, {len(fresh) - n_long} short.</div>
<p class="rule">Rule: the 4-hour candle <b>closes</b> across the Rolling VWAP. Cross up (previous close at or below its RVWAP, this close above) = <b>LONG</b>;
cross down = <b>SHORT</b>. RVWAP = the Pridi TradingView template&rsquo;s Rolling VWAP: hlc3, automatic 3-day period on the 4H chart, minimum 10 bars, tick-volume weighted.
Grade A = clean cross (0.3-2 ATR past RVWAP) with RVWAP sloping the same way, on the SMA200 trend side and little chop (&le;2 crosses in 30 bars);
C = hair-thin (&lt;0.15 ATR) or whipsawing (&ge;6 crosses). Stop ref = beyond RVWAP and the signal bar, at least 0.7 x ATR away.
This tab changes only when a new 4H candle closes.</p>
<section><h3>Fresh crosses on the last 4H candle</h3>{table(SIG_HEAD, [r for _, r in fr], 'No 4H close crossed its Rolling VWAP on this candle.')}</section>
<section><h3>Every 4H candle, last 5 days - all symbols that crossed</h3>{by_candle(h4, '4H', clock4, 30)}
<p class="small mut">Every cross is listed, whatever its grade - nothing is filtered out. The letter after each symbol is its grade; hover a symbol for its close,
RVWAP and distance. A few index feeds print a short 4H candle at their session open, so an odd time can appear with just those indices.</p></section>
<section><h3>Crossed 1-3 bars ago and still holding</h3>{table(SIG_HEAD, [r for _, r in lv], 'None.')}</section>
<section><h3>Whole board - where price sits against the 4H RVWAP</h3>{table(bhead, board, 'No data.')}</section>
<section><h3>History of this rule (last ~450 4H bars per symbol, all symbols pooled)</h3>{pooled(h4, '4H')}
<p class="small mut">Close 6 / 18 / 30 bars after every past cross, in the cross direction: win % · average move in 4H ATR at the cross. Small per-symbol samples (~30) - a hint, not proof.</p></section>
<section><h3>Track record of 4H signals shown on this page</h3>{record(state4, '4H', '19 Nov 2026')}</section>"""


# ---------------------------------------------------------------- page
CSS = """
:root{color-scheme:light;--bg:#f4f4f2;--card:#fff;--ink:#15181b;--ink2:#4d555d;--muted:#7d858d;--line:#e2e5e8;
--accent:#2a78d6;--long:#0f8a4f;--longbg:#e4f5ec;--short:#c4372f;--shortbg:#fbe8e6;--chip:#eef0f2}
@media (prefers-color-scheme:dark){:root:not([data-theme="light"]){color-scheme:dark;--bg:#0d0f11;--card:#15181b;--ink:#f2f4f6;
--ink2:#c2c8ce;--muted:#858d95;--line:#272c31;--accent:#4d94e8;--long:#3ddc97;--longbg:#10291d;--short:#ff6b6b;--shortbg:#2d1414;--chip:#1f2328}}
:root[data-theme="dark"]{color-scheme:dark;--bg:#0d0f11;--card:#15181b;--ink:#f2f4f6;--ink2:#c2c8ce;--muted:#858d95;--line:#272c31;
--accent:#4d94e8;--long:#3ddc97;--longbg:#10291d;--short:#ff6b6b;--shortbg:#2d1414;--chip:#1f2328}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--ink);font:400 14px/1.5 -apple-system,"Segoe UI",Roboto,system-ui,sans-serif}
.wrap{max-width:1240px;margin:0 auto;padding:18px 16px 48px}
header.top{display:flex;flex-wrap:wrap;gap:6px 18px;align-items:baseline;margin-bottom:14px}
h1{font-size:20px;margin:0;letter-spacing:-.2px}.meta{color:var(--muted);font-size:12.5px}
.headline{font-size:17px;font-weight:600;margin:6px 0 4px}
.dir{font-size:12px;font-weight:700;padding:2px 9px;border-radius:5px;letter-spacing:.4px}
.LONG{color:var(--long);background:var(--longbg)}.SHORT{color:var(--short);background:var(--shortbg)}
table{border-collapse:collapse;width:100%;font-variant-numeric:tabular-nums}
section{margin-top:26px}section>h3{font-size:15px;margin:0 0 10px}
.box{background:var(--card);border:1px solid var(--line);border-radius:10px;padding:12px 16px}
.small{font-size:12.5px;color:var(--ink2)}
.tabs{display:flex;flex-wrap:wrap;gap:6px;margin:4px 0 14px}
.tab{font:inherit;font-size:13.5px;padding:7px 14px;border-radius:7px;border:1px solid var(--line);background:transparent;color:var(--ink2);cursor:pointer}
.tab[aria-selected="true"]{background:var(--accent);border-color:var(--accent);color:#fff}
.pane[hidden]{display:none}
.hist{overflow-x:auto}.hist table td,.hist table th{padding:5px 7px;border-bottom:1px solid var(--line);font-size:12.5px;text-align:right;white-space:nowrap}
.hist table th{color:var(--muted);font-weight:500}.hist table td.l,.hist table th.l{text-align:left}
.pos{color:var(--long)}.neg{color:var(--short)}.mut{color:var(--muted)}
.stats{display:flex;flex-wrap:wrap;gap:10px;margin-bottom:10px}.stat{background:var(--card);border:1px solid var(--line);border-radius:8px;padding:8px 12px;min-width:150px}
.stat b{display:block;font-size:17px}.stat span{font-size:12px;color:var(--muted)}
.grade{display:inline-block;min-width:22px;text-align:center;font-weight:700;border-radius:5px;padding:1px 6px;font-size:12px}
.gA{background:var(--longbg);color:var(--long)}.gB{background:var(--chip);color:var(--accent)}.gC{background:var(--chip);color:var(--muted)}
.above{color:var(--long)}.below{color:var(--short)}.mixed{color:var(--muted)}
.rule{max-width:960px;color:var(--ink2);margin:0 0 16px}
.hist table td.wrapc{white-space:normal}
.chip{display:inline-block;font-size:12px;font-weight:600;padding:1px 7px;margin:2px 4px 2px 0;border-radius:5px;cursor:default}
.chip i{font-style:normal;font-weight:500;opacity:.65;margin-left:4px;font-size:11px}
.hist table tr.now td{background:var(--chip)}
details.day{margin:0 0 10px}details.day>summary{cursor:pointer;padding:8px 2px;font-size:14px}
details.day>.hist,details.day>.box{margin-top:4px}
.disc{margin-top:30px;color:var(--muted);font-size:12px}a{color:var(--accent)}
"""

JS = """
const tabs=[...document.querySelectorAll('.tab')];
function show(k){if(!document.getElementById('pane-'+k))k='h1';
 tabs.forEach(t=>t.setAttribute('aria-selected',String(t.dataset.k===k)));
 document.querySelectorAll('.pane').forEach(p=>p.hidden=p.id!=='pane-'+k);
 try{localStorage.setItem('rvwap-tab',k)}catch(e){}}
tabs.forEach(t=>t.addEventListener('click',()=>{show(t.dataset.k);history.replaceState(null,'','#'+t.dataset.k)}));
let k0=location.hash.slice(1);if(!k0){try{k0=localStorage.getItem('rvwap-tab')||''}catch(e){k0=''}}
show(k0||'h1');
"""


def render(view, h1, h4, clock1, clock4, state1, state4, rec, rec4, recd, missing, sl=None, clockd=None):
    miss = (f'<p class="small mut">No data this run for: {esc(", ".join(missing))}.</p>' if missing else "")
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Rolling VWAP Signals</title><style>{CSS}</style></head><body><div class="wrap">
<header class="top"><h1>Rolling VWAP Signals</h1>
<span class="meta">1H candle closed {bkk_str(clock1)} Bangkok · updates every hour · 28 FX pairs + 9 indices · <a href="{DESK}">AI Trade Desk →</a></span></header>
<div class="tabs" role="tablist">
<button class="tab" role="tab" data-k="h1" aria-selected="true">Hourly: Daily VWAP + 1H RVWAP</button>
<button class="tab" role="tab" data-k="slope" aria-selected="false">RVWAP slope: 1H, 4H, Daily</button>
<button class="tab" role="tab" data-k="rec" aria-selected="false">1H recommendation record</button>
<button class="tab" role="tab" data-k="rec4" aria-selected="false">4H recommendation record</button>
<button class="tab" role="tab" data-k="recd" aria-selected="false">Daily (US close) record</button>
<button class="tab" role="tab" data-k="h4" aria-selected="false">4-hour RVWAP crosses</button></div>
{miss}
<div class="pane" id="pane-h1">{hourly_tab(view, h1, h4, clock1, state1)}</div>
<div class="pane" id="pane-slope" hidden>{slope_tab(sl or {}, clock1, clock4, clockd)}</div>
<div class="pane" id="pane-rec" hidden>{rec_tab(rec, h1, clock1)}</div>
<div class="pane" id="pane-rec4" hidden>{rec_tab(rec4, h1, clock1, "4H")}</div>
<div class="pane" id="pane-recd" hidden>{rec_tab(recd, h1, clock1, "1D")}</div>
<div class="pane" id="pane-h4" hidden>{four_tab(h4, clock4, state4)}</div>
<p class="disc">Generated automatically every hour from TradingView prices. A mechanical signal, not a trade recommendation and not
financial advice. Levels can be wrong or stale; check the chart before acting.</p>
</div><script>{JS}</script></body></html>"""


PRIVACY = {
    "Windows user path": r"[A-Za-z]:[\\/]{1,2}Users", "username": r"\bUSER\b",
    "email address": r"[\w.+-]+@[\w-]+\.(?:com|net|org|io|co|th)\b", "Desktop path": r"Desktop[\\/]",
    "file link": r"file:/[/]", "AI vendor mention": r"(?i)\b(c[l]aude|a[n]thropic|o[p]enai)\b",   # bracketed so this file passes its own scan
    "secret-ish": r"(?i)(api[_-]?key|secret|token)\s*[:=]\s*['\"][^'\"]{8,}",
}


def privacy_scan(text):
    return [f"{k}: {sorted(set(re.findall(p, text)))[:3]}" for k, p in PRIVACY.items() if re.search(p, text)]


# ---------------------------------------------------------------- main
def main():
    argv = sys.argv[1:]
    opt = lambda k, d=None: argv[argv.index(k) + 1] if k in argv else d
    out = Path(opt("--out", str(ROOT / "site")))
    bars_path = Path(opt("--bars", str(ROOT / "bars.json")))
    raw = json.loads(bars_path.read_text()) if "--bars" in argv else fetch(bars_path)
    now = time.time()

    h1, h4, d1, hd, missing = {}, {}, {}, {}, []
    for sym, tv in TV.items():
        b1 = [b for b in raw.get("60", {}).get(tv, []) if b[0] + 3600 <= now]
        b4 = [b for b in raw.get("240", {}).get(tv, []) if b[0] + 4 * 3600 <= now]
        if len(b1) < 60 or len(b4) < 60:
            missing.append(sym)
            continue
        h1[sym], h4[sym] = Series(sym, b1, "1H"), Series(sym, b4, "4H")
        d1[sym] = raw.get("1D", {}).get(tv, [])
        bd = [b for b in d1[sym] if ny_close(b[0]) <= now]
        if len(bd) >= 60:
            hd[sym] = Series(sym, bd, "1D")
    if CLOCK not in h1 or len(missing) > 5:
        raise SystemExit(f"FATAL: missing series for {missing}")
    clock1, clock4 = h1[CLOCK].close_ts(), h4[CLOCK].close_ts()

    view = {}
    for sym, S in h1.items():
        st = S.state()
        dv, anchor, nb = daily_vwap(S.bars, d1[sym])
        sig = S.cross_at(S.last) if S.close_ts() == clock1 else None
        s4 = h4[sym].state()["side"]
        d_native = (S.c[-1] - dv) / S.pip if dv is not None else None
        d_atr = (S.c[-1] - dv) / st["atr"] if dv is not None and st["atr"] else None
        above_d, above_r = (d_native or 0) > 0, st["side"] == "above"
        align = "above both" if above_d and above_r else "below both" if not above_d and not above_r else "mixed"
        lu, ld = S.since(S.ups), S.since(S.dns)
        last_cross = None if lu is None and ld is None else ("up", lu) if ld is None or (lu is not None and lu < ld) else ("down", ld)
        view[sym] = {"st": st, "dvwap": dv, "anchor": anchor, "d_native": d_native, "d_atr": d_atr, "side4": s4,
                     "signal": sig, "grade": grade(st, 1 if sig == "LONG" else -1) if sig else None,
                     "align": align, "align_cls": "above" if align == "above both" else "below" if align == "below both" else "mixed",
                     "last_cross": last_cross, "eqw": "" if S.use_vol else ' <span class="mut">equal-wt</span>'}

    state1, state4 = load_state("signals_1h.json"), load_state("signals_4h.json")
    new1 = update_log(state1, h1, "1H", clock1)
    new4 = update_log(state4, h4, "4H", clock4)
    rec = load_state(REC_FILE)
    new_rec = update_recs(rec, h1, clock1)
    rec4 = load_state(REC_FILE_4H)
    new_rec4 = update_recs(rec4, h4, clock4)
    recd = load_state(REC_FILE_1D)
    clockd = max(S.close_ts() for S in hd.values()) if hd else None
    new_recd = update_recs(recd, hd, clockd, NY, DAILY_START) if hd else []
    sl = slopes(h1, h4, hd)
    print(f"1H candle {utc_str(clock1)} UTC, 4H candle {utc_str(clock4)} UTC; missing: {missing or 'none'}")
    print("new 1H crosses: " + (", ".join(f"{x['symbol']} {x['direction']} ({x['grade']}) @{x['bar_close_utc'][11:]}" for x in new1) or "none"))
    print("new 4H crosses: " + (", ".join(f"{x['symbol']} {x['direction']} ({x['grade']}) @{x['bar_close_utc'][11:]}" for x in new4) or "none"))

    print("new recommendations: " + (", ".join(f"{x['symbol']} {x['direction']} @{x['date']} {x['time_bkk']}" for x in new_rec) or "none"))
    print("new 4H recommendations: " + (", ".join(f"{x['symbol']} {x['direction']} @{x['date']} {x['time_bkk']}" for x in new_rec4) or "none"))
    print(f"daily: {len(hd)} symbols, last US close {utc_str(clockd) if clockd else '-'} UTC; new daily recommendations: "
          + (", ".join(f"{x['symbol']} {x['direction']} @{x['date']}" for x in new_recd) or "none"))

    page = render(view, h1, h4, clock1, clock4, state1, state4, rec, rec4, recd, missing, sl, clockd)
    latest = {"built_utc": utc_str(now), "bar_1h_close_utc": utc_str(clock1), "bar_4h_close_utc": utc_str(clock4),
              "signals_1h": [x for x in state1["signals"] if x["bar_close_utc"] == utc_str(clock1)],
              "signals_4h": [x for x in state4["signals"] if x["bar_close_utc"] == utc_str(clock4)],
              "board": {s: {"close": h1[s].c[-1], "daily_vwap": None if v["dvwap"] is None else round(v["dvwap"], h1[s].dp),
                            "rvwap_1h": None if v["st"]["rvwap"] is None else round(v["st"]["rvwap"], h1[s].dp),
                            "rvwap_4h_side": v["side4"], "price_is": v["align"]} for s, v in view.items()}}
    files = {"index.html": page, "latest.json": json.dumps(latest, indent=1),
             "signals_1h.json": json.dumps(state1, indent=0), "signals_4h.json": json.dumps(state4, indent=0),
             REC_FILE: json.dumps(rec, indent=0), "recommendations.csv": rec_csv(rec, h1),
             REC_FILE_4H: json.dumps(rec4, indent=0), "recommendations_4h.csv": rec_csv(rec4, h1),
             REC_FILE_1D: json.dumps(recd, indent=0), "recommendations_1d.csv": rec_csv(recd, h1),
             "slopes.json": json.dumps({s: {k: None if x is None else {"slope": "positive" if x["sign"] > 0 else "negative" if x["sign"] < 0 else "flat",
                                                              "change": round(x["native"], 2), "change_atr": None if x["atr"] is None else round(x["atr"], 4),
                                                              "same_sign_candles": x["run"], "candle_close_utc": utc_str(x["close_ts"])}
                                          for k, x in v.items()} for s, v in sl.items()}, indent=1),
             "stamp.txt": utc_str(clock1)}
    for name, text in files.items():
        problems = privacy_scan(text)
        if problems:
            raise SystemExit(f"FATAL: privacy scan flagged {name}:\n - " + "\n - ".join(problems))
    out.mkdir(parents=True, exist_ok=True)
    for name, text in files.items():
        (out / name).write_text(text, encoding="utf-8")
    (out / ".nojekyll").touch()
    print(f"built {out} (stamp {utc_str(clock1)})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
