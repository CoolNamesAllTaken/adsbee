"""HTML report from bench/validate.py results and bench/bench.py JSON files.

python bench/report.py VALDIR --bench a.json b.json ... --out report.html [--media DIR]
"""

import argparse
import base64
import glob
import html
import io
import json
import os
from collections import defaultdict

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402
import numpy as np  # noqa: E402

SERIES = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4", "#008300", "#4a3aa7", "#e34948"]
INK = "#0b0b0b"
INK2 = "#52514e"
GRID = "#e4e3df"
SURFACE = "#fcfcfb"

plt.rcParams.update({
    "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "axes.edgecolor": GRID, "axes.labelcolor": INK2,
    "xtick.color": INK2, "ytick.color": INK2, "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.8,
    "axes.spines.top": False, "axes.spines.right": False, "font.size": 10, "axes.titlesize": 11,
    "axes.titlecolor": INK, "legend.frameon": False, "lines.linewidth": 2,
})


def load(valdir):
    runs = {}
    for f in glob.glob(os.path.join(valdir, "*.json")):
        with open(f) as fh:
            d = json.load(fh)
        runs[d["spec"]["name"]] = d
    return runs


def arr(run, col, modes_only=False):
    rows = run["rows"]
    if modes_only:
        rows = [r for r in rows if not r[6]]
    return np.array([r[col] for r in rows], dtype=float)


def per_aircraft_rates(run, modes_only=False):
    by = defaultdict(list)
    for r in run["rows"]:
        if modes_only and r[6]:
            continue
        by[r[0]].append(r[1])
    out = []
    for ts in by.values():
        if len(ts) > 5 and max(ts) - min(ts) > 10:
            out.append((len(ts) - 1) / (max(ts) - min(ts)))
    return np.array(out)


class Figs:
    def __init__(self, media):
        self.media = media
        self.names = []

    def save(self, fig, name):
        buf = io.BytesIO()
        fig.savefig(buf, format="png", dpi=130, bbox_inches="tight")
        plt.close(fig)
        data = buf.getvalue()
        if self.media:
            os.makedirs(self.media, exist_ok=True)
            with open(os.path.join(self.media, name), "wb") as f:
                f.write(data)
        self.names.append(name)
        return f'<img alt="{html.escape(name)}" src="data:image/png;base64,{base64.b64encode(data).decode()}">'


def cdf(ax, x, label, color):
    x = np.sort(x)
    y = np.arange(1, len(x) + 1) / len(x)
    ax.plot(x, y * 100, label=label, color=color)


def table(headers, rows):
    h = "".join(f"<th>{html.escape(str(c))}</th>" for c in headers)
    b = "".join("<tr>" + "".join(f"<td>{c}</td>" for c in r) + "</tr>" for r in rows)
    return f"<table><thead><tr>{h}</tr></thead><tbody>{b}</tbody></table>"


def f0(x):
    return "-" if x is None or (isinstance(x, float) and not np.isfinite(x)) else f"{x:,.0f}"


def f1(x):
    return "-" if x is None or (isinstance(x, float) and not np.isfinite(x)) else f"{x:,.1f}"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("valdir")
    ap.add_argument("--bench", nargs="*", default=[])
    ap.add_argument("--out", required=True)
    ap.add_argument("--media")
    args = ap.parse_args()
    runs = load(args.valdir)
    figs = Figs(args.media)
    parts = []

    kinds = [("adsbee_1090", 48, "ADSBee 1090, 48 MHz"), ("adsbee_1090", 12, "ADSBee 1090, 12 MHz Beast"),
             ("rtlsdr", 12, "RTL-SDR + dump1090, 12 MHz")]
    sizes = [3, 4, 5, 6, 8]

    # Error CDF by array size.
    fig, axs = plt.subplots(1, 2, figsize=(10, 3.8))
    for k, n in enumerate(sizes):
        r = runs.get(f"size-adsbee_1090-48-{n}")
        if r:
            cdf(axs[0], arr(r, 2), f"{n} receivers", SERIES[k])
            cdf(axs[1], np.abs(arr(r, 3)), f"{n} receivers", SERIES[k])
    axs[0].set_xscale("log")
    axs[0].set_xlim(3, 20000)
    axs[0].set_xlabel("Horizontal error [m]")
    axs[0].set_ylabel("Fixes [%]")
    axs[0].set_title("Horizontal error, ADSBee 1090 at 48 MHz")
    axs[1].set_xlim(0, 30)
    axs[1].set_xlabel("Vertical error [m]")
    axs[1].set_title("Vertical error (barometric altitude in the fix)")
    axs[0].legend(loc="lower right")
    img_cdf = figs.save(fig, "error_cdf_by_size.png")

    # Median and 95th percentile vs receivers for three receiver types.
    fig, axs = plt.subplots(1, 2, figsize=(10, 3.8), sharey=False)
    size_rows = []
    for k, (kind, mhz, label) in enumerate(kinds):
        p50, p95, ns = [], [], []
        for n in sizes:
            r = runs.get(f"size-{kind}-{mhz}-{n}")
            if not r or not r["summary"].get("n"):
                continue
            s = r["summary"]
            ns.append(n)
            p50.append(s["h_p50"])
            p95.append(s["h_p95"])
            sm = r["summary_modes_only"]
            size_rows.append([label, n, f1(s["h_p50"]), f0(s["h_p95"]), f1(s["v_p95"]),
                              f1(sm.get("h_p50")), f1(s["rate_hz_median"]), f"{s['within_est_1sigma'] * 100:.0f} %"])
        axs[0].plot(ns, p50, marker="o", markersize=6, label=label, color=SERIES[k])
        axs[1].plot(ns, p95, marker="o", markersize=6, label=label, color=SERIES[k])
    for ax, t in zip(axs, ("Median horizontal error", "95th percentile horizontal error")):
        ax.set_yscale("log")
        ax.set_xlabel("Receivers")
        ax.set_ylabel("[m]")
        ax.set_title(t)
        ax.set_xticks(sizes)
    axs[0].legend()
    img_types = figs.save(fig, "error_vs_receivers.png")

    # Error vs range from the array center.
    fig, ax = plt.subplots(figsize=(6.5, 3.8))
    bins = np.arange(0, 175, 25)
    for k, n in enumerate((4, 5, 6, 8)):
        r = runs.get(f"size-adsbee_1090-48-{n}")
        if not r:
            continue
        rng_km = np.array([r["range_km"][str(int(x))] for x in arr(r, 0)])
        h = arr(r, 2)
        med = [np.median(h[(rng_km >= a) & (rng_km < b)]) if np.any((rng_km >= a) & (rng_km < b)) else np.nan
               for a, b in zip(bins[:-1], bins[1:])]
        ax.plot((bins[:-1] + bins[1:]) / 2, med, marker="o", markersize=6, label=f"{n} receivers",
                color=SERIES[k + 1])
    ax.set_yscale("log")
    ax.set_xlabel("Aircraft distance from the array center [km] (array: 30 km between neighbors)")
    ax.set_ylabel("Median horizontal error [m]")
    ax.set_title("Error grows with range outside the array")
    ax.legend()
    img_range = figs.save(fig, "error_vs_range.png")

    # Update rate per aircraft.
    fig, ax = plt.subplots(figsize=(6.5, 3.6))
    r = runs.get("size-adsbee_1090-48-5")
    if r:
        ra = per_aircraft_rates(r)
        rm = per_aircraft_rates(r, modes_only=True)
        ax.hist([ra, rm], bins=np.arange(0, 12.5, 0.5), label=["All aircraft", "Mode S only (no ADS-B)"],
                color=[SERIES[0], SERIES[1]], rwidth=0.85)
        ax.set_xlabel("MLAT position updates per second, per aircraft")
        ax.set_ylabel("Aircraft")
        ax.set_title("Update rate follows each aircraft's message rate (5 receivers)")
        ax.legend()
    img_rate = figs.save(fig, "update_rate.png")

    # Latency (socket run).
    sock = runs.get("socket-48-5")
    img_lat = ""
    lat_text = ""
    if sock:
        fig, ax = plt.subplots(figsize=(6.5, 3.4))
        for k, src in enumerate(("mlat", "adsb")):
            v = np.array(sock["latency_s"].get(src, [])) * 1e3
            if len(v):
                cdf(ax, v, {"mlat": "MLAT fixes", "adsb": "ADS-B positions"}[src], SERIES[k])
        ax.set_xlabel("Emission to fix handed to the publisher [ms]")
        ax.set_ylabel("Fixes [%]")
        ax.set_title("Latency over TCP sockets, real time, 0.3 s grouping window")
        ax.legend(loc="lower right")
        img_lat = figs.save(fig, "latency.png")
        v = np.array(sock["latency_s"]["mlat"]) * 1e3
        s = sock["summary"]
        lat_text = (f"<p>Real-time run, 5 receivers streaming Beast with receiver info frames over TCP for "
                    f"{sock['duration_s']:.0f} s: {sock['published']['mlat']:,} MLAT fixes and "
                    f"{sock['published']['adsb']:,} ADS-B positions published. MLAT latency median "
                    f"{np.median(v):.0f} ms, 95th percentile {np.percentile(v, 95):.0f} ms. Published MLAT fixes "
                    f"(Mode S only aircraft): median horizontal error {f1(s.get('h_p50'))} m, "
                    f"95th percentile {f0(s.get('h_p95'))} m, median rate {f1(s.get('rate_hz_median'))} per second "
                    f"per aircraft.</p>")

    # Tables: GNSS noise, baselines, bad clocks, m1421.
    def row(name, label):
        r = runs.get(name)
        if not r:
            return None
        s = r["summary"]
        return [label, f1(s.get("h_p50")), f0(s.get("h_p95")), f1(s.get("v_p95")), f1(s.get("rate_hz_median"))]

    base = row("size-adsbee_1090-48-5", "Surveyed positions (reference)")
    gnss_rows = [base] + [row(f"gnss-{g:g}", f"GNSS, {g:g} m horizontal / {2 * g:g} m vertical sigma")
                          for g in (2.0, 5.0, 10.0)]
    base_rows = [row(f"baseline-{b}", f"{b} km") for b in (10, 20)] + [
        [base[0].replace("Surveyed positions (reference)", "30 km")] + base[1:]] + [row("baseline-50", "50 km")]
    bad_labels = {"walk": "Frequency random walk 0.5 ppm per root second",
                  "jitter": "Timestamp jitter 400 ns RMS",
                  "wander": "Frequency wander 2 ppm, 60 s period",
                  "steps": "Phase steps of +3 us and -7 us",
                  "reset": "Counter reset (reboot) at 70 s"}
    bad_rows = []
    ref6 = runs.get("size-adsbee_1090-48-6")
    if ref6:
        s = ref6["summary"]
        bad_rows.append(["None (reference)", f1(s["h_p50"]), f0(s["h_p95"]), "-", "-"])
    for b, label in bad_labels.items():
        r = runs.get(f"bad-{b}")
        if not r:
            continue
        s = r["summary"]
        st = {x["id"]: x for x in r["receivers"]}.get("rx2", {})
        bad_rows.append([label, f1(s["h_p50"]), f0(s["h_p95"]), f1(st.get("clock_err_ns")),
                         "yes" if st.get("sync_ok") else "no (excluded)"])
    m = row("m1421-48-5", "ADSBee m1421 (sync word stamp, 125 ns grid)")

    bench_rows = []
    for f in args.bench:
        with open(f) as fh:
            b = json.load(fh)
        mode = b.get("label", os.path.basename(f))
        if "workers" in b:
            bench_rows.append([mode, f"{b['offered_msgs_per_s']:,}", f"{b['mean_group_size']}", f"{b['workers']} workers",
                               f"{b['realtime_factor']:.2f}x real time"])
        else:
            bench_rows.append([mode, f"{b['offered_msgs_per_s']:,}", f"{b['mean_group_size']}", "1 process",
                               f"{b['engine_realtime_load'] * 100:.0f} % of one core "
                               f"({1 / b['engine_realtime_load']:.1f}x real time)"])
        parse_rate = b["parse_msgs_per_s"]

    css = """
:root{--bg:#fcfcfb;--ink:#0b0b0b;--ink2:#52514e;--line:#e4e3df;--accent:#2a78d6}
@media (prefers-color-scheme: dark){:root:not([data-theme="light"]){--bg:#1a1a19;--ink:#fff;--ink2:#c3c2b7;--line:#3a3a37;--accent:#3987e5}}
:root[data-theme="dark"]{--bg:#1a1a19;--ink:#fff;--ink2:#c3c2b7;--line:#3a3a37;--accent:#3987e5}
body{background:var(--bg);color:var(--ink);font:15px/1.5 system-ui,-apple-system,Segoe UI,sans-serif;margin:0}
main{max-width:1040px;margin:0 auto;padding:24px 16px 64px}
h1{font-size:26px;margin:0 0 4px}h2{font-size:19px;margin:36px 0 8px;border-top:1px solid var(--line);padding-top:20px}
p,li{color:var(--ink)}.sub{color:var(--ink2)}
img{max-width:100%;height:auto;border:1px solid var(--line);border-radius:6px;margin:8px 0;background:#fcfcfb}
table{border-collapse:collapse;margin:8px 0 16px;font-size:14px;display:block;overflow-x:auto}
th,td{border-bottom:1px solid var(--line);padding:6px 10px;text-align:right;white-space:nowrap}
th:first-child,td:first-child{text-align:left}th{color:var(--ink2);font-weight:600}
.kpis{display:flex;flex-wrap:wrap;gap:12px;margin:16px 0}.kpi{border:1px solid var(--line);border-radius:8px;padding:10px 14px;min-width:150px}
.kpi b{display:block;font-size:22px}.kpi span{color:var(--ink2);font-size:13px}
"""
    r5 = runs.get("size-adsbee_1090-48-5", {}).get("summary", {})
    r8 = runs.get("size-adsbee_1090-48-8", {}).get("summary", {})
    lat_med = np.median(np.array(sock["latency_s"]["mlat"])) * 1e3 if sock else float("nan")
    kpis = f"""<div class="kpis">
<div class="kpi"><b>{f1(r5.get('h_p50'))} m</b><span>median horizontal error, 5 receivers</span></div>
<div class="kpi"><b>{f1(r8.get('h_p50'))} m</b><span>median horizontal error, 8 receivers</span></div>
<div class="kpi"><b>{f1(r5.get('rate_hz_median'))} /s</b><span>median MLAT updates per aircraft</span></div>
<div class="kpi"><b>{lat_med:.0f} ms</b><span>median latency (0.3 s grouping)</span></div>
</div>"""
    doc = f"""<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>ADSBee MLAT Validation</title>
<style>{css}</style></head><body><main>
<h1>ADSBee MLAT server core: validation</h1>
<p class="sub">Simulated traffic (adsbee_mlat_sim), 50 aircraft within 150 km, 40 % without ADS-B, 180 s per
scenario, first 30 s left out. Every message heard by two or more synchronized receivers updates the aircraft's track
(all aircraft are tracked here, also the ADS-B ones, so their GNSS positions serve as truth). Receivers on a ring
30 km between neighbors, plus one in the center from 5 receivers on.</p>
{kpis}
<h2>Accuracy by array size</h2>
{img_cdf}
<p>Vertical error stays small because the fix includes the barometric altitude (corrected with the ADS-B GNSS height
difference when the aircraft sends one).</p>
{img_types}
{table(["Receivers", "n", "Horizontal p50 [m]", "p95 [m]", "Vertical p95 [m]", "Mode S only p50 [m]",
        "Updates/s per aircraft", "Inside reported error"], size_rows)}
<p>The 48 and 12 MHz curves of the ADSBee 1090 nearly coincide: with this error model the per receiver and aircraft
biases, clock sync and geometry outweigh the counter resolution. See the timestamp study (t-0429) for the error
budget.</p>
<p>"Inside reported error": share of fixes whose true horizontal error is below the published <code>err_m</code>
(about 65 % is the goal for a one sigma estimate; with few receivers the estimate is optimistic by up to 1.4 times). Three receivers locate aircraft only where the solution is unique;
outside the array a fix with three receivers and altitude has a mirror solution, which the server detects and skips,
but the tail shows some mirror tracks remain. Use four or more receivers.</p>
{img_range}
<h2>Update rate</h2>
{img_rate}
<p>Fixes are not resampled: each Mode S reply, all-call reply or squitter heard by two synchronized receivers moves the
track, so an aircraft is updated as often as it transmits (here 2 to 12 messages per second each).</p>
<h2>Latency</h2>
<p>Latency is set by the grouping window (0.3 s), the time the server waits for copies of a message from all
receivers. Fixes below it are repeated identical replies that joined a window already open.</p>
{img_lat}
{lat_text}
<h2>Receiver position from GNSS</h2>
{table(["Receiver positions", "Horizontal p50 [m]", "p95 [m]", "Vertical p95 [m]", "Updates/s"],
       [x for x in gnss_rows if x])}
<h2>Baseline (5 receivers)</h2>
{table(["Distance between neighbors", "Horizontal p50 [m]", "p95 [m]", "Vertical p95 [m]", "Updates/s"],
       [x for x in base_rows if x])}
<h2>One receiver with a bad clock (6 receivers)</h2>
{table(["Fault on receiver rx2", "Horizontal p50 [m]", "p95 [m]", "rx2 estimated clock error [ns]",
        "rx2 used"], bad_rows)}
<p>Clock pairs adapt their process noise to the oscillator, so wander and phase steps are tracked. A receiver whose
timestamp noise exceeds 500 ns is left out; a counter reset is detected from the Unix time map and its pairs start
over.</p>
<h2>Receiver types</h2>
{table(["Receiver", "Horizontal p50 [m]", "p95 [m]", "Vertical p95 [m]", "Updates/s"],
       [x for x in ([["ADSBee 1090, 48 MHz"] + base[1:]] if base else []) + [m] if x])}
<h2>Throughput</h2>
<p>50 receivers spread over a 100 km radius, 400 aircraft within 250 km: about 2,000 messages per second per
receiver, 100,000 in total, each message heard by about 40 receivers. Beast parsing alone runs at
{parse_rate:,} messages per second on one core.</p>
{table(["Case", "Messages/s offered", "Receivers per message", "Processes", "Result"], bench_rows)}
<p>"MLAT for all": every message of every aircraft updates a track. In normal operation aircraft with a live ADS-B
position are tracked with one message in ten (to fill gaps), which is the "typical" case.</p>
</main></body></html>"""
    with open(args.out, "w") as f:
        f.write(doc)
    print("wrote", args.out, figs.names)


if __name__ == "__main__":
    main()
