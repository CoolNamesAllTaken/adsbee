import statistics
import time

import pytest

pytestmark = pytest.mark.e2e

FIX_COUNTS = "Object.fromEntries([...mlat.tracks.values()].map(a => [a.icao, [a.src, a.nFix]]))"


def fix_rates(page, seconds):
    """Per-source fix rates (Hz) seen by the page over `seconds`."""
    before = page.evaluate(FIX_COUNTS)
    time.sleep(seconds)
    after = page.evaluate(FIX_COUNTS)
    rates = {0: [], 1: []}
    for icao, (src, n) in after.items():
        if icao in before:
            rates[src].append((n - before[icao][1]) / seconds)
    return rates


def screen_motion(page, frames=60):
    """Fraction of display frames in which an aircraft moved on screen."""
    return page.evaluate("""frames => new Promise(done => {
        const ac = [...mlat.tracks.values()].find(a => a.gs > 100 && a.sx === a.sx);
        let last = null, moved = 0, n = 0;
        const step = () => {
            const p = [ac.sx, ac.sy];
            if (last && (p[0] !== last[0] || p[1] !== last[1])) moved++;
            last = p;
            if (++n < frames) requestAnimationFrame(step); else done(moved / (frames - 1));
        };
        requestAnimationFrame(step);
    })""", frames)


def test_fix_rates_and_motion(stack, page, media_dir):
    stack.publish("--aircraft", "60", "--mlat-fraction", "0.5", "--adsb-hz", "2", "--mlat-hz", "5",
                  "--radius-km", "60", "--seed", "3")
    page.goto(stack.url)
    page.wait_for_function("mlat.tracks.size >= 60 && mlat.receivers.size === 8", timeout=15000)
    time.sleep(2)
    rates = fix_rates(page, 5)
    adsb, mlat_ = statistics.median(rates[0]), statistics.median(rates[1])
    print(f"median fix rate: ADS-B {adsb:.2f} Hz, MLAT {mlat_:.2f} Hz")
    # Every fix reaches the map at its native rate.
    assert 1.7 <= adsb <= 2.3
    assert 4.3 <= mlat_ <= 5.7
    # Dead reckoning moves aircraft on (nearly) every frame, well above the fix rate.
    moved = screen_motion(page)
    print(f"aircraft moved in {moved:.0%} of frames")
    assert moved > 0.9

    # Selecting an aircraft opens the detail panel.
    icao = page.evaluate("[...mlat.tracks.values()].find(a => a.src === 1).icao")
    page.evaluate(f"mlat.select('{icao}')")
    page.wait_for_selector("#detail:not([hidden])")
    assert page.inner_text("#d-icao") == icao.upper()
    assert page.inner_text("#d-src") == "MLAT"
    if media_dir:
        page.evaluate("mlat.map.setView([37.4, -122.05], 9, {animate: false})")
        time.sleep(1.5)
        page.screenshot(path=str(media_dir / "map-overview.png"))


def test_hover_tooltip_and_toggles(stack, page):
    stack.publish("--aircraft", "60", "--radius-km", "60", "--seed", "4")
    page.goto(stack.url)
    page.wait_for_function("mlat.tracks.size >= 60", timeout=15000)
    time.sleep(1)
    xy = page.evaluate("(() => { const a = [...mlat.tracks.values()].find(a => a.sx > 300 && a.sx < 1100 && a.sy > 200 && a.sy < 700); return [a.sx, a.sy]; })()")
    page.mouse.move(xy[0], xy[1])
    page.wait_for_selector("#tip:not([hidden])")
    assert "ft" in page.inner_text("#tip")
    page.click("[data-layer=mlat]")
    assert page.evaluate("mlat.layers.mlat") is False
    page.wait_for_function("[...mlat.tracks.values()].every(a => a.src === 0 || a.sx !== a.sx)")


def fps(page, ms=2000):
    return page.evaluate("""ms => new Promise(d => { let n = 0; const t0 = performance.now();
        const f = () => { if (performance.now() - t0 < ms) { n++; requestAnimationFrame(f); } else d(n * 1000 / ms); };
        requestAnimationFrame(f); })""", ms)


def test_load_1000_aircraft_at_10hz(stack, page, media_dir):
    stack.publish("--aircraft", "1000", "--mlat-fraction", "0.5", "--adsb-hz", "10", "--mlat-hz", "10",
                  "--radius-km", "250", "--seed", "5")
    page.goto(stack.url)
    page.wait_for_function("mlat.tracks.size >= 1000", timeout=20000)
    page.evaluate("mlat.map.setView([37.4, -122.05], 7, {animate: false}); mlat.layers.trails = true")
    time.sleep(3)
    page.evaluate("mlat.layers.adsb = mlat.layers.mlat = false")
    fps_hidden = statistics.median(fps(page) for _ in range(3))
    page.evaluate("mlat.layers.adsb = mlat.layers.mlat = true")
    fps_shown = statistics.median(fps(page) for _ in range(3))
    perf = page.evaluate("mlat.perf")
    rates = fix_rates(page, 3)
    rate = statistics.median(rates[0] + rates[1])
    print(f"load: fps {fps_shown:.0f} with 1000 aircraft, {fps_hidden:.0f} with none drawn; "
          f"frame {perf['frameMsAvg']:.1f} ms avg, {perf['frameMsP95']:.1f} ms p95; "
          f"messages {perf['msgMsPerS']:.0f} ms/s; {perf['fixesPerS']:.0f} fixes/s; {rate:.1f} Hz per aircraft")
    assert perf["drawn"] >= 900
    assert perf["fixesPerS"] > 8000 and rate > 8.5
    # The page's own work per frame fits a 60 Hz frame with room to spare, and drawing
    # 1000 aircraft costs little frame rate compared to drawing none.
    assert perf["frameMsP95"] < 12
    assert perf["msgMsPerS"] < 150
    assert fps_shown >= 0.7 * fps_hidden
    if media_dir:
        page.screenshot(path=str(media_dir / "load-1000.png"))
