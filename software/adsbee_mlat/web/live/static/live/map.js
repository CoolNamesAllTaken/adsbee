// ADSBee MLAT live map.
//
// Aircraft are drawn on a canvas layer every display frame. Each fix is applied the moment it
// arrives; between fixes the position is dead-reckoned from ground speed and track, and the
// jump to a new fix is blended out over a fraction of a second.
'use strict';

(() => {
    const CFG = JSON.parse(document.getElementById('mlat-config').textContent);

    // ─── Tuning ─────────────────────────────────────────────────────────────
    const kMaxExtrapolateS = 5;      // Dead-reckoning limit after the last fix.
    const kStaleS = 15;              // Older fixes are drawn faded (as on the ADSBee map).
    const kDropS = 60;               // Aircraft without a fix this long are removed.
    const kBlendTauS = 0.2;          // Time constant for blending out the jump to a new fix.
    const kBlendMaxM = 3000;         // Larger jumps snap.
    const kPreferAdsbS = 3;          // MLAT fixes are ignored this long after an ADS-B fix.
    const kTrailMinIntervalS = 1;    // Trail point spacing (more often on turns).
    const kTrailMaxPoints = 900;
    const kTrailAllMaxPoints = 120;  // Per aircraft when all trails are shown.
    const kTrailRedrawS = 15;        // Full trail redraw interval.
    const kHitPx = 14;
    const kVectorPxPerKt = 0.128;    // Velocity vector length, as on the ADSBee map.
    const kVectorMinPx = 8;
    const kVectorMaxPx = 80;
    const kEarthCircM = 40075016.686;
    const kKtToMps = 0.514444;
    const SRC = [
        { label: 'ADS-B', stroke: 'rgba(0,0,0,0.55)', width: 1.2 },
        { label: 'MLAT', stroke: '#e11d48', width: 2.4 },
    ];
    const kMlatFill = 'rgba(225,29,72,0.10)';
    const kMlatEdge = 'rgba(225,29,72,0.45)';
    // Aircraft outline from the ADSBee map icon, centered on the rotation point.
    const kPlaneShape = [[0, -14], [7, 11], [0, 6], [-7, 11]];

    // ─── Helpers ────────────────────────────────────────────────────────────
    // Altitude color: tar1090 continuous HSL gradient, as on the ADSBee map.
    function altColor(altFt) {
        if (altFt == null) return '#888888';
        const hue = 30 + (Math.max(0, Math.min(altFt, 40000)) / 40000) * 255;
        return `hsl(${hue.toFixed(1)}, 90%, 55%)`;
    }
    // Colors in 500 ft steps (about 3 hue degrees) so icons and trails can be batched by color.
    const altBucket = altFt => (altFt == null ? -1 : Math.round(Math.max(0, Math.min(altFt, 40000)) / 500));
    const kBucketColors = Array.from({ length: 81 }, (_, b) => altColor(b * 500));
    const bucketColor = b => (b < 0 ? '#888888' : kBucketColors[b]);

    // Web Mercator in units of the world square (0..1); matches Leaflet's EPSG:3857.
    const mercX = lon => (lon + 180) / 360;
    const mercY = lat => {
        const s = Math.sin(Math.max(-85.0511, Math.min(85.0511, lat)) * Math.PI / 180);
        return 0.5 - Math.log((1 + s) / (1 - s)) / (4 * Math.PI);
    };

    const fmt = (v, d = 0) => (v == null || !Number.isFinite(v) ? '–' : v.toLocaleString('en-US', { maximumFractionDigits: d, minimumFractionDigits: d }));
    const esc = s => String(s ?? '').replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]);
    const store = {
        get(k, d) { try { const v = localStorage.getItem('mlat.' + k); return v == null ? d : JSON.parse(v); } catch { return d; } },
        set(k, v) { try { localStorage.setItem('mlat.' + k, JSON.stringify(v)); } catch { /* Storage unavailable. */ } },
    };

    // ─── State ──────────────────────────────────────────────────────────────
    const tracks = new Map();   // icao → Track
    const receivers = new Map();
    let stats = null;
    let selected = null;
    let clockOffset = null;     // Server clock minus browser clock (s).
    const offsetSamples = [];
    const layers = Object.assign(
        { trails: false, vectors: true, errors: true, receivers: true, links: true, labels: false, adsb: true, mlat: true },
        store.get('layers', {}));
    const perf = {
        fps: 0, frameMsAvg: 0, frameMsP95: 0, drawn: 0, fixesPerS: 0, msgsPerS: 0, bytesPerS: 0,
        fixAgeMsMedian: null, msgMsPerS: 0, trailMsPerS: 0,
        frames: 0, fixes: 0, msgs: 0, bytes: 0, msgMsSum: 0, trailMsSum: 0, frameTimes: [], fixAges: [],
    };
    const serverNow = () => Date.now() / 1000 + (clockOffset ?? 0);

    class Track {
        constructor(icao) {
            this.icao = icao;
            this.tFix = 0;
            this.adsbT = -Infinity;
            this.vx = this.vy = 0;
            this.corrX = this.corrY = 0;
            this.corrT0 = 0;
            this.trail = [];        // Flat [x, y, altBucket, ...] in world units.
            this.trailT = 0;
            this.trailTrack = null;
            this.trailDrawn = 0;    // Trail points already on the trail canvas.
            this.fixTimes = [];
            this.nFix = 0;
            this.sx = this.sy = NaN; // Screen position in the last frame.
        }

        // Position at server time t (s) and page time tp (s), in world units.
        position(t, tp, out) {
            let dt = t - this.tFix;
            dt = dt < 0 ? 0 : (dt > kMaxExtrapolateS ? kMaxExtrapolateS : dt);
            out.x = this.wx + this.vx * dt;
            out.y = this.wy + this.vy * dt;
            if (this.corrX !== 0 || this.corrY !== 0) {
                const k = Math.exp(-(tp - this.corrT0) / kBlendTauS);
                if (k < 0.005) { this.corrX = this.corrY = 0; } else { out.x += this.corrX * k; out.y += this.corrY * k; }
            }
            return out;
        }

        get rateHz() {
            const n = this.fixTimes.length;
            return n < 2 ? null : (n - 1) / Math.max(1e-3, this.fixTimes[n - 1] - this.fixTimes[0]);
        }
    }

    const tmp = { x: 0, y: 0 };
    function applyFix(row, batchT, tp) {
        const [icao, src, lat, lon, alt, gs, trk, vr, dt, err, nrecv, gdop, callsign, squawk] = row;
        const tFix = batchT + dt;
        let ac = tracks.get(icao);
        if (!ac) { ac = new Track(icao); tracks.set(icao, ac); }
        if (tFix <= ac.tFix) return false;  // Duplicate or out of order.
        // Prefer ADS-B: MLAT fixes are ignored while the aircraft reports its own position.
        if (src === 1 && tFix - ac.adsbT < kPreferAdsbS) return false;
        if (src === 0) ac.adsbT = tFix;
        const had = ac.nFix > 0;
        if (had) ac.position(serverNow(), tp, tmp);
        ac.src = src; ac.lat = lat; ac.lon = lon; ac.alt = alt; ac.gs = gs; ac.trk = trk; ac.vr = vr;
        ac.err = err; ac.nrecv = nrecv; ac.gdop = gdop; ac.tFix = tFix;
        if (callsign) ac.callsign = callsign.trim();
        if (squawk) ac.squawk = squawk;
        ac.wx = mercX(lon);
        ac.wy = mercY(lat);
        const mPerUnit = kEarthCircM * Math.cos(lat * Math.PI / 180);
        if (gs != null && trk != null) {
            const v = gs * kKtToMps / mPerUnit, a = trk * Math.PI / 180;
            ac.vx = v * Math.sin(a);
            ac.vy = -v * Math.cos(a);
        } else {
            ac.vx = ac.vy = 0;
        }
        if (had) {
            const before = { x: tmp.x, y: tmp.y };
            ac.corrX = ac.corrY = 0;
            ac.position(serverNow(), tp, tmp);
            const jx = before.x - tmp.x, jy = before.y - tmp.y;
            if (Math.hypot(jx, jy) * mPerUnit < kBlendMaxM) {
                ac.corrX = jx; ac.corrY = jy; ac.corrT0 = tp;
            }
        }
        ac.fixTimes.push(tFix);
        if (ac.fixTimes.length > 12) ac.fixTimes.shift();
        ac.nFix++;
        ac.recvT = tp;
        // Trail: one point per second, more often while turning.
        const turned = ac.trailTrack != null && trk != null && Math.abs(((trk - ac.trailTrack + 540) % 360) - 180) > 4;
        if (tFix - ac.trailT >= kTrailMinIntervalS || turned) {
            ac.trail.push(ac.wx, ac.wy, altBucket(alt));
            ac.trailT = tFix;
            ac.trailTrack = trk;
            if (ac.trail.length > (kTrailMaxPoints + 60) * 3) {
                ac.trail.splice(0, 180);
                ac.trailDrawn = Math.max(0, ac.trailDrawn - 60);
            }
            trailsNew = true;
        }
        return true;
    }

    // ─── Canvas overlay layer ───────────────────────────────────────────────
    // A canvas covering the viewport inside a map pane. It is repositioned on every move and
    // scaled with CSS during zoom animations, like Leaflet's own renderers.
    const CanvasOverlay = L.Layer.extend({
        initialize(pane, onReset) { this._paneName = pane; this._onResetCb = onReset; },
        onAdd(map) {
            this._canvas = L.DomUtil.create('canvas', 'mlat-canvas leaflet-zoom-animated');
            map.getPane(this._paneName).appendChild(this._canvas);
            this.ctx = this._canvas.getContext('2d');
            this._reset();
        },
        onRemove() { L.DomUtil.remove(this._canvas); },
        getEvents() {
            return { move: this._reset, viewreset: this._reset, resize: this._reset, zoomanim: this._animateZoom };
        },
        _reset() {
            const map = this._map;
            if (map._animatingZoom) return;
            const size = map.getSize(), dpr = window.devicePixelRatio || 1;
            this.topLeft = map.containerPointToLayerPoint([0, 0]);
            this.bounds = map.getBounds();
            L.DomUtil.setPosition(this._canvas, this.topLeft);
            if (this.w !== size.x || this.h !== size.y || this.dpr !== dpr) {
                this.w = size.x; this.h = size.y; this.dpr = dpr;
                this._canvas.width = size.x * dpr;
                this._canvas.height = size.y * dpr;
                this._canvas.style.width = size.x + 'px';
                this._canvas.style.height = size.y + 'px';
            }
            const origin = map.getPixelOrigin();
            this.scale = 256 * Math.pow(2, map.getZoom());
            this.ox = origin.x + this.topLeft.x;
            this.oy = origin.y + this.topLeft.y;
            if (this._onResetCb) this._onResetCb();
        },
        _animateZoom(e) {
            const scale = this._map.getZoomScale(e.zoom);
            const offset = this._map._latLngBoundsToNewLayerBounds(this.bounds, e.zoom, e.center).min;
            L.DomUtil.setTransform(this._canvas, offset, scale);
        },
    });

    // ─── Icons ──────────────────────────────────────────────────────────────
    function drawPlane(g, fill, src, alpha = 1) {
        g.globalAlpha = alpha;
        g.beginPath();
        kPlaneShape.forEach(([x, y], i) => (i ? g.lineTo(x, y) : g.moveTo(x, y)));
        g.closePath();
        g.fillStyle = fill;
        g.fill();
        g.lineJoin = 'round';
        g.lineWidth = SRC[src].width;
        g.strokeStyle = SRC[src].stroke;
        g.stroke();
        g.globalAlpha = 1;
    }
    function paintIcon(canvas, src, alt, track = 0) {
        const g = canvas.getContext('2d'), s = canvas.width / 32;
        g.setTransform(s, 0, 0, s, canvas.width / 2, canvas.height / 2);
        g.clearRect(-16, -16, 32, 32);
        g.rotate(track * Math.PI / 180);
        drawPlane(g, altColor(alt), src);
    }

    // ─── Map ────────────────────────────────────────────────────────────────
    const map = L.map('map', { zoomControl: false, preferCanvas: false, worldCopyJump: true }).setView([20, 0], 3);
    L.control.zoom({ position: 'bottomright' }).addTo(map);
    L.tileLayer(CFG.tiles, {
        attribution: '© <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a>',
        maxZoom: 18,
    }).addTo(map);
    // The map fits the receivers once, unless a start view is configured or the user moved first.
    let userMoved = false;
    if (CFG.start) { map.setView([CFG.start[0], CFG.start[1]], CFG.start[2]); userMoved = true; }
    map.on('dragstart', () => { userMoved = true; });
    map.getContainer().addEventListener('wheel', () => { userMoved = true; }, { passive: true });

    map.createPane('trails').style.zIndex = 410;
    map.createPane('rxlinks').style.zIndex = 420;
    map.createPane('aircraft').style.zIndex = 430;
    map.createPane('rx').style.zIndex = 440;
    let trailsFull = true, trailsNew = false;
    const trailLayer = new CanvasOverlay('trails', () => { trailsFull = true; }).addTo(map);
    const acLayer = new CanvasOverlay('aircraft').addTo(map);
    const rxRenderer = L.svg({ pane: 'rx' });
    const linkRenderer = L.svg({ pane: 'rxlinks' });
    const rxGroup = L.layerGroup().addTo(map);
    const linkGroup = L.layerGroup().addTo(map);

    // ─── Drawing ────────────────────────────────────────────────────────────
    let lastTrailDraw = 0, lastFullTrailDraw = 0;
    const pos = { x: 0, y: 0 };
    const visible = ac => (ac.src === 1 ? layers.mlat : layers.adsb);

    function drawAircraft(tp) {
        const L_ = acLayer, ctx = L_.ctx, dpr = L_.dpr, w = L_.w, h = L_.h;
        if (!ctx) return;
        const t = serverNow(), S = L_.scale, ox = L_.ox, oy = L_.oy;
        ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
        ctx.clearRect(0, 0, w, h);
        const margin = 40;
        let drawn = 0;
        // Pass 1: screen positions, MLAT error circles and velocity vectors (batched per color).
        const errPath = new Path2D();
        const vectors = new Map();
        for (const ac of tracks.values()) {
            if (!visible(ac)) { ac.sx = NaN; continue; }
            ac.position(t, tp, pos);
            let x = pos.x * S - ox;
            const y = pos.y * S - oy;
            // Nearest world copy horizontally.
            if (x < -margin) x += S * Math.ceil((-margin - x) / S);
            else if (x > w + margin) x -= S * Math.ceil((x - w - margin) / S);
            if (x < -margin || x > w + margin || y < -margin || y > h + margin) { ac.sx = NaN; continue; }
            ac.sx = x; ac.sy = y;
            ac.stale = t - ac.tFix > kStaleS;
            ac.bucket = altBucket(ac.alt);
            const a = (ac.trk ?? 0) * Math.PI / 180;
            const c = ac.cos = Math.cos(a), s = ac.sin = Math.sin(a);
            if (ac.src === 1 && ac.err != null && (layers.errors || ac === selected)) {
                const r = ac.err / (kEarthCircM * Math.cos(ac.lat * Math.PI / 180) / S);
                if (r >= 1.5) {
                    errPath.moveTo(x + r, y);
                    errPath.arc(x, y, r, 0, 2 * Math.PI);
                }
            }
            if (layers.vectors && ac.gs > 0 && !ac.stale) {
                const len = Math.min(kVectorMaxPx, Math.max(kVectorMinPx, ac.gs * kVectorPxPerKt));
                let p = vectors.get(ac.bucket);
                if (!p) { p = new Path2D(); vectors.set(ac.bucket, p); }
                p.moveTo(x + 14 * s, y - 14 * c);
                p.lineTo(x + (14 + len) * s, y - (14 + len) * c);
            }
        }
        ctx.fillStyle = kMlatFill;
        ctx.fill(errPath);
        ctx.strokeStyle = kMlatEdge;
        ctx.lineWidth = 1;
        ctx.stroke(errPath);
        ctx.globalAlpha = 0.8;
        ctx.lineWidth = 2;
        for (const [b, p] of vectors) {
            ctx.strokeStyle = bucketColor(b);
            ctx.stroke(p);
        }
        ctx.globalAlpha = 1;
        const sel = selected && selected.sx === selected.sx ? selected : null;
        if (sel && sel.trail.length) {
            // Join the selected trail to the moving icon.
            const n = sel.trail.length, lx = sel.trail[n - 3] * S - ox;
            ctx.beginPath();
            ctx.moveTo(lx + Math.round((sel.sx - lx) / S) * S, sel.trail[n - 2] * S - oy);
            ctx.lineTo(sel.sx, sel.sy);
            ctx.strokeStyle = bucketColor(sel.bucket);
            ctx.stroke();
        }
        // Pass 2: icons, one path per color, source and staleness.
        const icons = new Map();
        for (const ac of tracks.values()) {
            const x = ac.sx, y = ac.sy;
            if (x !== x) continue;  // NaN: off screen or hidden.
            const c = ac.cos, s = ac.sin, key = ac.bucket * 4 + ac.src * 2 + (ac.stale ? 1 : 0);
            let p = icons.get(key);
            if (!p) { p = new Path2D(); icons.set(key, p); }
            for (let i = 0; i < 4; i++) {
                const [px, py] = kPlaneShape[i];
                const X = x + px * c - py * s, Y = y + px * s + py * c;
                if (i) p.lineTo(X, Y); else p.moveTo(X, Y);
            }
            p.closePath();
            drawn++;
        }
        ctx.lineJoin = 'round';
        for (const [key, p] of icons) {
            const src = (key >> 1) & 1;
            ctx.globalAlpha = key & 1 ? 0.35 : 1;
            ctx.fillStyle = bucketColor(Math.floor(key / 4));
            ctx.fill(p);
            ctx.lineWidth = SRC[src].width;
            ctx.strokeStyle = SRC[src].stroke;
            ctx.stroke(p);
        }
        ctx.globalAlpha = 1;
        if (sel) {
            ctx.beginPath();
            ctx.arc(sel.sx, sel.sy, 17, 0, 2 * Math.PI);
            ctx.strokeStyle = 'rgba(255,255,255,0.85)';
            ctx.lineWidth = 2;
            ctx.stroke();
            ctx.strokeStyle = 'rgba(0,0,0,0.35)';
            ctx.lineWidth = 1;
            ctx.beginPath();
            ctx.arc(sel.sx, sel.sy, 19, 0, 2 * Math.PI);
            ctx.stroke();
        }
        if (layers.labels || selected) {
            ctx.font = '11px Arial, sans-serif';
            ctx.lineWidth = 3;
            ctx.strokeStyle = 'rgba(0,0,0,0.6)';
            ctx.fillStyle = '#fff';
            const all = layers.labels && drawn < 600;
            for (const ac of (all ? tracks.values() : [selected])) {
                if (!ac || ac.sx !== ac.sx) continue;
                const label = ac.callsign || ac.icao;
                ctx.strokeText(label, ac.sx + 12, ac.sy + 14);
                ctx.fillText(label, ac.sx + 12, ac.sy + 14);
            }
        }
        perf.drawn = drawn;
    }

    // Trails are drawn incrementally: new segments are added to the canvas as points arrive, and the
    // canvas is redrawn in full only when the view or selection changes (or periodically, to drop
    // points that aged out).
    function drawTrails(tp, full) {
        const L_ = trailLayer, ctx = L_.ctx;
        if (!ctx) return;
        trailsNew = false;
        lastTrailDraw = tp;
        ctx.setTransform(L_.dpr, 0, 0, L_.dpr, 0, 0);
        if (full) {
            trailsFull = false;
            lastFullTrailDraw = tp;
            ctx.clearRect(0, 0, L_.w, L_.h);
        }
        const S = L_.scale, ox = L_.ox, oy = L_.oy, w = L_.w;
        // One path per altitude color: thousands of segments cost a handful of strokes.
        const paths = new Map();
        const addTrail = (ac, maxPts) => {
            const tr = ac.trail, n = tr.length / 3;
            const first = full ? Math.max(0, n - maxPts) : Math.max(0, ac.trailDrawn - 1);
            ac.trailDrawn = n;
            if (n - first < 2) return;
            let px = tr[first * 3] * S - ox, py = tr[first * 3 + 1] * S - oy;
            // Draw on the world copy nearest the view center.
            const wrap = Math.round((w / 2 - px) / S) * S;
            px += wrap;
            for (let i = first + 1; i < n; i++) {
                const x = tr[i * 3] * S - ox + wrap, y = tr[i * 3 + 1] * S - oy, b = tr[i * 3 + 2];
                let p = paths.get(b);
                if (!p) { p = new Path2D(); paths.set(b, p); }
                p.moveTo(px, py);
                p.lineTo(x, y);
                px = x; py = y;
            }
        };
        for (const ac of tracks.values()) {
            if (ac === selected) addTrail(ac, kTrailMaxPoints);
            else if (layers.trails && visible(ac)) addTrail(ac, kTrailAllMaxPoints);
        }
        ctx.lineWidth = 2;
        ctx.lineJoin = 'round';
        ctx.globalAlpha = 0.85;
        for (const [b, p] of paths) {
            ctx.strokeStyle = bucketColor(b);
            ctx.stroke(p);
        }
        ctx.globalAlpha = 1;
    }

    // ─── Frame loop ─────────────────────────────────────────────────────────
    let fpsWindowStart = performance.now();
    function frame(ts) {
        requestAnimationFrame(frame);
        const t0 = performance.now(), tp = ts / 1000;
        if (trailsFull || tp - lastFullTrailDraw > kTrailRedrawS) drawTrails(tp, true);
        else if (trailsNew && tp - lastTrailDraw > 0.25) drawTrails(tp, false);
        const t1 = performance.now();
        drawAircraft(tp);
        const dt = performance.now() - t0;
        perf.trailMsSum += t1 - t0;
        perf.frames++;
        perf.frameTimes.push(dt);
        if (perf.frameTimes.length > 240) perf.frameTimes.shift();
        if (t0 - fpsWindowStart >= 1000) {
            const s = (t0 - fpsWindowStart) / 1000;
            perf.fps = perf.frames / s;
            perf.fixesPerS = perf.fixes / s;
            perf.msgsPerS = perf.msgs / s;
            perf.bytesPerS = perf.bytes / s;
            perf.msgMsPerS = perf.msgMsSum / s;
            perf.trailMsPerS = perf.trailMsSum / s;
            perf.frames = perf.fixes = perf.msgs = perf.bytes = perf.msgMsSum = perf.trailMsSum = 0;
            const sorted = [...perf.frameTimes].sort((a, b) => a - b);
            perf.frameMsAvg = sorted.reduce((a, b) => a + b, 0) / Math.max(1, sorted.length);
            perf.frameMsP95 = sorted[Math.floor(sorted.length * 0.95)] ?? 0;
            const ages = perf.fixAges.sort((a, b) => a - b);
            perf.fixAgeMsMedian = ages.length ? ages[ages.length >> 1] : null;
            perf.fixAges = [];
            fpsWindowStart = t0;
            everySecond();
        }
    }
    requestAnimationFrame(frame);

    // ─── WebSocket ──────────────────────────────────────────────────────────
    const connEl = document.getElementById('conn');
    let retry = 0;
    function connect() {
        const url = new URL(CFG.ws, location.href);
        url.protocol = location.protocol === 'https:' ? 'wss:' : 'ws:';
        const ws = new WebSocket(url);
        ws.onopen = () => { retry = 0; connEl.className = 'conn live'; connEl.dataset.tip = 'Live'; };
        ws.onclose = () => {
            connEl.className = 'conn down';
            connEl.dataset.tip = 'Reconnecting';
            setTimeout(connect, Math.min(10000, 500 * 2 ** retry++));
        };
        ws.onmessage = ev => {
            const t0 = performance.now();
            perf.msgs++;
            perf.bytes += ev.data.length;
            let msg;
            try { msg = JSON.parse(ev.data); } catch { return; }
            if (msg.type === 'ac') onAircraft(msg);
            else if (msg.type === 'rx') onReceivers(msg);
            else if (msg.type === 'stats') onStats(msg);
            perf.msgMsSum += performance.now() - t0;
        };
    }

    function onAircraft(msg) {
        const now = Date.now() / 1000;
        if (!msg.snap) {
            // The batch time can only be earlier than its arrival; the largest recent offset is the best clock estimate.
            offsetSamples.push(msg.t - now);
            if (offsetSamples.length > 100) offsetSamples.shift();
            clockOffset = Math.max(...offsetSamples);
        }
        const tp = performance.now() / 1000;
        for (const row of msg.a) {
            if (applyFix(row, msg.t, tp)) {
                perf.fixes++;
                if (!msg.snap) perf.fixAges.push((serverNow() - (msg.t + row[8])) * 1000);
            }
        }
    }

    // ─── Receivers ──────────────────────────────────────────────────────────
    const rxMarkers = new Map();
    const links = new Map();
    function rxTip(r) {
        const sync = r.sync_ok ? '<span class="ok">● sync</span>' : '<span class="bad">● no sync</span>';
        return `<b>${esc(r.name || r.id)}</b> <span class="dim">${esc(r.id)}</span><br>` +
            `${sync}${r.clock_err_ns != null ? ` ±${fmt(r.clock_err_ns, 0)} ns` : ''}<br>` +
            `✉ ${fmt(r.msg_rate, 0)}/s · ⇄ ${(r.peers || []).length} · ${fmt(r.clock_hz / 1e6, 0)} MHz<br>` +
            `<span class="dim">⌖ ${esc(r.pos_src)} · ${fmt(r.alt_m, 0)} m${r.owner ? ' · ' + esc(r.owner) : ''}</span>`;
    }
    function onReceivers(msg) {
        const seen = new Set();
        for (const r of msg.receivers || []) {
            if (!Number.isFinite(r.lat) || !Number.isFinite(r.lon)) continue;
            seen.add(r.id);
            receivers.set(r.id, r);
            let m = rxMarkers.get(r.id);
            const style = { color: r.sync_ok ? '#16a34a' : '#dc2626' };
            if (!m) {
                m = L.circleMarker([r.lat, r.lon], {
                    renderer: rxRenderer, pane: 'rx', radius: 7, weight: 3, fillColor: '#ffcb00', fillOpacity: 1, ...style,
                }).bindTooltip('', { className: 'rx-tip', direction: 'top', offset: [0, -6] });
                rxMarkers.set(r.id, m);
                if (layers.receivers) m.addTo(rxGroup);
            } else {
                m.setLatLng([r.lat, r.lon]);
                m.setStyle(style);
            }
            m.setTooltipContent(rxTip(r));
        }
        for (const [id, m] of rxMarkers) if (!seen.has(id)) { m.remove(); rxMarkers.delete(id); receivers.delete(id); }
        // Sync links: solid when both ends list each other, dashed when only one does.
        const want = new Map();
        for (const r of receivers.values()) {
            for (const p of r.peers || []) {
                if (!receivers.has(p) || p === r.id) continue;
                const key = r.id < p ? `${r.id}|${p}` : `${p}|${r.id}`;
                want.set(key, (want.get(key) || 0) + 1);
            }
        }
        for (const [key, n] of want) {
            const [a, b] = key.split('|').map(id => receivers.get(id));
            const ll = [[a.lat, a.lon], [b.lat, b.lon]];
            const style = { color: n > 1 ? '#16a34a' : '#f59e0b', dashArray: n > 1 ? null : '6 5', weight: 2, opacity: 0.6 };
            let l = links.get(key);
            if (!l) {
                l = L.polyline(ll, { renderer: linkRenderer, pane: 'rxlinks', interactive: true, ...style })
                    .bindTooltip(`${esc(a.name || a.id)} ⇄ ${esc(b.name || b.id)}`, { className: 'rx-tip', sticky: true });
                links.set(key, l);
                if (layers.links) l.addTo(linkGroup);
            } else {
                l.setLatLngs(ll);
                l.setStyle(style);
            }
        }
        for (const [key, l] of links) if (!want.has(key)) { l.remove(); links.delete(key); }
        if (!userMoved && receivers.size) {
            const b = L.latLngBounds([...receivers.values()].map(r => [r.lat, r.lon]));
            map.fitBounds(b.pad(1.2), { maxZoom: 9, animate: false });
            userMoved = true;
        }
        updateStats();
    }

    // ─── Stats ──────────────────────────────────────────────────────────────
    const solveHist = [], latHist = [];
    function onStats(msg) {
        stats = msg;
        const solves = msg.solves_per_s ?? msg.solve_rate ?? null;
        const lat = msg.latency_ms ?? (msg.latency_s != null ? msg.latency_s * 1000 : null);
        solveHist.push(solves); latHist.push(lat);
        if (solveHist.length > 60) { solveHist.shift(); latHist.shift(); }
        updateStats();
    }
    function spark(id, hist) {
        const vals = hist.filter(v => v != null);
        const el = document.querySelector(`#${id} path`);
        if (vals.length < 2) { el.setAttribute('d', ''); return; }
        const max = Math.max(...vals) || 1;
        el.setAttribute('d', hist.map((v, i) => `${i ? 'L' : 'M'}${(i / 59) * 60},${18 - ((v ?? 0) / max) * 16 - 1}`).join(''));
    }
    const $ = id => document.getElementById(id);
    function updateStats() {
        let nA = 0, nM = 0;
        const t = serverNow();
        for (const ac of tracks.values()) {
            if (t - ac.tFix > kStaleS) continue;
            if (ac.src === 1) nM++; else nA++;
        }
        $('st-ac-n').textContent = fmt(nA + nM);
        $('st-ac-adsb').textContent = fmt(nA);
        $('st-ac-mlat').textContent = fmt(nM);
        $('st-ac').dataset.tip = `${fmt(nA + nM)} aircraft: ${fmt(nA)} ADS-B, ${fmt(nM)} MLAT<br>` +
            `<span class="dim">${fmt(perf.fixesPerS, 0)} fixes/s to this page</span>`;
        const solves = solveHist.length ? solveHist[solveHist.length - 1] : null;
        const lat = latHist.length ? latHist[latHist.length - 1] : null;
        $('st-solve-n').textContent = fmt(solves, 0);
        $('st-lat-n').textContent = fmt(lat, 0);
        spark('st-solve-spark', solveHist);
        spark('st-lat-spark', latHist);
        const extra = stats ? Object.entries(stats).filter(([k, v]) => !['type', 't'].includes(k) && typeof v !== 'object')
            .map(([k, v]) => `<span class="dim">${esc(k)}</span> ${esc(typeof v === 'number' ? fmt(v, 1) : v)}`).join('<br>') : '';
        $('st-solve').dataset.tip = `MLAT solves per second<br>${extra}`;
        $('st-lat').dataset.tip = `Solver latency (ms)<br><span class="dim">fix age at this page</span> ${fmt(perf.fixAgeMsMedian, 0)} ms`;
        const rx = [...receivers.values()];
        const ok = rx.filter(r => r.sync_ok).length;
        $('st-rx-n').textContent = rx.length ? `${ok}/${rx.length}` : '–';
        $('st-rx-dots').innerHTML = rx.map(r => `<i class="${r.sync_ok ? '' : 'bad'}"></i>`).join('');
        $('st-rx').dataset.tip = rx.length ? rx.map(r => `<span class="${r.sync_ok ? 'ok' : 'bad'}">●</span> ${esc(r.name || r.id)}`).join('<br>') : 'Receivers in sync';
        $('st-fps-n').textContent = `${fmt(perf.fps, 0)}`;
        $('st-fps').dataset.tip = `Frames per second<br><span class="dim">draw</span> ${fmt(perf.frameMsAvg, 1)} ms avg, ${fmt(perf.frameMsP95, 1)} ms p95<br>` +
            `<span class="dim">drawn</span> ${fmt(perf.drawn)} · <span class="dim">feed</span> ${fmt(perf.bytesPerS / 1024, 0)} KiB/s`;
    }

    function everySecond() {
        const t = serverNow();
        for (const [icao, ac] of tracks) {
            if (t - ac.tFix > kDropS) {
                tracks.delete(icao);
                if (ac === selected) select(null);
                trailsFull = true;
            }
        }
        updateStats();
        if (selected) updateDetail();
        if (tipTarget && tipTarget.ac) showAircraftTip(tipTarget.ac, tipTarget.x, tipTarget.y);
    }

    // ─── Selection and detail panel ─────────────────────────────────────────
    const detailEl = $('detail');
    function select(ac) {
        selected = ac;
        trailsFull = true;
        detailEl.hidden = !ac;
        if (ac) updateDetail();
    }
    function updateDetail() {
        const ac = selected;
        const age = serverNow() - ac.tFix;
        detailEl.classList.toggle('is-mlat', ac.src === 1);
        $('d-call').textContent = ac.callsign || ac.icao.toUpperCase();
        $('d-icao').textContent = ac.icao.toUpperCase();
        const srcEl = $('d-src');
        srcEl.textContent = SRC[ac.src].label;
        srcEl.className = 'chip ' + (ac.src === 1 ? 'mlat' : 'adsb');
        $('d-alt').textContent = fmt(ac.alt);
        $('d-vr').textContent = ac.vr == null ? '–' : (ac.vr > 0 ? '+' : '') + fmt(ac.vr);
        $('d-gs').textContent = fmt(ac.gs);
        $('d-trk').textContent = ac.trk == null ? '–' : fmt(ac.trk) + '°';
        $('d-trk-arrow').style.transform = `rotate(${ac.trk ?? 0}deg)`;
        $('d-sq').textContent = ac.squawk ?? '–';
        $('d-rate').textContent = fmt(ac.rateHz, 1);
        $('d-err').textContent = fmt(ac.err);
        $('d-nrecv').textContent = fmt(ac.nrecv);
        $('d-gdop').textContent = fmt(ac.gdop, 1);
        $('d-age').textContent = fmt(Math.max(0, age), 1);
        $('d-pos').textContent = `${ac.lat.toFixed(5)}, ${ac.lon.toFixed(5)}`;
        paintIcon($('d-icon'), ac.src, ac.alt, ac.trk ?? 0);
        // Altitude profile from the trail.
        const tr = ac.trail, n = tr.length / 3, prof = $('d-prof');
        if (n >= 2) {
            const pts = [];
            for (let i = Math.max(0, n - 200); i < n; i++) pts.push(tr[i * 3 + 2] < 0 ? 0 : tr[i * 3 + 2] * 500);
            const max = 45000;
            const xy = pts.map((v, i) => `${(i / (pts.length - 1)) * 200},${40 - (v / max) * 36 - 2}`);
            prof.innerHTML = `<path class="area" d="M0,40L${xy.join('L')}L200,40Z"/><path class="line" d="M${xy.join('L')}"/>`;
            prof.dataset.tip = `Altitude profile, 0 to ${fmt(max)} ft`;
        } else {
            prof.innerHTML = '';
        }
    }
    $('d-close').onclick = () => select(null);

    // ─── Hover and click ────────────────────────────────────────────────────
    const tipEl = $('tip');
    let tipTarget = null;
    function nearest(x, y) {
        let best = null, bd = kHitPx * kHitPx;
        for (const ac of tracks.values()) {
            const dx = ac.sx - x, dy = ac.sy - y, d = dx * dx + dy * dy;
            if (d < bd) { bd = d; best = ac; }
        }
        return best;
    }
    function placeTip(cx, cy) {
        tipEl.hidden = false;
        const r = tipEl.getBoundingClientRect();
        let x = cx + 14, y = cy + 14;
        if (x + r.width > innerWidth - 4) x = cx - r.width - 14;
        if (y + r.height > innerHeight - 4) y = cy - r.height - 14;
        tipEl.style.left = x + 'px';
        tipEl.style.top = y + 'px';
    }
    function showAircraftTip(ac, cx, cy) {
        const src = ac.src === 1
            ? `<span class="m">◆ MLAT</span> ±${fmt(ac.err)} m · ${fmt(ac.nrecv)} rx`
            : '<span class="dim">◆ ADS-B</span>';
        tipEl.innerHTML = `<b>${esc(ac.callsign || ac.icao.toUpperCase())}</b> <span class="dim">${esc(ac.icao)}</span><br>` +
            `⇡ ${fmt(ac.alt)} ft · » ${fmt(ac.gs)} kt · ${fmt(ac.trk)}°<br>${src}`;
        placeTip(cx, cy);
    }
    map.on('mousemove', e => {
        const ac = nearest(e.containerPoint.x, e.containerPoint.y);
        map.getContainer().style.cursor = ac ? 'pointer' : '';
        if (ac) {
            tipTarget = { ac, x: e.originalEvent.clientX, y: e.originalEvent.clientY };
            showAircraftTip(ac, tipTarget.x, tipTarget.y);
        } else if (tipTarget && tipTarget.ac) {
            tipTarget = null;
            tipEl.hidden = true;
        }
    });
    map.on('mouseout', () => { if (tipTarget && tipTarget.ac) { tipTarget = null; tipEl.hidden = true; } });
    map.on('click', e => select(nearest(e.containerPoint.x, e.containerPoint.y)));

    // UI tooltips from data-tip attributes.
    document.addEventListener('mouseover', e => {
        const el = e.target.closest && e.target.closest('[data-tip]');
        if (!el || el.closest('#map')) return;
        tipTarget = { el };
        tipEl.innerHTML = el.dataset.tip;
        const r = el.getBoundingClientRect();
        placeTip(r.left, r.bottom - 8);
    });
    document.addEventListener('mouseout', e => {
        if (tipTarget && tipTarget.el && e.target.closest && e.target.closest('[data-tip]') === tipTarget.el &&
            !tipTarget.el.contains(e.relatedTarget)) { tipTarget = null; tipEl.hidden = true; }
    });

    // ─── Layer toggles and theme ────────────────────────────────────────────
    function applyLayers() {
        document.querySelectorAll('#layers button').forEach(b => b.classList.toggle('on', !!layers[b.dataset.layer]));
        for (const m of rxMarkers.values()) layers.receivers ? m.addTo(rxGroup) : m.remove();
        for (const l of links.values()) layers.links ? l.addTo(linkGroup) : l.remove();
        trailsFull = true;
    }
    document.querySelectorAll('#layers button').forEach(b => {
        b.onclick = () => { layers[b.dataset.layer] = !layers[b.dataset.layer]; store.set('layers', layers); applyLayers(); };
    });
    applyLayers();
    document.querySelectorAll('canvas.src-icon').forEach(c => {
        c.width = c.height = 24 * (window.devicePixelRatio || 1);
        paintIcon(c, Number(c.dataset.src), 20000, 45);
    });

    const themeBtn = $('theme');
    function setTheme(dark) {
        document.body.classList.toggle('dark-mode', dark);
        themeBtn.querySelector('use').setAttribute('href', dark ? '#i-sun' : '#i-moon');
    }
    setTheme(store.get('dark', window.matchMedia && matchMedia('(prefers-color-scheme: dark)').matches));
    themeBtn.onclick = () => { const d = !document.body.classList.contains('dark-mode'); store.set('dark', d); setTheme(d); };

    // Test and debugging hooks.
    window.mlat = { map, tracks, receivers, perf, layers, select: icao => select(tracks.get(icao) || null), serverNow };

    connect();
})();
