// Tests for the FIS-B decoder and map layer (fisb.js). Runs in CI (web_ui_test job).
// Run: node --test firmware/adsbee_1090/esp/main/server/web/test/fisb.test.js
//
// fisb_data/sjc_20261011.txt.gz: uplinks received near San Jose, CA on 2026-10-11 10:08-10:25 UTC, repeats removed.
// Expected values come from aviationweather.gov, tfr.faa.gov and the Iowa State NEXRAD mosaic for the same time.
'use strict';
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const path = require('node:path');
const zlib = require('node:zlib');
const Fisb = require('../fisb.js');

const DATA = path.join(__dirname, 'fisb_data');
const LINES = zlib.gunzipSync(fs.readFileSync(path.join(DATA, 'sjc_20261011.txt.gz'))).toString().split('\n').filter(Boolean);
const REFERENCE = JSON.parse(fs.readFileSync(path.join(DATA, 'nexrad_reference.json'), 'utf8'));

function replay(listener) {
    const decoder = new Fisb.Decoder();
    if (listener) decoder.on(listener);
    for (const line of LINES) {
        const frame = Fisb.parseRawLine(line);
        frame.meta.timestampMs = +line.split(' ')[0];
        decoder.ingestUplink(frame.payload, frame.meta);
    }
    return decoder;
}
Fisb.setStations(require('../fisb_stations.js'));
const reportLists = [];
const decoder = replay((kind, item) => { if (kind === 'crl') reportLists.push(item); });
const text = (key) => decoder.texts.get(key).text.replace(/\s+/g, ' ');
const report = (pattern) => [...decoder.reports.values()].find((r) => pattern.test(r.text));

function distanceNm(a, b) {
    return Math.hypot((a[0] - b[0]) * 60, (a[1] - b[1]) * 60 * Math.cos(a[0] * Math.PI / 180));
}
// Largest distance from a vertex of one outline to the nearest vertex of the other.
function outlineDistanceNm(p, q) {
    const far = (from, to) => Math.max(...from.map((a) => Math.min(...to.map((b) => distanceNm(a, b)))));
    return Math.max(far(p, q), far(q, p));
}

test('deinterleave follows the uplink block layout', () => {
    const encoded = new Uint8Array(552);
    for (let block = 0; block < 6; block++) for (let i = 0; i < 92; i++) encoded[i * 6 + block] = i < 72 ? block * 72 + i : 0xFF;
    const payload = Fisb.deinterleave(encoded);
    assert.strictEqual(payload.length, 432);
    payload.forEach((value, index) => assert.strictEqual(value, index & 0xFF));
    assert.deepStrictEqual(Fisb.deinterleave(Buffer.from(encoded).toString('hex')), payload);
    assert.strictEqual(Fisb.deinterleave(new Uint8Array(100)), null);
});

test('parseRawLine accepts only uplink lines', () => {
    const frame = Fisb.parseRawLine(LINES[0]);
    assert.strictEqual(frame.payload.length, 432);
    assert.ok(frame.meta.rssiDbm < 0 && frame.meta.rssiDbm > -120);
    assert.strictEqual(Fisb.parseRawLine('#MDS*8DA561FD991137B418042EC0D8E4;(1,-73,18,00000C66C1A31376)'), null);
    assert.strictEqual(Fisb.parseRawLine('#UAT*-00AB;(-70,3,0)'), null);
    assert.strictEqual(Fisb.parseRawLine('#UAT*+ABCD;(-70,3,0)'), null);
});

test('ground stations', () => {
    // Both sites are FAA ADS-B ground stations in the San Jose area; the position-valid bit is clear on air.
    const stations = [...decoder.stations.values()].sort((a, b) => a.lon - b.lon);
    assert.strictEqual(stations.length, 2);
    assert.ok(Math.abs(stations[0].lat - 37.4104) < 1e-4 && Math.abs(stations[0].lon + 122.3070) < 1e-4);
    assert.ok(Math.abs(stations[1].lat - 37.3227) < 1e-4 && Math.abs(stations[1].lon + 121.7550) < 1e-4);
    assert.deepStrictEqual(stations.map((s) => s.tisbSiteId), [9, 11]);
    for (const s of stations) {
        assert.ok(s.utcCoupled && s.appDataValid && s.slot < 32 && s.rssiDbm < 0);
    }
});

test('METAR and TAF text matches aviationweather.gov', () => {
    assert.strictEqual(text('METAR KSJC'), 'METAR KSJC 110953Z AUTO 13003KT 10SM CLR 11/07 A2954 RMK AO2 SLP001 T01110072=');
    assert.strictEqual(text('METAR KSFO'), 'METAR KSFO 110956Z 27007KT 10SM FEW016 13/09 A2952 RMK AO2 SLP997 T01280094=');
    assert.strictEqual(text('METAR KMRY'), 'METAR KMRY 110954Z AUTO 24004KT 10SM OVC021 14/09 A2957 RMK AO2 SLP025 T01440089=');
    assert.strictEqual(text('TAF KSFO'),
        'TAF.AMD KSFO 110855Z 1109/1212 26010KT P6SM SCT250 FM112000 25015KT P6SM FEW250 FM120100 27010KT P6SM SKC=');
    const ksjc = decoder.texts.get('METAR KSJC');
    assert.strictEqual(ksjc.timeMs, Date.UTC(2026, 9, 11, 9, 53));
    assert.strictEqual(ksjc.expiresMs, Date.UTC(2026, 9, 11, 11, 53));
    assert.strictEqual(ksjc.category, 'VFR');
    assert.strictEqual(decoder.texts.get('METAR KMRY').category, 'MVFR');
    // TAF validity 1109/1212 ends on the 12th at 12:00.
    assert.strictEqual(decoder.texts.get('TAF KSFO').expiresMs, Date.UTC(2026, 9, 12, 12, 0));
});

test('winds aloft keep one entry per forecast time', () => {
    const winds = [...decoder.texts.values()].filter((t) => t.kind === 'WINDS' && t.id === 'SFO');
    assert.ok(winds.length >= 2);
    assert.match(winds[0].text, /^WINDS SFO \d{6}Z\s+FT 3000 6000/);
    assert.strictEqual(new Set(winds.map((w) => w.timeMs)).size, winds.length);
    // Forecast valid 12:00 UTC, same groups as the aviationweather.gov winds aloft table.
    const noon = winds.find((w) => w.timeMs === Date.UTC(2026, 9, 11, 12));
    assert.strictEqual(noon.text.split('\n')[1].trim(), '3507 9900+10 2511+06 2214-02 2716-12 2820-24 263029 263933 274144');
});

test('flight category', () => {
    const category = (body) => Fisb.flightCategory(`METAR KXXX 110953Z ${body} 11/07 A2954 RMK AO2`);
    assert.strictEqual(category('13003KT 10SM CLR'), 'VFR');
    assert.strictEqual(category('13003KT 10SM BKN035'), 'VFR');
    assert.strictEqual(category('13003KT 10SM BKN030'), 'MVFR');
    assert.strictEqual(category('13003KT 5SM BR SCT017'), 'MVFR');
    assert.strictEqual(category('13003KT 2 1/2SM BR FEW008 BKN020'), 'IFR');
    assert.strictEqual(category('13003KT 10SM RA BKN009'), 'IFR');
    assert.strictEqual(category('13003KT 10SM RA BKN004 BKN029'), 'LIFR');
    assert.strictEqual(category('13003KT 3/4SM BR OVC010'), 'LIFR');
    assert.strictEqual(category('13003KT M1/4SM FG VV001'), 'LIFR');
    assert.strictEqual(category('13003KT'), null);
    // Cloud groups after RMK are remarks.
    assert.strictEqual(Fisb.flightCategory('METAR KXXX 110953Z 13003KT 10SM CLR 11/07 A2954 RMK OVC003'), 'VFR');
});

test('segmented TFR text is joined cleanly and its circle matches the NOTAM', () => {
    // FDC 6/6741, San Francisco Fleet Week: 5 NM around 374900N1222536W, surface to 15000 ft. tfr.faa.gov draws the same ring.
    const tfr = report(/^NOTAM-TFR 6\/6741 /);
    assert.match(tfr.text, /WI AN AREA DEFINED AS 5NM RADIUS OF 374900N1222536W \(SAU100005\.1\) SFC-15000FT MSL/);
    assert.match(tfr.text, /UNTIL 2610102359 UTC \(1659 LOCAL 10\/10\/26\), AND 2610111800 UTC/);
    assert.doesNotMatch(tfr.text, /[\x00-\x09\x0B-\x1F]/);
    const outlines = Fisb.reportOutlines(tfr);
    assert.strictEqual(outlines.length, 1);
    assert.strictEqual(outlines[0].shape, 'circle');
    assert.ok(distanceNm(outlines[0].center, [37 + 49 / 60, -(122 + 25 / 60 + 36 / 3600)]) < 0.05);
    assert.strictEqual(outlines[0].radiusNm, 5);
    assert.deepStrictEqual([outlines[0].lo, outlines[0].hi], [0, 15000]);
    assert.deepStrictEqual(outlines[0].times[3], [Date.UTC(2026, 9, 11, 18, 0), Date.UTC(2026, 9, 11, 23, 59)]);
});

test('convective SIGMET outline matches aviationweather.gov', () => {
    const sigmet = report(/CONVECTIVE SIGMET 37W/);
    assert.match(sigmet.text, /^WST KMKC 110954 CONVECTIVE SIGMET 37W\nVALID UNTIL 1155Z\nAZ NV CA\n/);
    const published = [[36.918, -112.69], [34.153, -114.771], [33.612, -117.23], [35.169, -117.592], [36.187, -116.428], [36.918, -112.69]];
    const shape = sigmet.shapes[0];
    assert.strictEqual(shape.shape, 'polygon');
    assert.strictEqual(shape.points.length, published.length);
    assert.ok(outlineDistanceNm(shape.points, published) < 1);
    assert.strictEqual(shape.hi, 30000);
    assert.strictEqual(shape.startMs, Date.UTC(2026, 9, 11, 9, 55));
    assert.strictEqual(shape.stopMs, Date.UTC(2026, 9, 11, 11, 55));
});

test('G-AIRMET outlines match aviationweather.gov', () => {
    const at = (element, startMs, near) => [...decoder.reports.values()].filter((r) => r.productId === 14)
        .flatMap((r) => r.shapes).find((s) => s.element === element && s.startMs === startMs && distanceNm(s.points[0], near) < 5);
    // Mountain obscuration over the Bay Area, valid 09:00 UTC: "MTNS OBSC BY CLDS BR".
    const mountains = at('MTN', Date.UTC(2026, 9, 11, 9), [38.35, -122.40]);
    assert.ok(outlineDistanceNm(mountains.points,
        [[38.35, -122.40], [38.18, -121.97], [37.53, -121.63], [36.98, -121.56], [36.52, -121.41], [36.27, -121.64], [38.22, -122.99]]) < 1);
    assert.deepStrictEqual(mountains.conditions, ['BR', 'CLDS']);
    assert.strictEqual(mountains.stopMs, Date.UTC(2026, 9, 11, 12));
    // IFR off southern California, valid 09:00 UTC: "CIG BLW 010 VIS BLW 3SM PCPN BR FG".
    const ifr = at('IFR', Date.UTC(2026, 9, 11, 9), [34.25, -117.72]);
    assert.ok(outlineDistanceNm(ifr.points, [[34.25, -117.72], [33.79, -116.75], [32.68, -116.63], [32.44, -117.22], [30.56, -120.77],
        [31.40, -121.10], [32.16, -120.05], [32.90, -119.23], [33.69, -118.78]]) < 1);
    assert.deepStrictEqual(ifr.conditions, ['PCPN', 'BR', 'FG', 'CLDS']);
});

test('airport NOTAMs carry the airport position', () => {
    const notam = report(/^NOTAM-D KSFO\./);
    const point = notam.shapes.find((s) => s.shape === 'point');
    assert.strictEqual(point.label, 'KSFO');
    assert.ok(distanceNm(point.points[0], [37.619, -122.375]) < 0.5);
    assert.ok(distanceNm(decoder.airports.get('KSFO'), Fisb.stationPosition('KSFO')) < 1);
});

test('block geometry', () => {
    // Block 0 touches the equator and the prime meridian; 450 blocks of 48 arc minutes circle the globe.
    assert.deepStrictEqual(Fisb.blockBounds(0, 0, false), { north: 4 / 60, west: 0, binLat: 1 / 60, binLon: 1.5 / 60 });
    const sanJose = Fisb.blockBounds(559 * 450 + 297, 0, false);
    assert.ok(Math.abs(sanJose.north - 37.3333) < 1e-4 && Math.abs(sanJose.west + 122.4) < 1e-9);
    // A medium resolution block is 5 times larger and extends south and east from the same corner.
    const medium = Fisb.blockBounds(559 * 450 + 295, 1, false);
    assert.ok(Math.abs(medium.north - 37.3333) < 1e-4 && Math.abs(medium.west + 124) < 1e-9);
    assert.ok(Math.abs(medium.binLat - 5 / 60) < 1e-12 && Math.abs(medium.binLon - 7.5 / 60) < 1e-12);
    assert.strictEqual(Fisb.blockBounds(405000, 0, false).binLon, 3 / 60);
});

// Calls visit(lat, lon, level) with the center of every bin of a grid product.
function eachBin(productId, visit) {
    for (const block of decoder.grids.get(productId).values()) {
        if (!block.bins) continue;
        const b = Fisb.blockBounds(block.blockNumber, block.scale, block.south);
        block.bins.forEach((level, i) => visit(b.north - ((i >> 5) + 0.5) * b.binLat, b.west + ((i & 31) + 0.5) * b.binLon, level));
    }
}

// Share of bins at or above minLevel that lie in a reference cell at or above minReference.
function radarAgreement(productId, reference, minLevel, minReference, shiftLat, shiftLon) {
    let bins = 0, hits = 0;
    eachBin(productId, (lat, lon, level) => {
        if (level < minLevel) return;
        const row = reference.rows[Math.floor((reference.north - lat - shiftLat) / reference.cell)];
        const cell = row && row[Math.floor((lon + shiftLon - reference.west) / reference.cell)];
        if (cell === undefined) return;
        bins++;
        if (+cell >= minReference) hits++;
    });
    return { bins, share: hits / bins };
}

test('CONUS NEXRAD echoes lie where the national mosaic has echoes', () => {
    const blocks = [...decoder.grids.get(64).values()];
    assert.ok(blocks.every((b) => b.scale === 1 && b.timeMs === Date.UTC(2026, 9, 11, 10, 20)));
    // The image spans 20-53 N, 132-60 W.
    const bounds = blocks.map((b) => Fisb.blockBounds(b.blockNumber, 1, false));
    assert.ok(Math.abs(Math.max(...bounds.map((b) => b.north)) - 53) < 1e-9);
    assert.ok(Math.abs(Math.min(...bounds.map((b) => b.north - 4 * b.binLat)) - 20) < 1e-9);
    assert.ok(Math.abs(Math.min(...bounds.map((b) => b.west)) + 132) < 1e-9);
    assert.ok(Math.abs(Math.max(...bounds.map((b) => b.west + 32 * b.binLon)) + 60) < 1e-9);

    const here = radarAgreement(64, REFERENCE.conus, 3, 2, 0, 0);
    assert.ok(here.bins > 5000 && here.share > 0.95, JSON.stringify(here));
    const strong = radarAgreement(64, REFERENCE.conus, 5, 4, 0, 0);
    assert.ok(strong.bins > 500 && strong.share > 0.95, JSON.stringify(strong));
    // The match is lost when the image is moved 3 degrees in any direction.
    for (const [lat, lon] of [[3, 0], [-3, 0], [0, 3], [0, -3]]) {
        assert.ok(radarAgreement(64, REFERENCE.conus, 5, 4, lat, lon).share < 0.7);
    }
});

test('regional NEXRAD echoes lie where the mosaic has echoes', () => {
    const blocks = [...decoder.grids.get(63).values()];
    assert.ok(blocks.every((b) => b.scale === 0));
    assert.ok(blocks.filter((b) => b.bins).length > 50);
    const here = radarAgreement(63, REFERENCE.regional, 2, 2, 0, 0);
    assert.ok(here.bins > 500 && here.share > 0.95, JSON.stringify(here));
    assert.ok(radarAgreement(63, REFERENCE.regional, 2, 2, 0.75, 0).share < 0.8);
    assert.ok(radarAgreement(63, REFERENCE.regional, 2, 2, 0, -0.75).share < 0.8);
    // No rain over the San Francisco Bay Area at the time.
    eachBin(63, (lat, lon, level) => {
        if (lat > 37 && lat < 38 && lon > -122.6 && lon < -121.6) assert.ok(level < 2);
    });
});

test('other grid products decode to full blocks', () => {
    for (const productId of [70, 71, 84, 90, 91, 103]) {
        const blocks = [...decoder.grids.get(productId).values()];
        assert.ok(blocks.length > 0, `product ${productId}`);
        for (const b of blocks) {
            if (b.bins) assert.strictEqual(b.bins.length, 128);
            if (productId === 70 || productId === 90) assert.ok(b.altitudeFt >= 2000 && b.altitudeFt <= 16000);
            if (productId === 71 || productId === 91) assert.ok(b.altitudeFt >= 18000 && b.altitudeFt <= 24000);
        }
    }
});

test('current report list', () => {
    // The two stations list G-AIRMETs within 250 and 375 NM.
    const gairmet = reportLists.find((l) => l.productId === 14 && l.rangeNm === 375);
    assert.ok(reportLists.some((l) => l.productId === 14 && l.rangeNm === 250));
    assert.strictEqual(gairmet.rangeNm, 375);
    assert.ok(gairmet.reports.length > 50 && gairmet.reports.every((r) => r.graphic && !r.text));
    // Every listed G-AIRMET was decoded.
    for (const r of gairmet.reports) assert.ok(decoder.reports.has(`14/${r.year}/${r.number}`));
});

test('every product in the capture is decoded', () => {
    assert.deepStrictEqual(Object.keys(decoder.stats.products).map(Number).sort((a, b) => a - b),
        [8, 12, 13, 14, 18, 19, 63, 64, 70, 71, 84, 90, 91, 103, 413]);
    assert.deepStrictEqual(decoder.stats.unknownProducts, {});
    assert.deepStrictEqual(decoder.stats.unknownFrames, {});
    assert.strictEqual(decoder.stats.errors, 0);
    assert.strictEqual(decoder.stats.uplinks, LINES.length);
});

test('reports expire and listeners hear about it', () => {
    const d = replay();
    const events = [];
    d.on((kind) => events.push(kind));
    const start = d.timeMs;
    assert.ok(d.texts.has('METAR KSJC') && d.grids.get(63).size > 0 && d.stations.size > 0);
    d.expire(start + 10 * 60000);
    assert.strictEqual(d.stations.size, 0);
    assert.ok(d.grids.get(63).size > 0);
    d.expire(start + 80 * 60000);
    assert.strictEqual(d.grids.get(63).size, 0);
    assert.strictEqual([...d.reports.values()].filter((r) => r.productId === 14).length, 0);
    d.expire(Date.UTC(2026, 9, 11, 11, 54));
    assert.ok(!d.texts.has('METAR KSJC') && d.texts.has('TAF KSJC'));
    d.expire(Date.UTC(2026, 9, 13));
    assert.strictEqual(d.texts.size, 0);
    assert.ok(events.length >= 4 && events.every((kind) => kind === 'expire'));
});

test('change events and unsubscribe', () => {
    const d = new Fisb.Decoder();
    const kinds = new Set();
    const off = d.on((kind, item) => { kinds.add(kind); assert.ok(item || kind === 'expire'); });
    for (const line of LINES.slice(0, 300)) {
        const frame = Fisb.parseRawLine(line);
        d.ingestUplink(frame.payload, { timestampMs: +line.split(' ')[0] });
    }
    for (const kind of ['station', 'text', 'report', 'grid', 'crl']) assert.ok(kinds.has(kind), kind);
    off();
    kinds.clear();
    d.ingestUplink(Fisb.parseRawLine(LINES[300]).payload, { timestampMs: +LINES[300].split(' ')[0] });
    assert.strictEqual(kinds.size, 0);
});

// Builds a payload holding one product frame.
function payloadWith(productId, body) {
    const p = new Uint8Array(432);
    p.set([0x35, 0x14, 0xC9, 0x52, 0xD6, 0x5C, 0xA0, 0xB0]);
    const length = 4 + body.length;
    // Header: product id and time 10:20.
    p.set([length >> 1, (length & 1) << 7, productId >> 6, (productId & 0x3F) << 2, (10 << 2) | (20 >> 4), (20 & 0x0F) << 4], 8);
    p.set(body, 14);
    return p;
}

test('unknown products are counted', () => {
    const d = new Fisb.Decoder();
    d.ingestUplink(payloadWith(999, [1, 2, 3]), { timestampMs: Date.UTC(2026, 9, 11, 10, 21) });
    d.ingestUplink(payloadWith(999, [1, 2, 3]), { timestampMs: Date.UTC(2026, 9, 11, 10, 21) });
    assert.deepStrictEqual(d.stats.unknownProducts, { 999: 2 });
    assert.deepStrictEqual(d.stats.products, {});
});

test('product time resolves around midnight', () => {
    const d = new Fisb.Decoder();
    // A block of product 63 stamped 10:20, received a day boundary apart.
    const body = [0x80, 0, 0, ...new Array(8).fill(0xF8)];
    d.ingestUplink(payloadWith(63, body), { timestampMs: Date.UTC(2026, 9, 11, 10, 21) });
    assert.strictEqual(d.grids.get(63).get('0').timeMs, Date.UTC(2026, 9, 11, 10, 20));
    assert.strictEqual(Fisb.resolveTime(Date.UTC(2026, 0, 1, 0, 5), { hour: 23, minute: 58 }), Date.UTC(2025, 11, 31, 23, 58));
    assert.strictEqual(Fisb.resolveTime(Date.UTC(2026, 11, 31, 23, 58), { hour: 0, minute: 3 }), Date.UTC(2027, 0, 1, 0, 3));
    assert.strictEqual(Fisb.resolveTime(Date.UTC(2026, 2, 1, 0, 5), { day: 28, hour: 23, minute: 50 }), Date.UTC(2026, 1, 28, 23, 50));
    assert.strictEqual(Fisb.resolveTime(Date.UTC(2026, 0, 2), { month: 12, day: 30, hour: 12, minute: 0 }), Date.UTC(2025, 11, 30, 12));
});

test('malformed input never throws', (t) => {
    const d = new Fisb.Decoder();
    assert.strictEqual(d.ingestUplink(null), null);
    assert.strictEqual(d.ingestUplink(new Uint8Array(10)), null);
    let seed = 12345;
    const random = () => (seed = (seed * 1103515245 + 12345) & 0x7FFFFFFF) >> 16 & 0xFF;
    // Random payloads, and real payloads with random bytes overwritten.
    for (let n = 0; n < 3000; n++) {
        const p = n % 2 ? Fisb.parseRawLine(LINES[n % LINES.length]).payload : new Uint8Array(432);
        const changes = n % 2 ? 1 + random() % 12 : 432;
        for (let k = 0; k < changes; k++) p[n % 2 ? 8 + (random() * 256 + random()) % 424 : k] = random();
        p[6] |= 0x20;
        d.ingestUplink(p, { timestampMs: Date.UTC(2026, 9, 11, 10, 0) + n * 1000 });
    }
    assert.strictEqual(d.stats.uplinks, 3000);
    // Whatever was stored can be drawn.
    const { L, map, document } = fakeBrowser();
    globalThis.document = document;
    t.after(() => { delete globalThis.document; });
    Fisb.createLayer(L, d, { stationsUrl: null }).addTo(map);
    d.expire(Date.UTC(2027, 0, 1));
});

// Minimal Leaflet and DOM stand-ins that record what the layer draws.
function fakeBrowser() {
    const made = [];
    const element = (tag) => ({
        tag, children: [], style: {}, textContent: '',
        classList: { names: new Set(), toggle(name, on) { if (on) this.names.add(name); else this.names.delete(name); } },
        setAttribute(name, value) { this[name] = value; },
        appendChild(child) { this.children.push(child); return child; },
        remove() {},
        getContext: () => ({ clearRect() {}, fillRect(x, y, w, h) { made.push({ type: 'rect', color: this.fillStyle, x, y, w, h }); } }),
    });
    const shape = (type) => (where, options) => {
        const object = {
            type, where, options,
            bindTooltip(c) { this.tooltip = c; return this; },
            bindPopup(c) { this.popup = c; return this; },
            bringToBack() {},
        };
        made.push(object);
        return object;
    };
    const group = () => ({
        layers: new Set(),
        addLayer(l) { this.layers.add(l); return this; },
        removeLayer(l) { this.layers.delete(l); return this; },
        eachLayer(visit) { this.layers.forEach(visit); },
        onAdd() {}, onRemove() {}, bringToBack() {},
        addTo(map) { this.onAdd(map); return this; },
    });
    const L = {
        layerGroup: group, featureGroup: group,
        circleMarker: shape('circleMarker'), circle: shape('circle'), polygon: shape('polygon'), polyline: shape('polyline'), marker: shape('marker'),
        divIcon: (options) => options,
        control: () => ({ addTo(map) { this.box = this.onAdd(map); return this; }, remove() {} }),
        Layer: { extend: (methods) => function () { Object.assign(this, methods); } },
        DomUtil: { create: (tag) => element(tag), setPosition() {} },
        DomEvent: { disableClickPropagation() {} },
    };
    // 100 pixels per degree, north up, top left corner at 40 N 125 W.
    const map = {
        getPane: () => ({ style: {} }), on() {}, off() {},
        getSize: () => ({ x: 900, y: 700 }),
        getBounds: () => ({ getNorth: () => 40, getSouth: () => 33, getWest: () => -125, getEast: () => -116 }),
        containerPointToLayerPoint: (p) => p,
        latLngToContainerPoint: ([lat, lon]) => ({ x: (lon + 125) * 100, y: (40 - lat) * 100 }),
    };
    const document = { createElement: element, createTextNode: (t) => ({ textContent: t }), getElementById: () => null, head: element('head') };
    return { L, map, document, made };
}

const flatten = (node) => (node.textContent || '') + (node.children || []).map(flatten).join('');
const tooltip = (object) => (object.tooltip ? flatten(object.tooltip()) : '');

test('map layer draws airports, areas, ground stations and radar', (t) => {
    const { L, map, document, made } = fakeBrowser();
    globalThis.document = document;
    t.after(() => { delete globalThis.document; });
    const layer = Fisb.createLayer(L, decoder, { stationsUrl: null });
    layer.addTo(map);
    // Nine buttons and the altitude selector.
    assert.strictEqual(layer.control.box.children.length, 10);

    // San Jose: green (VFR) marker at the airport with the METAR in its tooltip and the TAF in its popup.
    const ksjc = made.find((o) => o.type === 'circleMarker' && /METAR KSJC/.test(tooltip(o)));
    assert.ok(distanceNm(ksjc.where, [37.363, -121.929]) < 1);
    assert.strictEqual(ksjc.options.fillColor, Fisb.CATEGORY_COLORS.VFR);
    assert.match(flatten(ksjc.popup()), /TAF KSJC 110520Z/);
    const ksfo = made.find((o) => o.type === 'circleMarker' && /METAR KSFO/.test(tooltip(o)));
    assert.match(flatten(ksfo.popup()), /WINDS SFO \d{6}Z\n3000    6000    9000    12000 .*\n\d{4}    \d{4}[+-]\d\d \d{4}[+-]\d\d /);
    const kmry = made.find((o) => o.type === 'circleMarker' && /METAR KMRY/.test(tooltip(o)));
    assert.strictEqual(kmry.options.fillColor, Fisb.CATEGORY_COLORS.MVFR);

    // Fleet Week TFR: one 5 NM circle, with the NOTAM text in its popup.
    const circles = made.filter((o) => o.type === 'circle' && /6\/6741/.test(tooltip(o)));
    assert.strictEqual(circles.length, 1);
    assert.strictEqual(circles[0].options.radius, 5 * 1852);
    assert.ok(distanceNm(circles[0].where, [37.8167, -122.4267]) < 0.05);
    assert.match(flatten(circles[0].popup()), /FLEET WEEK AIR SHOW/);
    assert.match(tooltip(circles[0]), /SFC–15000 ft/);
    // Received text reaches the page as text nodes, never as HTML strings.
    for (const o of made) {
        if (o.tooltip) assert.strictEqual(typeof o.tooltip, 'function');
        if (o.popup) assert.strictEqual(typeof o.popup, 'function');
    }

    // An area is a pointer-transparent shape plus an unseen wide outline carrying the tooltip.
    const sigmet = made.find((o) => o.type === 'polyline' && /^WST KMKC 110954 CONVECTIVE SIGMET 37W · 30000 ft/.test(tooltip(o)));
    assert.strictEqual(sigmet.where.length, 7);
    assert.deepStrictEqual(sigmet.where[6], sigmet.where[0]);
    assert.ok(sigmet.options.weight >= 12 && sigmet.options.opacity === 0 && sigmet.options.fill === false);
    const fill = made.find((o) => o.type === 'polygon' && o.where.length === 6 && o.where[0] === sigmet.where[0]);
    assert.ok(fill.options.interactive === false && fill.options.weight === 2 && !fill.tooltip);
    const wideCircle = made.find((o) => o.type === 'circle' && o.where === circles[0].where && o !== circles[0]);
    assert.ok(circles[0].options.opacity === 0 && wideCircle.options.interactive === false);
    assert.strictEqual(made.filter((o) => o.type === 'marker').length, 2);

    // Radar: a block is drawn as runs of bins inside the block's rectangle.
    layer.parts.radar._map = map;
    layer.parts.radar.onAdd(map);
    const rects = made.filter((o) => o.type === 'rect');
    assert.ok(rects.length > 100);
    assert.ok(rects.every((r) => Fisb.RADAR_COLORS.includes(r.color) && r.w > 0 && r.h > 0));
    assert.ok(rects.every((r) => r.x >= -400 && r.x <= 1300 && r.y >= -40 && r.y <= 740));
    // Radar, airports, areas and ground stations start shown; the other parts start hidden.
    const shown = Object.keys(layer.parts).filter((name) => layer.layers.has(layer.parts[name]));
    assert.deepStrictEqual(shown, ['radar', 'airports', 'areas', 'stations']);

    // Hiding a part removes it from the group; a second refresh draws nothing new.
    layer.setVisible('areas', false);
    assert.ok(!layer.layers.has(layer.parts.areas));
    const count = made.filter((o) => o.type !== 'rect').length;
    layer.refresh();
    assert.strictEqual(made.filter((o) => o.type !== 'rect').length, count);
});

// ─── Synthetic uplinks ────────────────────────────────────────────────────────
const DLAC = '\x03ABCDEFGHIJKLMNOPQRSTUVWXYZ\x1A\t\x1E\n| !"#$%&\'()*+,-./0123456789:;<=>?';
// Text in the six-bit character set, four characters in three bytes.
function dlacBytes(text) {
    const out = [];
    for (let i = 0; i < text.length; i += 4) {
        const c = [0, 1, 2, 3].map((k) => (i + k < text.length ? DLAC.indexOf(text[i + k]) : 0));
        out.push((c[0] << 2) | (c[1] >> 4), ((c[1] & 0x0F) << 4) | (c[2] >> 2), ((c[2] & 0x03) << 6) | c[3]);
    }
    return out;
}
// Information frame holding one unsegmented product stamped 10:00 UTC.
function productFrame(productId, payload) {
    const data = [productId >> 6, ((productId & 0x3F) << 2), 10 << 2, 0, ...payload];
    return [data.length >> 1, ((data.length & 1) << 7), ...data];
}
// Current report list frame. reports: [[year, number], ...].
function crlFrame(productId, reports, flags = 0) {
    const data = [productId >> 3, ((productId & 0x07) << 5) | flags, 75, reports.length];
    for (const [year, number] of reports) data.push(year, 0x80 | (number >> 8), number & 0xFF);
    return [data.length >> 1, ((data.length & 1) << 7) | 14, ...data];
}
// Uplink payload from a ground station at the given latitude.
function uplink(frames, stationLat = 37.5) {
    const p = new Uint8Array(432);
    const lat = Math.round(stationLat * 16777216 / 360), lon = Math.round(238 * 16777216 / 360);
    p.set([lat >> 15, (lat >> 7) & 0xFF, ((lat & 0x7F) << 1) | (lon >> 23), (lon >> 15) & 0xFF, (lon >> 7) & 0xFF, ((lon & 0x7F) << 1) | 1, 0xA0, 0]);
    p.set(frames.flat(), 8);
    return p;
}
const T0 = Date.UTC(2026, 9, 12, 10, 1);
// Text product record: report number, year 26, active.
const textReport = (number, text) => {
    const body = dlacBytes(text);
    const length = 5 + body.length;
    return [0x20, 0x10, ...dlacBytes('KSFO').slice(0, 3), 0, length >> 8, length & 0xFF, number >> 6, ((number & 0x3F) << 2), (26 << 3) | 0x04, ...body];
};
// Grid block with its north west corner at 36.067 N 120 W. level: altitude index or scale. runs: run-length bytes.
const gridBlock = (level, runs) => [0x80 | (level << 4) | (243300 >> 16), (243300 >> 8) & 0xFF, 243300 & 0xFF, ...runs];

test('pilot report fields', () => {
    const p = Fisb.parsePirep('PIREP LAS 120145Z LAS UA /OV LAS213045/TM 0145/FL150/TP E145/TA M09/TB MOD CHOP/IC LGT RIME');
    assert.deepStrictEqual(p.fields, { OV: 'LAS213045', TM: '0145', FL: '150', TP: 'E145', TA: 'M09', TB: 'MOD CHOP', IC: 'LGT RIME' });
    assert.deepStrictEqual([p.station, p.urgent, p.altitudeFt, p.severity], ['LAS', false, 15000, 2]);
    // A slash inside a field stays in it; an unknown altitude gives none.
    const q = Fisb.parsePirep('PIREP SFO 120150Z SFO UUA /OV SFO/TM 0150/FLUNKN/TP B738/SK BKN030-TOP050/OVC080/TB SEV/RM LLWS +/-10 KT');
    assert.deepStrictEqual([q.urgent, q.altitudeFt, q.severity, q.fields.SK, q.fields.RM], [true, undefined, 3, 'BKN030-TOP050/OVC080', 'LLWS +/-10 KT']);
    assert.strictEqual(Fisb.parsePirep('PIREP SNS 120150Z SNS UA /OV SNS/TM 0150/FL040/TP C172/TB NEG/IC NEG').severity, 0);
});

test('pilot report positions match aviationweather.gov', () => {
    // Location field, reporting station and the position aviationweather.gov gave the same report.
    const cases = [
        ['MZB', 'SAN', 32.7822, -117.2254],
        ['RNM270003', 'RNM', 33.0496, -116.9735],
        ['BOI117049', 'BOI', 42.9837, -115.3905],
        ['YKM270050', 'YKM', 46.8627, -121.5804],
        ['RAP084081', 'RAP', 43.7968, -101.1591],
        ['KRNO167009', 'RNO', 39.3536, -119.7334],
        ['KFAR', 'FAR', 46.9207, -96.8158],
    ];
    for (const [ov, station, lat, lon] of cases) {
        const position = Fisb.pirepPosition(Fisb.parsePirep(`PIREP ${station} 120150Z ${station} UA /OV ${ov}/TM 0150/FL100/TP C172`), null);
        assert.ok(distanceNm(position, [lat, lon]) < 3, `${ov}: ${position}`);
    }
    const at = (ov, station = 'SFO') => Fisb.pirepPosition(Fisb.parsePirep(`PIREP ${station} 120150Z ${station} UA /OV ${ov}/TM 0150`), null);
    // Bearings are magnetic: the Oakland navaid is aligned 17 degrees east of true north.
    const oak = at('OAK'), north = at('OAK360020');
    const [northNm, eastNm] = [(north[0] - oak[0]) * 60, (north[1] - oak[1]) * 60 * Math.cos(oak[0] * Math.PI / 180)];
    assert.ok(Math.abs(Math.hypot(northNm, eastNm) - 20) < 0.2 && Math.abs(Math.atan2(eastNm, northNm) * 180 / Math.PI - 17) < 1);
    // Distance and compass direction, with and without a space.
    assert.ok(distanceNm(at('10 E OAK'), at('OAK090010')) < 0.1);
    assert.ok(distanceNm(at('30W PDX'), at('PDX270030')) < 0.1);
    // A route uses its first point; an unknown place falls back to the reporting station.
    assert.deepStrictEqual(at('SNS-OAK'), at('SNS'));
    assert.deepStrictEqual(at('GEELA'), at('SFO'));
    assert.deepStrictEqual(at('ZZZ090010'), at('SFO'));
    assert.strictEqual(at('ZZZ', 'ZZZ'), null);
});

test('station file without navaids still loads', (t) => {
    const data = require('../fisb_stations.js');
    t.after(() => Fisb.setStations(data));
    Fisb.setStations(data.split('|')[0]);
    assert.ok(distanceNm(Fisb.stationPosition('KSJC'), [37.363, -121.929]) < 1);
    const p = Fisb.parsePirep('PIREP SJC 120150Z SJC UA /OV SJC090010/TM 0150');
    assert.ok(distanceNm(Fisb.pirepPosition(p, null), [37.363, -121.72]) < 1);
});

test('current report list drops reports the station stopped sending', () => {
    const d = new Fisb.Decoder();
    const expired = [];
    d.on((kind, item) => { if (kind === 'expire' && item) expired.push(item.key); });
    const send = (frames, stationLat, seconds) => d.ingestUplink(uplink(frames, stationLat), { timestampMs: T0 + seconds * 1000 });
    send([productFrame(12, textReport(101, 'SIGMET A')), productFrame(12, textReport(102, 'SIGMET B'))], 37.5, 0);
    send([productFrame(12, textReport(102, 'SIGMET B')), productFrame(8, textReport(7, 'NOTAM'))], 38.5, 1);
    assert.deepStrictEqual([...d.reports.keys()], ['12/26/101', '12/26/102', '8/26/7']);
    // Lists that are cut short or cover only TFRs remove nothing.
    send([crlFrame(12, [], 0x02), crlFrame(8, [], 0x10)], 37.5, 2);
    assert.strictEqual(d.reports.size, 3);
    // The first station stops listing both SIGMETs; the second one still sends B.
    send([crlFrame(12, [])], 37.5, 3);
    assert.deepStrictEqual([...d.reports.keys()], ['12/26/102', '8/26/7']);
    assert.deepStrictEqual(expired, ['12/26/101']);
    send([crlFrame(12, [[26, 102]])], 38.5, 4);
    assert.ok(d.reports.has('12/26/102'));
    send([crlFrame(12, [[26, 555]])], 38.5, 5);
    assert.deepStrictEqual([...d.reports.keys()], ['8/26/7']);
});

test('map layer draws pilot reports, lightning, cloud tops, icing and turbulence', (t) => {
    const { L, map, document, made } = fakeBrowser();
    const stored = {};
    globalThis.document = document;
    globalThis.localStorage = { getItem: (key) => stored[key] || null, setItem: (key, value) => { stored[key] = value; } };
    t.after(() => { delete globalThis.document; delete globalThis.localStorage; });
    const d = new Fisb.Decoder();
    const pirep = 'PIREP SNS 121000Z SNS UUA /OV SNS090020/TM 1000/FL085/TP C172/TA M02/TB SEV/IC LGT RIME';
    d.ingestUplink(uplink([
        productFrame(413, dlacBytes(pirep + '\x1E')),
        // One strike of positive polarity in the first bin.
        productFrame(103, gridBlock(0, [0x09, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xF0, 0xE0])),
        // Cloud tops: 9000 to 10500 ft in the first row.
        productFrame(84, gridBlock(1, [0xE7, 31, 0xE0, 95])),
        // Icing at 6000 ft: moderate with large droplets in 8 bins, then none. At 8000 ft: trace everywhere.
        productFrame(70, gridBlock(2, [7, 0x40 | (3 << 3) | 2, 119, 0])),
        productFrame(70, gridBlock(3, [127, 1 << 3])),
        // Turbulence at 20000 ft: class 5 everywhere.
        productFrame(91, gridBlock(1, [0xE5, 127])),
    ]), { timestampMs: T0 });
    assert.strictEqual(d.stats.errors, 0);
    const layer = Fisb.createLayer(L, d, { stationsUrl: null });
    layer.addTo(map);
    const names = Object.keys(layer.parts);
    const [buttons, select] = [layer.control.box.children.filter((c) => c.tag === 'button'), layer.control.box.children.find((c) => c.tag === 'select')];
    const tip = (name) => flatten(buttons[names.indexOf(name)].children[1]);
    const draw = (name) => {
        made.length = 0;
        layer.parts[name]._map = map;
        layer.parts[name].onAdd(map);
        return made.filter((o) => o.type === 'rect');
    };

    // The pilot report sits 20 NM magnetic east of Salinas.
    const marker = made.find((o) => o.type === 'marker' && /SNS UUA/.test(tooltip(o)));
    assert.ok(distanceNm(marker.where, [36.59, -121.20]) < 2, String(marker.where));
    assert.match(marker.options.icon.className, /fisb-urgent/);
    assert.ok(marker.options.icon.html.includes('#e00'));
    assert.match(flatten(marker.popup()), /Urgent pilot report · SNS\nLocation: SNS090020\nTime: 10:00Z\nAltitude: 8500 ft\nAircraft: C172\nTemperature: -02 °C\nTurbulence: SEV\nIcing: LGT RIME/);
    assert.match(tip('pireps'), /^Pilot reports 1/);

    // Lightning: one mark of at least 6 pixels with a dark rim, centered on the bin at 36.058 N 119.988 W.
    let rects = draw('lightning');
    assert.deepStrictEqual(rects.map((r) => r.color), ['#222', '#fd0']);
    assert.ok(rects[1].w >= 6 && rects[1].h >= 6);
    assert.ok(Math.abs(rects[1].x + rects[1].w / 2 - (125 - 119.9875) * 100) < 1.5 && Math.abs(rects[1].y + rects[1].h / 2 - (40 - 36.058) * 100) < 1.5);
    assert.match(tip('lightning'), /^Lightning 10:00Z.*strikes$/);

    // Cloud tops on the medium scale: the first row of the block, 4 degrees wide and 5 minutes high.
    rects = draw('cloudTops');
    assert.strictEqual(rects.length, 1);
    assert.deepStrictEqual([rects[0].x, rects[0].y, rects[0].w, rects[0].h], [500, 393, 400, 9]);

    // Icing and turbulence show one altitude at a time.
    assert.strictEqual(select.style.display, 'none');
    layer.setVisible('icing', true);
    assert.strictEqual(select.style.display, '');
    assert.deepStrictEqual(select.children.map((o) => o.textContent), ['2', '4', '6', '8', '10', '12', '14', '16', '18', '20', '22', '24']);
    rects = draw('icing');
    assert.deepStrictEqual([...new Set(rects.map((r) => r.color))], ['#bef']);
    assert.strictEqual(rects.length, 4);
    assert.match(tip('icing'), /^Icing 8000 ft 10:00Z.*Trace.*Large droplets$/);
    select.value = '6000';
    select.onchange();
    rects = draw('icing');
    // Moderate icing in 8 bins, each with a large droplet dot.
    assert.deepStrictEqual(rects.map((r) => r.color), ['#36d', ...new Array(8).fill('#e00')]);
    assert.strictEqual(rects[0].w, 100);
    assert.match(tip('icing'), /^Icing 6000 ft 10:00Z/);
    assert.strictEqual(draw('turbulence').length, 0);
    assert.ok(buttons[names.indexOf('turbulence')].classList.names.has('fisb-none'));
    layer.setAltitude(20000);
    rects = draw('turbulence');
    assert.deepStrictEqual([...new Set(rects.map((r) => r.color))], ['#f93']);
    assert.match(tip('turbulence'), /^Turbulence 20000 ft 10:00Z.*eddy dissipation rate × 100$/);
    assert.ok(!buttons[names.indexOf('turbulence')].classList.names.has('fisb-none'));

    // The choice of parts and altitude carries over to the next layer.
    layer.setVisible('pireps', true);
    layer.setVisible('radar', false);
    const next = Fisb.createLayer(L, d, { stationsUrl: null });
    assert.deepStrictEqual(names.filter((name) => next.layers.has(next.parts[name])), ['icing', 'airports', 'pireps', 'areas', 'stations']);
    next.addTo(map);
    assert.strictEqual(next.control.box.children.find((c) => c.tag === 'select').children.find((o) => o.selected).textContent, '20');
});
