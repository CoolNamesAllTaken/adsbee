// FIS-B (weather and notices on the 978 MHz UAT ground uplink): decoder, report store and Leaflet layer.
// Formats follow RTCA DO-282 (uplink), DO-267A (product headers) and DO-358 (products).
(function (root) {
    'use strict';

    const UPLINK_ENCODED_BYTES = 552;
    const UPLINK_PAYLOAD_BYTES = 432;
    const UPLINK_BLOCKS = 6;  // Interleaved Reed-Solomon blocks, 72 payload bytes each.
    const MIN = 60000;

    // Six-bit character set used by text products. 28 is a tab (run of spaces), 30 a record separator.
    const DLAC = '\x03ABCDEFGHIJKLMNOPQRSTUVWXYZ\x1A\t\x1E\n| !"#$%&\'()*+,-./0123456789:;<=>?';

    const PRODUCT_NAMES = {
        8: 'NOTAM', 11: 'AIRMET', 12: 'SIGMET', 13: 'SUA', 14: 'G-AIRMET', 15: 'CWA', 16: 'NOTAM-TRA', 17: 'NOTAM-TMOA', 18: 'TFR', 19: 'TFR',
        63: 'NEXRAD regional', 64: 'NEXRAD CONUS', 70: 'Icing low', 71: 'Icing high', 84: 'Cloud tops',
        90: 'Turbulence low', 91: 'Turbulence high', 103: 'Lightning', 413: 'Text',
    };
    const GRID_PRODUCTS = [63, 64, 70, 71, 84, 90, 91, 103];
    const TWGO_PRODUCTS = [8, 11, 12, 13, 14, 15, 16, 17, 18, 19];
    // Minutes a grid image stays valid after its product time.
    const GRID_RETENTION_MIN = { 63: 75, 64: 75, 103: 75, 70: 105, 71: 105, 84: 105, 90: 105, 91: 105 };
    const GAIRMET_ELEMENTS = ['TFR', 'TURB', 'LLWS', 'SFC', 'ICING', 'FRZLVL', 'IFR', 'MTN'];
    // Cause of an IFR or mountain obscuration area, by qualifier bit.
    const GAIRMET_CONDITIONS = ['PCPN', 'BR', 'FG', 'HZ', 'FU', 'BLSN', 'CLDS', 'DU', 'ASH'];

    function hexToBytes(hex) {
        const out = new Uint8Array(hex.length >> 1);
        for (let i = 0; i < out.length; i++) out[i] = parseInt(hex.substr(i * 2, 2), 16);
        return out;
    }

    /** 552-byte encoded uplink message (bytes or hex) -> 432-byte payload. No error correction. */
    function deinterleave(encoded) {
        const src = typeof encoded === 'string' ? hexToBytes(encoded) : encoded;
        if (!src || src.length < UPLINK_ENCODED_BYTES) return null;
        const out = new Uint8Array(UPLINK_PAYLOAD_BYTES);
        const blockBytes = UPLINK_PAYLOAD_BYTES / UPLINK_BLOCKS;
        for (let block = 0; block < UPLINK_BLOCKS; block++) {
            for (let i = 0; i < blockBytes; i++) out[block * blockBytes + i] = src[i * UPLINK_BLOCKS + block];
        }
        return out;
    }

    /** RAW console line "#UAT*+<hex>;(rssi,quality,timestamp)" -> {payload, meta}, or null for other lines. */
    function parseRawLine(line) {
        const m = /#UAT\*\+([0-9A-Fa-f]{1104});(?:\((-?\d+)[^)]*\))?/.exec(line);
        if (!m) return null;
        const meta = {};
        if (m[2] !== undefined) meta.rssiDbm = parseInt(m[2], 10);
        return { payload: deinterleave(m[1]), meta };
    }

    const UPLINK_MESSAGE_BYTES = 440;
    const UPLINK_RSSI_UNKNOWN = -128;

    /** /uplink WebSocket message (ArrayBuffer or bytes) -> {payload, meta}, or null when too short. */
    function parseUplinkMessage(data) {
        const b = data instanceof Uint8Array ? data : new Uint8Array(data);
        if (b.length < UPLINK_MESSAGE_BYTES) return null;
        const view = new DataView(b.buffer, b.byteOffset, b.byteLength);
        const meta = { deviceMs: view.getUint32(436, true) };
        const rssiDbm = view.getInt8(UPLINK_PAYLOAD_BYTES);
        if (rssiDbm !== UPLINK_RSSI_UNKNOWN) meta.rssiDbm = rssiDbm;
        return { payload: b.subarray(0, UPLINK_PAYLOAD_BYTES), meta };
    }

    /** True for an AIRCRAFT_JSON_UAT_UPLINK uplink line, complete or cut short. */
    const isUplinkLine = (line) => /^\s*\{"uat_uplink"/.test(line);

    /** Serial line {"uat_uplink":"<Base64>","rssi":..,"t":..} -> {payload, meta}, or null for other lines. */
    function parseUplinkLine(line) {
        if (!isUplinkLine(line)) return null;
        let o, text;
        try { o = JSON.parse(line); text = atob(o.uat_uplink); } catch (_) { return null; }
        if (text.length !== UPLINK_PAYLOAD_BYTES) return null;
        const payload = new Uint8Array(UPLINK_PAYLOAD_BYTES);
        for (let i = 0; i < payload.length; i++) payload[i] = text.charCodeAt(i);
        const meta = {};
        if (typeof o.rssi === 'number') meta.rssiDbm = o.rssi;
        if (typeof o.t === 'number') meta.deviceMs = o.t;
        return { payload, meta };
    }

    function dlac(b, start, numBytes) {
        let text = '', tab = false;
        const end = Math.min(b.length, start + numBytes);
        const add = (c) => {
            if (tab) { text += ' '.repeat(c); tab = false; }
            else if (c === 28) tab = true;
            else text += DLAC[c];
        };
        for (let i = start; i < end; i++) {
            const m = (i - start) % 3;
            if (m === 0) add(b[i] >> 2);
            else if (m === 1) add(((b[i - 1] & 0x03) << 4) | (b[i] >> 4));
            else { add(((b[i - 1] & 0x0F) << 2) | (b[i] >> 6)); add(b[i] & 0x3F); }
        }
        return text;
    }

    // Reads big-endian bit fields.
    function bitReader(b, bit) {
        return (n) => {
            let v = 0;
            for (let i = 0; i < n; i++, bit++) v = v * 2 + ((b[bit >> 3] >> (7 - (bit & 7))) & 1);
            return v;
        };
    }

    function angle(raw, bits, isLat) {
        const deg = raw * 360 / Math.pow(2, bits);
        return isLat ? (deg > 90 ? deg - 180 : deg) : (deg > 180 ? deg - 360 : deg);
    }

    /** Timestamp nearest to refMs matching the given UTC fields {month?, day?, hour, minute, second?}. */
    function resolveTime(refMs, t) {
        const ref = new Date(refMs);
        let best = NaN;
        // Try the year, month or day before and after for the first field that is missing.
        for (let k = -1; k <= 1; k++) {
            const year = ref.getUTCFullYear() + (t.month ? k : 0);
            const month = t.month ? t.month - 1 : ref.getUTCMonth() + (t.day ? k : 0);
            const c = Date.UTC(year, month, t.day || ref.getUTCDate() + k, t.hour, t.minute, t.second || 0);
            // Skip rollovers such as day 31 in a 30-day month.
            if (t.day && new Date(c).getUTCDate() !== t.day) continue;
            if (isNaN(best) || Math.abs(c - refMs) < Math.abs(best - refMs)) best = c;
        }
        return best;
    }

    function decodeUplinkHeader(p) {
        return {
            lat: angle((p[0] << 15) | (p[1] << 7) | (p[2] >> 1), 24, true),
            lon: angle(((p[2] & 0x01) << 23) | (p[3] << 15) | (p[4] << 7) | (p[5] >> 1), 24, false),
            positionValid: !!(p[5] & 0x01),
            utcCoupled: !!(p[6] & 0x80),
            appDataValid: !!(p[6] & 0x20),
            slot: p[6] & 0x1F,
            tisbSiteId: p[7] >> 4,
        };
    }

    /** Splits application data into information frames [{type, data}]. */
    function splitFrames(p) {
        const frames = [];
        let i = 8;
        while (i + 2 <= p.length) {
            const len = (p[i] << 1) | (p[i + 1] >> 7);
            if (len === 0 || i + 2 + len > p.length) break;
            frames.push({ type: p[i + 1] & 0x0F, data: p.subarray(i + 2, i + 2 + len) });
            i += 2 + len;
        }
        return frames;
    }

    /** Product header: id, time and optional segmentation, followed by the product payload. */
    function decodeApduHeader(d) {
        const r = bitReader(d, 3);
        const h = { productId: r(11) };
        h.segmented = !!r(1);
        const timeOption = r(2);
        if (timeOption & 2) { h.month = r(4); h.day = r(5); }
        h.hour = r(5);
        h.minute = r(6);
        let bits = 17 + (timeOption & 2 ? 9 : 0) + 11;
        if (timeOption & 1) { h.second = r(6); bits += 6; }
        if (h.segmented) {
            h.fileId = r(10);
            h.fileLength = r(9);
            h.apduNumber = r(9);
            bits += 28;
        }
        h.payload = d.subarray((bits + 7) >> 3);
        return h;
    }

    /** Ceiling/visibility flight category of a METAR: 'VFR', 'MVFR', 'IFR', 'LIFR' or null. */
    function flightCategory(metar) {
        const body = metar.split(' RMK ')[0];
        let vis = null;
        const v = /(?:^| )(M)?(?:(\d+) )?(\d+)(?:\/(\d+))?SM(?= |$)/.exec(body);
        if (v) {
            vis = v[4] ? (v[2] ? +v[2] : 0) + v[3] / v[4] : +v[3];
            if (v[1]) vis -= 0.01;
        }
        let ceiling = null;
        const re = /(?:^| )(BKN|OVC|VV)(\d{3})/g;
        for (let m; (m = re.exec(body));) ceiling = Math.min(ceiling === null ? Infinity : ceiling, m[2] * 100);
        if (vis === null && ceiling === null && !/ (CLR|SKC|FEW|SCT|NSC|CAVOK)/.test(body)) return null;
        if ((ceiling !== null && ceiling < 500) || (vis !== null && vis < 1)) return 'LIFR';
        if ((ceiling !== null && ceiling < 1000) || (vis !== null && vis < 3)) return 'IFR';
        if ((ceiling !== null && ceiling <= 3000) || (vis !== null && vis <= 5)) return 'MVFR';
        return 'VFR';
    }

    /** Text product 413 payload -> [{kind, id, day, hour, minute, text}]. */
    function decodeText(payload) {
        const out = [];
        for (const rec of dlac(payload, 0, payload.length).split(/[\x1E\x03]/)) {
            const text = rec.replace(/\s+$/, '');
            const m = /^(\S+) (\S+) (\d\d)(\d\d)(\d\d)Z\s*/.exec(text);
            if (!m) continue;
            out.push({ kind: m[1], id: m[2], day: +m[3], hour: +m[4], minute: +m[5], text });
        }
        return out;
    }

    function decodeVertices(d, i, count, option) {
        const pts = [];
        for (let k = 0; k < count; k++) {
            if (option === 7 || option === 8) {
                if (i + 14 > d.length) break;
                const r = bitReader(d, i * 8);
                const lon = angle(r(18), 18, false), lat = angle(r(18), 18, true);
                r(36);  // Top center; equal to the bottom center for a cylinder.
                pts.push({ lat, lon, lo: r(7) * 500, hi: r(7) * 500, rLon: r(9) * 0.2, rLat: r(9) * 0.2 });
                i += 14;
            } else {
                if (i + 6 > d.length) break;
                const r = bitReader(d, i * 8);
                const lon = angle(r(19), 19, false), lat = angle(r(19), 19, true);
                pts.push({ lat, lon, alt: r(10) * 100 });
                i += 6;
            }
        }
        return pts;
    }

    function decodeGraphicRecord(d, productId) {
        const rec = {
            number: ((d[1] & 0x3F) << 8) | d[2],
            year: d[3] >> 1,
            recordId: ((d[4] & 0x1E) >> 1) + 1,
        };
        let i = 5;
        if (d[4] & 0x01) { rec.label = dlac(d, i, 9).replace(/[\x00-\x1F]/g, '').trim(); i += 9; }
        else i += 2;
        const qualifierFlag = d[i] & 0x40, parameterFlag = d[i] & 0x20;
        if (d[i] & 0x80 && productId === 14) rec.element = GAIRMET_ELEMENTS[d[i] & 0x1F];
        rec.objectType = d[i + 1] >> 4;
        rec.status = d[i + 1] & 0x0F;
        i += 2;
        if (qualifierFlag) {
            const bits = (d[i] << 16) | (d[i + 1] << 8) | d[i + 2];
            rec.conditions = GAIRMET_CONDITIONS.filter((name, bit) => name && bits & (1 << bit));
            i += 3;
        }
        if (parameterFlag) i += 2;
        const applicability = d[i] >> 6, timeFormat = (d[i] >> 4) & 0x03, option = d[i] & 0x0F;
        rec.operator = d[i + 1] >> 6;
        const count = option ? (d[i + 1] & 0x3F) + 1 : 0;
        i += 2;
        const readTime = () => {
            const t = {};
            if (timeFormat === 1) t.month = d[i++];
            if (timeFormat === 1 || timeFormat === 2) t.day = d[i++];
            if (timeFormat) { t.hour = d[i++]; t.minute = d[i++]; }
            return t;
        };
        if (applicability & 1) rec.start = readTime();
        if (applicability & 2) rec.stop = readTime();
        const v = decodeVertices(d, i, count, option);
        rec.agl = option === 4 || option === 8 || option === 9 || option === 12;
        if (option === 7 || option === 8) {
            if (v[0]) Object.assign(rec, { shape: 'circle', center: [v[0].lat, v[0].lon], radiusNm: v[0].rLon, lo: v[0].lo, hi: v[0].hi });
        } else if (v.length) {
            rec.shape = option === 9 || option === 10 ? 'point' : option === 11 || option === 12 ? 'line' : 'polygon';
            // A volume is sent as the same outline twice: first at one altitude limit, then at the other.
            const half = v.length / 2;
            const doubled = v.length % 2 === 0 && v.every((p, k) => k < half || (p.lat === v[k - half].lat && p.lon === v[k - half].lon));
            const ring = doubled ? v.slice(0, half) : v;
            rec.points = ring.map((p) => [p.lat, p.lon]);
            const alts = [v[0].alt, v[v.length - 1].alt];
            rec.lo = Math.min(alts[0], alts[1]);
            rec.hi = Math.max(alts[0], alts[1]);
        }
        return rec;
    }

    /** Text with graphic overlay products (NOTAM, AIRMET, SIGMET, ...) -> {location, texts, graphics}. */
    function decodeTwgo(d, productId) {
        const out = { location: dlac(d, 2, 3).replace(/[\x00-\x1F]/g, '').trim(), texts: [], graphics: [] };
        const format = d[0] >> 4, count = d[1] >> 4;
        let i = 6;
        for (let k = 0; k < count && i + 5 <= d.length; k++) {
            if (format === 2) {
                const len = (d[i] << 8) | d[i + 1];
                if (len < 5) break;
                out.texts.push({
                    number: (d[i + 2] << 6) | (d[i + 3] >> 2),
                    year: ((d[i + 3] & 0x03) << 5) | (d[i + 4] >> 3),
                    active: !!(d[i + 4] & 0x04),
                    text: dlac(d, i + 5, len - 5).replace(/[\x00-\x08\x0B-\x1F]/g, '').replace(/\s+$/, ''),
                });
                i += len;
            } else if (format === 8) {
                const len = (d[i] << 2) | (d[i + 1] >> 6);
                if (len < 9) break;
                out.graphics.push(decodeGraphicRecord(d.subarray(i, Math.min(d.length, i + len)), productId));
                i += len;
            } else break;
        }
        return out;
    }

    /** Bounds of a grid block: north and west edges plus bin size, in degrees. */
    function blockBounds(blockNumber, scale, south) {
        const mult = [1, 5, 9][scale] || 1;
        const row = Math.floor(blockNumber / 450);
        let west = (blockNumber % 450) * 0.8;
        if (west >= 180) west -= 360;
        const wide = blockNumber >= 405000 ? 2 : 1;  // Blocks double in width above 60 degrees latitude.
        const binLat = mult / 60, binLon = 1.5 * mult * wide / 60;
        return { north: south ? -row * 4 / 60 : (row + 1) * 4 / 60, west, binLat, binLon };
    }

    /** Global block product payload -> {blockNumber, scale, south, altitudeFt?, bins | emptyBlocks}. */
    function decodeGrid(d, productId) {
        const out = { blockNumber: ((d[0] & 0x0F) << 16) | (d[1] << 8) | d[2], scale: (d[0] >> 4) & 0x03, south: !!(d[0] & 0x40) };
        if (productId === 70 || productId === 71 || productId === 90 || productId === 91) {
            // Icing and turbulence carry an altitude level where other products carry the scale.
            out.altitudeFt = ((d[0] >> 4) & 0x07) * 2000 + (productId === 70 || productId === 90 ? 2000 : 18000);
            out.scale = 1;
            out.south = false;
        }
        if (!(d[0] & 0x80)) {
            // Empty block list: this block, then one bit for each following block.
            const step = [1, 5, 9][out.scale] || 1;
            out.emptyBlocks = [out.blockNumber];
            const len = d[3] & 0x0F;
            for (let bit = 0; bit < 4 + len * 8; bit++) {
                const set = bit < 4 ? d[3] & (0x10 << bit) : d[4 + ((bit - 4) >> 3)] & (1 << ((bit - 4) & 7));
                if (set) out.emptyBlocks.push(out.blockNumber + (bit + 1) * step);
            }
            return out;
        }
        const bins = new Uint8Array(128);
        let n = 0;
        for (let i = 3; i < d.length && n < 128;) {
            let run, value;
            if (productId === 63 || productId === 64) { run = (d[i] >> 3) + 1; value = d[i] & 0x07; i++; }
            else if (productId === 103) {
                // 0xF8 is a 32-bin run of "no strikes".
                run = (d[i] >> 4) + (d[i] === 0xF8 ? 17 : 1); value = d[i] & 0x07; i++;
            } else if (productId === 70 || productId === 71) { run = d[i] + 1; value = d[i + 1]; i += 2; }
            else if (d[i] >> 4 === 0x0E) { run = d[i + 1] + 1; value = d[i] & 0x0F; i += 2; }
            else { run = (d[i] >> 4) + 1; value = d[i] & 0x0F; i++; }
            bins.fill(value, n, Math.min(128, n + run));
            n += run;
        }
        out.bins = bins;
        return out;
    }

    /** Current report list: which reports of a product the station is sending. */
    function decodeCrl(d) {
        const out = { productId: (d[0] << 3) | (d[1] >> 5), tfr: !!(d[1] & 0x10), overflow: !!(d[1] & 0x02), rangeNm: d[2] * 5, reports: [] };
        let i = 3;
        if (d[1] & 0x01) { out.location = dlac(d, 3, 3).trim(); i = 6; }
        const count = d[i++];
        for (let k = 0; k < count && i + 3 <= d.length; k++, i += 3) {
            out.reports.push({ year: d[i] & 0x7F, number: ((d[i + 1] & 0x3F) << 8) | d[i + 2], text: !!(d[i + 1] & 0x80), graphic: !!(d[i + 1] & 0x40) });
        }
        return out;
    }

    class Decoder {
        /** @param {{now?: () => number}} [options] Clock used when ingestUplink gets no timestamp. */
        constructor(options) {
            this.now = (options && options.now) || Date.now;
            this.listeners = [];
            this.reset();
        }

        reset() {
            this.stations = new Map();  // Ground stations by "lat,lon".
            this.texts = new Map();     // METAR, TAF, PIREP and winds by "KIND id".
            this.reports = new Map();   // NOTAM, AIRMET, SIGMET, ... by "product/year/number". from: stations sending it.
            this.grids = new Map();     // Product id -> Map of blocks.
            this.crl = new Map();       // Current report lists by "station/product".
            this.airports = new Map();  // Airport positions learned from NOTAMs, by id.
            this.segments = new Map();
            this.stats = { uplinks: 0, frames: 0, products: {}, unknownProducts: {}, unknownFrames: {}, errors: 0 };
            this.timeMs = 0;
            this.lastExpireMs = 0;
        }

        /** Subscribe to changes: callback(kind, item) with kind 'station', 'text', 'report', 'grid', 'crl' or 'expire'. */
        on(callback) {
            this.listeners.push(callback);
            return () => { this.listeners = this.listeners.filter((l) => l !== callback); };
        }

        emit(kind, item) {
            for (const l of this.listeners) l(kind, item);
        }

        /**
         * @param {Uint8Array} payload De-interleaved 432-byte uplink payload.
         * @param {{rssiDbm?: number, timestampMs?: number}} [meta]
         * @returns {object|null} Decoded header, or null for an unusable payload.
         */
        ingestUplink(payload, meta) {
            if (!payload || payload.length < UPLINK_PAYLOAD_BYTES) return null;
            const nowMs = (meta && meta.timestampMs) || this.now();
            this.timeMs = nowMs;
            this.stats.uplinks++;
            const header = decodeUplinkHeader(payload);
            let station = null;
            if (header.lat || header.lon) {
                const key = header.lat.toFixed(4) + ',' + header.lon.toFixed(4);
                station = this.stations.get(key) || { key, uplinks: 0 };
                Object.assign(station, header, { rxMs: nowMs, expiresMs: nowMs + 5 * MIN });
                if (meta && meta.rssiDbm !== undefined) station.rssiDbm = meta.rssiDbm;
                station.uplinks++;
                this.stations.set(key, station);
                this.emit('station', station);
            }
            if (header.appDataValid) {
                for (const frame of splitFrames(payload)) {
                    this.stats.frames++;
                    try {
                        this.ingestFrame(frame, nowMs, station);
                    } catch (e) {
                        this.stats.errors++;
                    }
                }
            }
            if (nowMs - this.lastExpireMs > 10000 || nowMs < this.lastExpireMs) this.expire(nowMs);
            return header;
        }

        ingestFrame(frame, nowMs, station) {
            if (frame.type === 0) {
                const h = decodeApduHeader(frame.data);
                if (!h.segmented) return this.ingestProduct(h.productId, h.payload, h, nowMs, station);
                // Collect linked segments, then decode them as one payload.
                const key = h.productId + '/' + h.fileId;
                let file = this.segments.get(key);
                if (!file || file.parts.length !== h.fileLength) file = { parts: new Array(h.fileLength).fill(null), expiresMs: 0 };
                file.expiresMs = nowMs + 5 * MIN;
                if (h.apduNumber >= 1 && h.apduNumber <= h.fileLength) file.parts[h.apduNumber - 1] = h.payload.slice();
                this.segments.set(key, file);
                if (file.parts.every(Boolean)) {
                    this.segments.delete(key);
                    // Every segment of a text/graphic product repeats the 6-byte record header.
                    const skip = TWGO_PRODUCTS.includes(h.productId) ? 6 : 0;
                    const parts = file.parts.map((p, k) => (k ? p.subarray(skip) : p));
                    const joined = new Uint8Array(parts.reduce((n, p) => n + p.length, 0));
                    let at = 0;
                    for (const p of parts) { joined.set(p, at); at += p.length; }
                    this.ingestProduct(h.productId, joined, h, nowMs, station);
                }
            } else if (frame.type === 14) {
                const list = decodeCrl(frame.data);
                list.station = station ? station.key : '';
                list.rxMs = nowMs;
                list.expiresMs = nowMs + 5 * MIN;
                this.crl.set(list.station + '/' + list.productId + (list.tfr ? 'T' : ''), list);
                this.emit('crl', list);
                this.applyCrl(list);
            } else if (frame.type !== 15) {  // 15: traffic service status, unrelated to FIS-B.
                this.stats.unknownFrames[frame.type] = (this.stats.unknownFrames[frame.type] || 0) + 1;
            }
        }

        /** Drops reports of a product that the station stopped listing and no other station still sends. */
        applyCrl(list) {
            // Lists marked TFR cover part of a product; an overflowed list is incomplete.
            if (list.tfr || list.overflow) return;
            const listed = new Set(list.reports.map((r) => r.year + '/' + r.number));
            for (const [key, report] of this.reports) {
                if (report.productId !== list.productId || !report.from.has(list.station) || listed.has(report.year + '/' + report.number)) continue;
                report.from.delete(list.station);
                if (report.from.size) continue;
                this.reports.delete(key);
                this.emit('expire', report);
            }
        }

        ingestProduct(productId, payload, header, nowMs, station) {
            const count = (table) => { table[productId] = (table[productId] || 0) + 1; };
            if (productId === 413) {
                count(this.stats.products);
                for (const t of decodeText(payload)) this.storeText(t, nowMs);
            } else if (TWGO_PRODUCTS.includes(productId)) {
                count(this.stats.products);
                this.storeTwgo(productId, decodeTwgo(payload, productId), nowMs, station ? station.key : '');
            } else if (GRID_PRODUCTS.includes(productId)) {
                count(this.stats.products);
                this.storeGrid(productId, decodeGrid(payload, productId), resolveTime(nowMs, header), nowMs);
            } else count(this.stats.unknownProducts);
        }

        storeText(t, nowMs) {
            const kind = /^(METAR|SPECI)$/.test(t.kind) ? 'METAR' : t.kind.split('.')[0];
            const timeMs = resolveTime(nowMs, t);
            // Pilot reports have no unique id.
            const key = kind + ' ' + (kind === 'PIREP' ? t.text : kind === 'WINDS' ? t.id + ' ' + timeMs : t.id);
            const old = this.texts.get(key);
            if (old && old.timeMs > timeMs) return;
            const item = { key, kind, id: t.id, timeMs, text: t.text, rxMs: nowMs, expiresMs: nowMs + 120 * MIN };
            if (kind === 'METAR') {
                item.category = flightCategory(t.text);
                item.expiresMs = timeMs + 120 * MIN;
            } else if (kind === 'PIREP') item.expiresMs = timeMs + 120 * MIN;
            else if (kind === 'TAF') {
                const v = /\b(\d\d)(\d\d)\/(\d\d)(\d\d)\b/.exec(t.text);
                const end = v && resolveTime(timeMs + 15 * 60 * MIN, { day: +v[3], hour: +v[4] % 24, minute: 0 });
                item.expiresMs = end ? end + (v[4] === '24' ? 1440 * MIN : 0) : timeMs + 30 * 60 * MIN;
            }
            if (old && old.timeMs === timeMs && old.text === t.text) { old.rxMs = nowMs; old.expiresMs = item.expiresMs; return; }
            this.texts.set(key, item);
            this.emit('text', item);
        }

        storeTwgo(productId, twgo, nowMs, stationKey) {
            const get = (r) => {
                const key = productId + '/' + r.year + '/' + r.number;
                let report = this.reports.get(key);
                if (!report) {
                    report = { key, productId, product: PRODUCT_NAMES[productId], number: r.number, year: r.year, text: '', shapes: [], from: new Set() };
                    this.reports.set(key, report);
                }
                report.from.add(stationKey);
                report.rxMs = nowMs;
                report.expiresMs = nowMs + 60 * MIN;
                if (twgo.location) report.location = twgo.location;
                return report;
            };
            for (const t of twgo.texts) {
                const report = get(t);
                if (!t.active) { this.reports.delete(report.key); this.emit('expire', report); continue; }
                if (report.text === t.text) continue;
                report.text = t.text;
                this.emit('report', report);
            }
            for (const g of twgo.graphics) {
                const report = get(g);
                const shape = Object.assign({}, g);
                delete shape.number;
                delete shape.year;
                if (g.start) shape.startMs = resolveTime(nowMs, g.start);
                if (g.stop) shape.stopMs = resolveTime(shape.startMs || nowMs, g.stop);
                if (g.shape === 'point' && g.label) this.airports.set(g.label, g.points[0]);
                const at = report.shapes.findIndex((s) => s.recordId === g.recordId);
                if (at >= 0 && JSON.stringify(report.shapes[at]) === JSON.stringify(shape)) continue;
                if (at >= 0) report.shapes[at] = shape; else report.shapes.push(shape);
                report.shapes.sort((a, b) => a.recordId - b.recordId);
                this.emit('report', report);
            }
        }

        storeGrid(productId, grid, timeMs, nowMs) {
            let blocks = this.grids.get(productId);
            if (!blocks) this.grids.set(productId, blocks = new Map());
            const expiresMs = timeMs + GRID_RETENTION_MIN[productId] * MIN;
            const altitude = grid.altitudeFt || 0;
            let changed = false;
            for (const blockNumber of grid.emptyBlocks || [grid.blockNumber]) {
                const key = blockNumber + (altitude ? '@' + altitude : '');
                const old = blocks.get(key);
                if (old && old.timeMs > timeMs) continue;
                changed = changed || !old || old.timeMs !== timeMs;
                blocks.set(key, {
                    blockNumber, scale: grid.scale, south: grid.south, altitudeFt: grid.altitudeFt,
                    bins: grid.bins || null, timeMs, rxMs: nowMs, expiresMs,
                });
            }
            if (changed) this.emit('grid', { productId, timeMs });
        }

        /** Drops everything past its validity. Called from ingestUplink; call it on a timer when uplinks stop. */
        expire(nowMs) {
            nowMs = nowMs || this.now();
            this.lastExpireMs = nowMs;
            let expired = 0;
            const sweep = (map) => {
                for (const [key, item] of map) {
                    if (item.expiresMs > nowMs && !(item.shapes && item.shapes.length && item.shapes.every((s) => s.stopMs <= nowMs))) continue;
                    map.delete(key);
                    expired++;
                }
            };
            for (const map of [this.stations, this.texts, this.reports, this.crl, this.segments, ...this.grids.values()]) sweep(map);
            if (expired) this.emit('expire', null);
        }
    }

    let stationTable = null, navaidTable = null;

    /** Loads the station and navaid tables from fisb_stations.js (a string, see that file). */
    function setStations(data) {
        const [stations, navaids = ''] = data.split('|');
        const position = (text, i) => [parseInt(text.substr(i, 3), 36) / 100 - 90, parseInt(text.substr(i + 3, 3), 36) / 100 - 180];
        stationTable = new Map();
        for (let i = 0; i + 10 <= stations.length; i += 10) stationTable.set(stations.substr(i, 4), position(stations, i + 4));
        navaidTable = new Map();
        for (let i = 0; i + 10 <= navaids.length; i += 10) {
            navaidTable.set(navaids.substr(i, 3), position(navaids, i + 3).concat(parseInt(navaids[i + 9], 36) * 1.5 - 21));
        }
    }

    /** [lat, lon] of a weather station or airport, or null when unknown. */
    function stationPosition(id, decoder) {
        if (!stationTable && root.FISB_STATIONS) setStations(root.FISB_STATIONS);
        return (stationTable && (stationTable.get(id) || stationTable.get('K' + id))) || (decoder && decoder.airports.get(id)) || null;
    }

    // Position of a navaid [lat, lon, magnetic variation] or of a station [lat, lon].
    const locate = (id, decoder) => (id && ((id.length === 3 && navaidTable && navaidTable.get(id)) || stationPosition(id, decoder))) || null;

    // Magnetic variation in degrees east: the navaid's own, else that of the nearest navaid.
    function variation(position) {
        if (position.length > 2) return position[2];
        let best = 0, nearest = Infinity;
        for (const n of navaidTable ? navaidTable.values() : []) {
            const d = Math.hypot(n[0] - position[0], (n[1] - position[1]) * Math.cos(position[0] * Math.PI / 180));
            if (d < nearest) { nearest = d; best = n[2]; }
        }
        return best;
    }

    const PIREP_FIELD = /\/(?=(?:OV|TM|TP|SK|WX|TA|WV|TB|IC|RM)(?: |$)|FL)/;
    const COMPASS = ['N', 'NNE', 'NE', 'ENE', 'E', 'ESE', 'SE', 'SSE', 'S', 'SSW', 'SW', 'WSW', 'W', 'WNW', 'NW', 'NNW'];

    /** Pilot report text -> {station, urgent, fields: {OV, TM, FL, ...}, altitudeFt, severity}. severity: 0 none to 3 severe. */
    function parsePirep(text) {
        const parts = text.replace(/\s+/g, ' ').split(PIREP_FIELD);
        const head = /(\S+) (UUA|UA) ?$/.exec(parts[0]) || [];
        const p = { station: head[1], urgent: head[2] === 'UUA', fields: {} };
        for (const part of parts.slice(1)) p.fields[part.slice(0, 2)] = part.slice(2).trim();
        if (/^\d{3}$/.test(p.fields.FL)) p.altitudeFt = p.fields.FL * 100;
        const hazard = (p.fields.TB || '') + ' ' + (p.fields.IC || '');
        p.severity = /SEV|EXTRM|HVY/.test(hazard) ? 3 : /MOD/.test(hazard) ? 2 : /LGT|TRACE/.test(hazard) ? 1 : 0;
        return p;
    }

    /**
     * [lat, lon] of a parsed pilot report, or null. Reads "ABC", "ABC090025" (magnetic bearing and nautical miles from ABC)
     * and "10 NE ABC"; uses the first point of a route and falls back to the reporting station.
     */
    function pirepPosition(p, decoder) {
        const ov = p.fields.OV || '';
        let id, bearing = 0, distance = 0;
        let m = /^(\d+) ?(?:NM |SM |MI(?:LES?)? )?([NSEW]{1,3}) (?:OF )?([A-Z0-9]{3,4})$/.exec(ov);
        if (m) [id, bearing, distance] = [m[3], COMPASS.indexOf(m[2]) * 22.5, +m[1]];
        else if ((m = /^([A-Z0-9]{3,4}?) ?(?:(\d{3})(\d{3}))?(?![A-Z0-9])/.exec(ov))) [id, bearing, distance] = [m[1], +m[2] || 0, +m[3] || 0];
        let base = locate(id, decoder);
        if (!base) { base = locate(p.station, decoder); distance = 0; }
        if (!base || !distance) return base && base.slice(0, 2);
        const course = (bearing + variation(base)) * Math.PI / 180;
        return [base[0] + distance * Math.cos(course) / 60, base[1] + distance * Math.sin(course) / 60 / Math.cos(base[0] * Math.PI / 180)];
    }

    const RADAR_COLORS = [null, null, '#5d5', '#181', '#fe0', '#f90', '#e00', '#d0d'];
    // Strike count classes 1, 2, 3-5, 6-10, 11-15 and above.
    const LIGHTNING_COLORS = [null, '#fd0', '#fb0', '#f80', '#f50', '#e20', '#d0d', null];
    // Cloud top height classes; CLOUD_TOP_FT holds their upper limits.
    const CLOUD_TOP_COLORS = [null, '#425', '#44a', '#36d', '#29d', '#1bb', '#2c8', '#6d4', '#ad2', '#dc2', '#fa2', '#f71', '#e31', '#b12', '#d3c', null];
    const CLOUD_TOP_FT = [1500, 3000, 4500, 6000, 7500, 9000, 10500, 12000, 13500, 15000, 18000, 21000, 24000];
    // Icing severity: trace, light, moderate, severe, heavy.
    const ICING_COLORS = [null, '#bef', '#7bf', '#36d', '#a0c', '#208', null, null];
    const ICING_NAMES = ['', 'Trace', 'Light', 'Moderate', 'Severe', 'Heavy'];
    // Eddy dissipation rate x 100 in steps of 7, drawn from 14.
    const TURBULENCE_COLORS = [null, null, '#cf7', '#ed3', '#fb3', '#f93', '#f72', '#f52', '#f02', '#e01', '#b01', '#901', '#701', '#500', '#400', null];
    const PIREP_COLORS = ['#9bd', '#fe0', '#f90', '#e00'];
    const PIREP_LABELS = { OV: 'Location', TM: 'Time', FL: 'Altitude', TP: 'Aircraft', SK: 'Sky', WX: 'Weather', TA: 'Temperature', WV: 'Wind',
                           TB: 'Turbulence', IC: 'Icing', RM: 'Remarks' };
    const ALTITUDES_FT = [2000, 4000, 6000, 8000, 10000, 12000, 14000, 16000, 18000, 20000, 22000, 24000];
    const CATEGORY_COLORS = { VFR: '#2a2', MVFR: '#27e', IFR: '#e22', LIFR: '#d2d' };
    const AREA_COLORS = { 8: '#e22', 18: '#e22', 19: '#e22', 11: '#d90', 12: '#e60', 13: '#888', 15: '#a4c', 16: '#a63', 17: '#a63' };
    const GAIRMET_COLORS = { IFR: '#c4c', MTN: '#a63', TURB: '#d80', ICING: '#38e', FRZLVL: '#4bd', LLWS: '#da0', SFC: '#888' };
    const CSS = '.fisb-ctl{display:flex;flex-direction:column}.fisb-ctl button,.fisb-ctl select{width:30px;height:30px;border:0;' +
        'border-bottom:1px solid #ccc;background:#fff;font:16px/30px sans-serif;padding:0;cursor:pointer;color:#222;position:relative}' +
        '.fisb-ctl select{font-size:12px;text-align:center;text-align-last:center;appearance:none;-webkit-appearance:none;border-radius:0}' +
        '.fisb-ctl button:last-child{border:0}.fisb-ctl button[aria-pressed=false]{color:#bbb;background:#f4f4f4}' +
        '.fisb-ctl button.fisb-none>span{opacity:.45}' +
        '.fisb-tip{display:none;position:absolute;top:0;left:34px;z-index:1000;background:#fff;color:#222;border:1px solid #999;border-radius:3px;' +
        'padding:2px 6px;font:12px/18px sans-serif;white-space:nowrap;text-align:left;cursor:default}.fisb-right .fisb-tip{left:auto;right:34px}' +
        '.fisb-ctl button:hover .fisb-tip{display:block}.fisb-tip i{display:inline-block;width:10px;height:10px;margin:0 3px 0 6px;border:1px solid #999}' +
        '.fisb-tip i:first-child{margin-left:0}.fisb-pirep{font:15px/14px sans-serif;text-align:center;text-shadow:0 0 2px #000,0 0 1px #000}' +
        '.fisb-urgent{font-size:21px}' +
        '.fisb-text{font:11px/1.35 monospace;white-space:pre-wrap;margin:0 0 6px;width:max-content;max-width:480px}.fisb-text b{font-family:sans-serif}' +
        '.fisb-gs{color:#222;font:14px/14px sans-serif;text-shadow:0 0 2px #fff,0 0 2px #fff}';

    const POPUP = { minWidth: 260, maxWidth: 500, maxHeight: 320 };

    // Map parts in button order.
    const SYMBOLS = { radar: '☂', lightning: '⚡\uFE0E', cloudTops: '☁\uFE0E', icing: '❄\uFE0E', turbulence: '≋', airports: '◉', pireps: '◆', areas: '⬡', stations: '▲' };
    // Color keys shown with a button's label: [color, text] pairs.
    const LEGENDS = {
        lightning: ['1', '2', '3–5', '6–10', '11–15', '16+ strikes'].map((text, i) => [LIGHTNING_COLORS[i + 1], text]),
        cloudTops: [1, 4, 7, 10, 12, 14].map((i) => [CLOUD_TOP_COLORS[i], i > 13 ? 'higher' : CLOUD_TOP_FT[i - 1] + (i > 1 ? '' : ' ft')]),
        icing: [1, 2, 3, 5, 4].map((i) => [ICING_COLORS[i], ICING_NAMES[i]]).concat([['#e00', 'Large droplets']]),
        turbulence: [2, 3, 5, 8, 11, 14].map((i) => [TURBULENCE_COLORS[i], i * 7 + (i > 13 ? '+ eddy dissipation rate × 100' : '')]),
        pireps: ['None', 'Light', 'Moderate', 'Severe turbulence or icing'].map((text, i) => [PIREP_COLORS[i], text]),
    };

    const hhmm = (ms) => new Date(ms).toISOString().slice(11, 16) + 'Z';
    const dayTime = (ms) => new Date(ms).toISOString().slice(5, 16).replace('T', ' ') + 'Z';
    const feet = (ft, agl) => (ft ? ft + ' ft' : agl ? 'SFC' : '0 ft');

    // Winds aloft as two aligned rows: altitudes, then wind and temperature groups.
    function windsTable(text) {
        const m = /^(WINDS \S+ \S+)\s+FT\s+([\d\s]+?)\n\s*(.+)$/.exec(text);
        if (!m) return text;
        const row = (cells) => cells.trim().split(/\s+/).map((c) => c.padEnd(7)).join(' ').trim();
        return m[1] + '\n' + row(m[2]) + '\n' + row(m[3]);
    }

    // Canvas overlays. products: drawn in this order. color(bin value) -> CSS color or null. levels: one altitude at a time.
    // minSize: smallest drawn cell in pixels, with a dark rim. dot(bin value) -> true for a red dot in the cell.
    const GRIDS = {
        // CONUS underneath, regional on top.
        radar: { products: [64, 63], color: (v) => RADAR_COLORS[v], opacity: 0.65 },
        lightning: { products: [103], color: (v) => LIGHTNING_COLORS[v & 7], opacity: 1, minSize: 6 },
        cloudTops: { products: [84], color: (v) => CLOUD_TOP_COLORS[v], opacity: 0.6 },
        icing: { products: [70, 71], color: (v) => ICING_COLORS[(v >> 3) & 7], opacity: 0.6, levels: true, dot: (v) => (v >> 6) % 3 > 0 },
        turbulence: { products: [90, 91], color: (v) => TURBULENCE_COLORS[v], opacity: 0.6, levels: true },
    };

    /** Canvas overlay for one entry of GRIDS. state.altitudeFt selects the level of icing and turbulence. */
    function gridLayer(L, decoder, grid, state) {
        return new (L.Layer.extend({
            onAdd(map) {
                const pane = map.getPane('fisb') || map.createPane('fisb');
                pane.style.zIndex = 350;
                pane.style.pointerEvents = 'none';
                this.canvas = L.DomUtil.create('canvas', 'leaflet-zoom-hide', pane);
                this.canvas.style.opacity = grid.opacity;
                map.on('move zoomend resize', this.redraw, this);
                this.redraw();
            },
            onRemove(map) {
                map.off('move zoomend resize', this.redraw, this);
                this.canvas.remove();
            },
            redraw() {
                const map = this._map;
                if (!map) return;
                const size = map.getSize(), view = map.getBounds(), ctx = this.canvas.getContext('2d');
                this.canvas.width = size.x;
                this.canvas.height = size.y;
                L.DomUtil.setPosition(this.canvas, map.containerPointToLayerPoint([0, 0]));
                const minSize = grid.minSize || 0;
                for (const productId of grid.products) {
                    for (const block of (decoder.grids.get(productId) || new Map()).values()) {
                        if (grid.levels && block.altitudeFt !== state.altitudeFt) continue;
                        const b = blockBounds(block.blockNumber, block.scale, block.south);
                        const south = b.north - 4 * b.binLat, east = b.west + 32 * b.binLon;
                        if (south > view.getNorth() || b.north < view.getSouth() || b.west > view.getEast() || east < view.getWest()) continue;
                        const x0 = map.latLngToContainerPoint([b.north, b.west]).x;
                        const dx = (map.latLngToContainerPoint([b.north, east]).x - x0) / 32;
                        const ys = [0, 1, 2, 3, 4].map((r) => Math.round(map.latLngToContainerPoint([b.north - r * b.binLat, b.west]).y));
                        // Regional radar replaces the coarser CONUS image where both exist.
                        if (productId === 63) ctx.clearRect(Math.round(x0), ys[0], Math.round(x0 + 32 * dx) - Math.round(x0), ys[4] - ys[0]);
                        if (!block.bins) continue;
                        for (let r = 0; r < 4; r++) {
                            for (let c = 0; c < 32;) {
                                const value = block.bins[r * 32 + c];
                                let end = c + 1;
                                while (end < 32 && block.bins[r * 32 + end] === value) end++;
                                const color = grid.color(value);
                                if (color) {
                                    let x = Math.round(x0 + c * dx), w = Math.round(x0 + end * dx) - x, y = ys[r], h = ys[r + 1] - y;
                                    if (w < minSize) { x -= (minSize - w) >> 1; w = minSize; }
                                    if (h < minSize) { y -= (minSize - h) >> 1; h = minSize; }
                                    if (minSize) {
                                        ctx.fillStyle = '#222';
                                        ctx.fillRect(x - 1, y - 1, w + 2, h + 2);
                                    }
                                    ctx.fillStyle = color;
                                    ctx.fillRect(x, y, w, h);
                                    if (grid.dot && dx > 5 && grid.dot(value)) {
                                        ctx.fillStyle = '#e00';
                                        for (let k = c; k < end; k++) ctx.fillRect(Math.round(x0 + (k + 0.5) * dx) - 1, y + (h >> 1) - 1, 3, 3);
                                    }
                                }
                                c = end;
                            }
                        }
                    }
                }
            },
        }))();
    }

    /** Distinct outlines of a report with their altitude range and time windows. */
    function reportOutlines(report) {
        const outlines = new Map();
        for (const s of report.shapes) {
            if (!s.shape || s.shape === 'point') continue;
            const key = s.shape + JSON.stringify(s.points || [s.center, s.radiusNm]) + (s.element || '');
            let o = outlines.get(key);
            if (!o) {
                outlines.set(key, o = { shape: s.shape, points: s.points, center: s.center, radiusNm: s.radiusNm, element: s.element,
                                        conditions: s.conditions, lo: Infinity, hi: 0, times: [] });
            }
            // Altitudes above ground level only mark the surface here.
            if (!s.agl || s.hi) { o.lo = Math.min(o.lo, s.lo); o.hi = Math.max(o.hi, s.hi); } else o.lo = 0;
            if (s.startMs || s.stopMs) {
                if (!o.times.some((t) => t[0] === s.startMs && t[1] === s.stopMs)) o.times.push([s.startMs, s.stopMs]);
            }
        }
        return [...outlines.values()];
    }

    const isActive = (outline, nowMs) => !outline.times.length || outline.times.some((t) => (t[0] || 0) <= nowMs && nowMs < (t[1] || Infinity));

    /**
     * Leaflet layer showing a Decoder's reports. Adding it to a map also adds its toggle control.
     * @param {object} L Leaflet namespace.
     * @param {Decoder} decoder
     * @param {{stationsUrl?: string, position?: string, show?: object, altitudeFt?: number}} [options]
     *     show: parts shown at the start, by the names in SYMBOLS. altitudeFt: icing and turbulence level.
     *     Without them the layer starts as the user left it.
     */
    function createLayer(L, decoder, options) {
        const o = Object.assign({ stationsUrl: 'fisb_stations.js', position: 'topright' }, options);
        let saved = {};
        try { saved = JSON.parse(root.localStorage.getItem('fisbLayer')) || {}; } catch (_) { /* No storage. */ }
        const show = Object.assign({ radar: true, airports: true, areas: true, stations: true }, saved.show, o.show);
        const state = { altitudeFt: o.altitudeFt || saved.altitudeFt || 8000 };
        const save = () => {
            try { root.localStorage.setItem('fisbLayer', JSON.stringify({ show, altitudeFt: state.altitudeFt })); } catch (_) { /* No storage. */ }
        };
        const doc = root.document;
        const layer = L.layerGroup();
        const parts = {};
        for (const name in SYMBOLS) parts[name] = GRIDS[name] ? gridLayer(L, decoder, GRIDS[name], state) : L.layerGroup();
        const drawn = { airports: new Map(), pireps: new Map(), areas: new Map(), stations: new Map() };
        const buttons = {}, tips = {};
        let timer = null, unsubscribe = null, stationsRequested = false, altitude = null;

        const el = (tag, className, text) => {
            const e = doc.createElement(tag);
            if (className) e.className = className;
            if (text) e.textContent = text;
            return e;
        };
        const textBlock = (title, text) => {
            const pre = el('pre', 'fisb-text');
            if (title) { pre.appendChild(el('b', '', title)); pre.appendChild(doc.createTextNode('\n')); }
            pre.appendChild(doc.createTextNode(text));
            return pre;
        };

        // Adds, replaces and removes Leaflet objects so that the group matches items [{key, signature, make}].
        const sync = (name, items) => {
            const cache = drawn[name], keep = new Set();
            for (const item of items) {
                keep.add(item.key);
                const old = cache.get(item.key);
                if (old && old.signature === item.signature) continue;
                if (old) parts[name].removeLayer(old.object);
                const object = item.make();
                cache.set(item.key, { signature: item.signature, object });
                parts[name].addLayer(object);
                // Areas stay beneath airports and ground stations.
                if (name === 'areas') object.bringToBack();
            }
            for (const [key, old] of cache) {
                if (!keep.has(key)) { parts[name].removeLayer(old.object); cache.delete(key); }
            }
        };

        const loadStations = () => {
            if (stationTable || stationsRequested || !o.stationsUrl || !doc) return;
            stationsRequested = true;
            if (root.FISB_STATIONS) return;
            const script = el('script');
            script.src = o.stationsUrl;
            script.onload = () => refresh();
            doc.head.appendChild(script);
        };

        const airportItems = () => {
            const airports = new Map();
            const at = (id) => {
                if (!airports.has(id)) airports.set(id, { id, notams: [], winds: [] });
                return airports.get(id);
            };
            for (const t of decoder.texts.values()) {
                if (t.kind === 'METAR') at(t.id).metar = t;
                else if (t.kind === 'TAF') at(t.id).taf = t;
                else if (t.kind === 'WINDS') at(t.id.length === 3 ? 'K' + t.id : t.id).winds.push(t);
            }
            for (const r of decoder.reports.values()) {
                const point = r.shapes.find((s) => s.shape === 'point' && s.label);
                if (point && r.text) at(point.label).notams.push(r);
            }
            const items = [];
            for (const a of airports.values()) {
                const position = stationPosition(a.id, decoder);
                if (!position || !(a.metar || a.taf || a.notams.length)) continue;
                const color = a.metar ? CATEGORY_COLORS[a.metar.category] || '#999' : '#999';
                items.push({
                    key: a.id,
                    signature: [color, a.metar && a.metar.timeMs, a.taf && a.taf.timeMs, a.notams.length, a.winds.length].join(),
                    make: () => {
                        const marker = L.circleMarker(position, {
                            radius: a.metar ? 5 : 3, color: '#222', weight: 1, fillColor: color, fillOpacity: a.metar ? 0.95 : 0.6,
                        });
                        const metar = a.metar && a.metar.text.replace(/\s+/g, ' ');
                        marker.bindTooltip(() => textBlock(metar ? '' : a.id, metar || (a.taf ? a.taf.text : a.notams.length + ' NOTAM')));
                        marker.bindPopup(() => {
                            const box = el('div');
                            if (metar) box.appendChild(textBlock('', metar));
                            if (a.taf) box.appendChild(textBlock('', a.taf.text));
                            for (const w of a.winds.sort((x, y) => x.timeMs - y.timeMs)) box.appendChild(textBlock('', windsTable(w.text)));
                            for (const n of a.notams) box.appendChild(textBlock('', n.text));
                            return box;
                        }, POPUP);
                        return marker;
                    },
                });
            }
            return items;
        };

        const pirepItems = () => {
            const items = [];
            for (const t of decoder.texts.values()) {
                if (t.kind !== 'PIREP') continue;
                const p = parsePirep(t.text), position = pirepPosition(p, decoder);
                if (!position) continue;
                items.push({
                    key: t.key,
                    signature: position.join(),
                    make: () => {
                        const icon = L.divIcon({
                            className: 'fisb-pirep' + (p.urgent ? ' fisb-urgent' : ''), iconSize: [14, 14],
                            html: '<span style="color:' + PIREP_COLORS[p.severity] + '">&#9670;</span>',
                        });
                        const marker = L.marker(position, { icon, keyboard: false });
                        marker.bindTooltip(() => textBlock('', t.text.replace(/^PIREP \S+ \S+ /, '')));
                        marker.bindPopup(() => {
                            const lines = [];
                            for (const code in PIREP_LABELS) {
                                let value = p.fields[code];
                                if (!value) continue;
                                if (code === 'FL' && p.altitudeFt !== undefined) value = feet(p.altitudeFt);
                                if (code === 'TM') value = value.replace(/^(\d\d)(\d\d)$/, '$1:$2Z');
                                if (code === 'TA') value = value.replace(/^M/, '-') + ' °C';
                                lines.push(PIREP_LABELS[code] + ': ' + value);
                            }
                            const box = el('div');
                            box.appendChild(textBlock((p.urgent ? 'Urgent pilot report' : 'Pilot report') + ' · ' + p.station, lines.join('\n')));
                            box.appendChild(textBlock('', t.text));
                            return box;
                        }, POPUP);
                        return marker;
                    },
                });
            }
            return items;
        };

        const areaItems = (nowMs) => {
            const items = [], seen = new Set();
            // A TFR can arrive under several product ids; draw the copy that has its text.
            const reports = [...decoder.reports.values()].sort((a, b) => !a.text - !b.text);
            for (const r of reports) {
                reportOutlines(r).forEach((outline, index) => {
                    const geometry = r.year + '/' + r.number + JSON.stringify(outline.points || [outline.center, outline.radiusNm]);
                    if (r.productId !== 14 && seen.has(geometry)) return;
                    seen.add(geometry);
                    const active = isActive(outline, nowMs);
                    // Graphical AIRMETs come as a series of forecast snapshots; show the current one.
                    if (r.productId === 14 && !active) return;
                    const color = (r.productId === 14 ? GAIRMET_COLORS[outline.element] : AREA_COLORS[r.productId]) || '#888';
                    // Only turbulence, icing and freezing level AIRMETs carry real altitudes.
                    const altitudes = outline.hi && (r.productId !== 14 || /TURB|ICING|FRZLVL/.test(outline.element));
                    const firstLine = r.text.split('\n')[0];
                    const title = (firstLine.length > 40 ? firstLine.slice(0, 40) + '…' : firstLine || r.product) +
                        (outline.element ? ' ' + outline.element : '') + (outline.conditions ? ' ' + outline.conditions.join(' ') : '') +
                        (altitudes ? ' · ' + (outline.lo === outline.hi ? '' : feet(outline.lo === Infinity ? 0 : outline.lo, true) + '–') + feet(outline.hi) : '');
                    const times = outline.times.map((t) => (t[0] ? dayTime(t[0]) : '') + ' → ' + (t[1] ? dayTime(t[1]) : '')).join('\n');
                    items.push({
                        key: r.key + '#' + index,
                        signature: [active, title, r.text.length, times, JSON.stringify(outline.points || outline.center)].join(),
                        make: () => {
                            const style = { color, weight: 2, dashArray: active ? null : '6 5', fillOpacity: active ? 0.1 : 0.03, interactive: false };
                            // Only the outline reacts to the pointer, so large areas leave the map usable: an unseen wide line on top of it.
                            const wide = { weight: 14, opacity: 0, fill: false };
                            const circle = (options) => L.circle(outline.center, Object.assign({ radius: outline.radiusNm * 1852 }, options));
                            const closed = outline.shape === 'polygon';
                            const seen = outline.shape === 'circle' ? circle(style) :
                                closed ? L.polygon(outline.points, style) : L.polyline(outline.points, Object.assign({ fill: false }, style));
                            const edge = outline.shape === 'circle' ? circle(wide) :
                                L.polyline(closed ? outline.points.concat([outline.points[0]]) : outline.points, wide);
                            // An element keeps received text from being parsed as HTML.
                            edge.bindTooltip(() => el('span', '', title), { sticky: true });
                            edge.bindPopup(() => {
                                const box = el('div');
                                box.appendChild(textBlock(title, times));
                                if (r.text) box.appendChild(textBlock('', r.text));
                                return box;
                            }, POPUP);
                            return L.featureGroup([seen, edge]);
                        },
                    });
                });
            }
            return items;
        };

        const stationItems = () => [...decoder.stations.values()].map((s) => ({
            key: s.key,
            signature: s.key,
            make: () => L.marker([s.lat, s.lon], { icon: L.divIcon({ className: 'fisb-gs', html: '&#9650;', iconSize: [14, 14] }), keyboard: false })
                .bindTooltip(() => {
                    const now = decoder.stations.get(s.key) || s;
                    return textBlock('', now.lat.toFixed(4) + ', ' + now.lon.toFixed(4) + '\n#' + now.tisbSiteId + ' · ' + now.uplinks + '×' +
                        (now.rssiDbm !== undefined ? ' · ' + now.rssiDbm + ' dBm' : '') + ' · ' + hhmm(now.rxMs));
                }),
        }));

        function refresh() {
            timer = null;
            const nowMs = decoder.timeMs || decoder.now();
            if (decoder.texts.size) loadStations();
            const lists = { airports: airportItems(), pireps: pirepItems(), areas: areaItems(nowMs), stations: stationItems() };
            for (const name in lists) sync(name, lists[name]);
            // Newest product time of each grid, at the selected level where there are levels.
            const times = {};
            for (const name in GRIDS) {
                parts[name].redraw();
                times[name] = GRIDS[name].products.map((id) => {
                    let newest = 0;
                    for (const b of (decoder.grids.get(id) || new Map()).values()) {
                        if (!GRIDS[name].levels || b.altitudeFt === state.altitudeFt) newest = Math.max(newest, b.timeMs);
                    }
                    return newest;
                });
            }
            const time = (name) => { const newest = Math.max(...times[name]); return newest ? ' ' + hhmm(newest) : ''; };
            const level = ' ' + state.altitudeFt + ' ft';
            const labels = {
                radar: 'NEXRAD' + (times.radar[1] ? ' ' + hhmm(times.radar[1]) : '') + (times.radar[0] ? ' · CONUS ' + hhmm(times.radar[0]) : ''),
                lightning: 'Lightning' + time('lightning'),
                cloudTops: 'Cloud tops' + time('cloudTops'),
                icing: 'Icing' + level + time('icing'),
                turbulence: 'Turbulence' + level + time('turbulence'),
                airports: 'METAR/TAF/NOTAM ' + lists.airports.length,
                pireps: 'Pilot reports ' + lists.pireps.length,
                areas: 'TFR/SIGMET/AIRMET ' + lists.areas.length,
                stations: 'FIS-B ' + lists.stations.length,
            };
            for (const name in buttons) {
                tips[name].textContent = labels[name];
                buttons[name].setAttribute('aria-label', labels[name]);
                buttons[name].classList.toggle('fisb-none', lists[name] ? !lists[name].length : !Math.max(...times[name]));
            }
        }
        const schedule = () => { if (!timer) timer = setTimeout(refresh, 500); };

        const control = L.control({ position: o.position });
        control.onAdd = () => {
            if (!doc.getElementById('fisb-css')) {
                const style = el('style');
                style.id = 'fisb-css';
                style.textContent = CSS;
                doc.head.appendChild(style);
            }
            const box = el('div', 'fisb-ctl leaflet-bar' + (/right/.test(o.position) ? ' fisb-right' : ''));
            for (const name in SYMBOLS) {
                const button = buttons[name] = el('button');
                button.type = 'button';
                button.setAttribute('aria-pressed', !!show[name]);
                button.onclick = () => layer.setVisible(name, !show[name]);
                button.appendChild(el('span', '', SYMBOLS[name]));
                // Shown on hover: the label, then the color key.
                const tip = button.appendChild(el('div', 'fisb-tip'));
                tips[name] = tip.appendChild(el('div'));
                if (LEGENDS[name]) {
                    const key = tip.appendChild(el('div'));
                    for (const [color, text] of LEGENDS[name]) {
                        key.appendChild(el('i')).style.background = color;
                        key.appendChild(doc.createTextNode(text));
                    }
                }
                box.appendChild(button);
                if (name !== 'turbulence') continue;
                altitude = box.appendChild(el('select'));
                altitude.title = 'Icing and turbulence altitude, 1000 ft above sea level';
                for (const ft of ALTITUDES_FT) {
                    const option = altitude.appendChild(el('option', '', String(ft / 1000)));
                    option.value = ft;
                    option.selected = ft === state.altitudeFt;
                }
                altitude.onchange = () => layer.setAltitude(+altitude.value);
            }
            showAltitude();
            L.DomEvent.disableClickPropagation(box);
            return box;
        };
        const showAltitude = () => { if (altitude) altitude.style.display = show.icing || show.turbulence ? '' : 'none'; };

        /** Shows or hides one part, by its name in SYMBOLS. */
        layer.setVisible = (name, visible) => {
            show[name] = visible;
            if (visible) layer.addLayer(parts[name]); else layer.removeLayer(parts[name]);
            if (visible && name === 'areas') parts.areas.eachLayer((area) => area.bringToBack());
            if (buttons[name]) buttons[name].setAttribute('aria-pressed', visible);
            showAltitude();
            save();
        };
        /** Selects the icing and turbulence level, in feet. */
        layer.setAltitude = (ft) => {
            state.altitudeFt = ft;
            if (altitude) altitude.value = ft;
            save();
            refresh();
        };
        layer.refresh = refresh;
        layer.control = control;
        layer.parts = parts;
        for (const name in parts) if (show[name]) layer.addLayer(parts[name]);

        const onAdd = layer.onAdd, onRemove = layer.onRemove;
        layer.onAdd = function (map) {
            onAdd.call(this, map);
            control.addTo(map);
            unsubscribe = decoder.on(schedule);
            refresh();
        };
        layer.onRemove = function (map) {
            onRemove.call(this, map);
            control.remove();
            if (unsubscribe) unsubscribe();
            clearTimeout(timer);
            timer = null;
        };
        return layer;
    }

    const api = {
        Decoder, createLayer, deinterleave, parseRawLine, parseUplinkMessage, parseUplinkLine, isUplinkLine, hexToBytes, flightCategory, blockBounds, resolveTime, setStations, stationPosition,
        parsePirep, pirepPosition, reportOutlines, PRODUCT_NAMES, RADAR_COLORS, CATEGORY_COLORS, GRIDS, ALTITUDES_FT,
        decode: { uplinkHeader: decodeUplinkHeader, frames: splitFrames, apduHeader: decodeApduHeader, text: decodeText, twgo: decodeTwgo, grid: decodeGrid, crl: decodeCrl, dlac },
    };
    if (typeof module !== 'undefined' && module.exports) module.exports = api;
    else root.Fisb = api;
})(typeof window !== 'undefined' ? window : globalThis);
