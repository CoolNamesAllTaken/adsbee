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
            this.reports = new Map();   // NOTAM, AIRMET, SIGMET, ... by "product/year/number".
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
                if (!h.segmented) return this.ingestProduct(h.productId, h.payload, h, nowMs);
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
                    this.ingestProduct(h.productId, joined, h, nowMs);
                }
            } else if (frame.type === 14) {
                const list = decodeCrl(frame.data);
                list.station = station ? station.key : '';
                list.rxMs = nowMs;
                list.expiresMs = nowMs + 5 * MIN;
                this.crl.set(list.station + '/' + list.productId + (list.tfr ? 'T' : ''), list);
                this.emit('crl', list);
            } else if (frame.type !== 15) {  // 15: traffic service status, unrelated to FIS-B.
                this.stats.unknownFrames[frame.type] = (this.stats.unknownFrames[frame.type] || 0) + 1;
            }
        }

        ingestProduct(productId, payload, header, nowMs) {
            const count = (table) => { table[productId] = (table[productId] || 0) + 1; };
            if (productId === 413) {
                count(this.stats.products);
                for (const t of decodeText(payload)) this.storeText(t, nowMs);
            } else if (TWGO_PRODUCTS.includes(productId)) {
                count(this.stats.products);
                this.storeTwgo(productId, decodeTwgo(payload, productId), nowMs);
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

        storeTwgo(productId, twgo, nowMs) {
            const get = (r) => {
                const key = productId + '/' + r.year + '/' + r.number;
                let report = this.reports.get(key);
                if (!report) {
                    report = { key, productId, product: PRODUCT_NAMES[productId], number: r.number, year: r.year, text: '', shapes: [] };
                    this.reports.set(key, report);
                }
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

    let stationTable = null;

    /** Loads the station table from fisb_stations.js (a string, see that file). */
    function setStations(data) {
        stationTable = new Map();
        for (let i = 0; i + 10 <= data.length; i += 10) {
            stationTable.set(data.substr(i, 4), [parseInt(data.substr(i + 4, 3), 36) / 100 - 90, parseInt(data.substr(i + 7, 3), 36) / 100 - 180]);
        }
    }

    /** [lat, lon] of a weather station or airport, or null when unknown. */
    function stationPosition(id, decoder) {
        if (!stationTable && root.FISB_STATIONS) setStations(root.FISB_STATIONS);
        return (stationTable && (stationTable.get(id) || stationTable.get('K' + id))) || (decoder && decoder.airports.get(id)) || null;
    }

    const RADAR_COLORS = [null, null, '#5d5', '#181', '#fe0', '#f90', '#e00', '#d0d'];
    const CATEGORY_COLORS = { VFR: '#2a2', MVFR: '#27e', IFR: '#e22', LIFR: '#d2d' };
    const AREA_COLORS = { 8: '#e22', 18: '#e22', 19: '#e22', 11: '#d90', 12: '#e60', 13: '#888', 15: '#a4c', 16: '#a63', 17: '#a63' };
    const GAIRMET_COLORS = { IFR: '#c4c', MTN: '#a63', TURB: '#d80', ICING: '#38e', FRZLVL: '#4bd', LLWS: '#da0', SFC: '#888' };
    const CSS = '.fisb-ctl{display:flex;flex-direction:column}.fisb-ctl button{width:30px;height:30px;border:0;border-bottom:1px solid #ccc;' +
        'background:#fff;font:16px/30px sans-serif;padding:0;cursor:pointer;color:#222}.fisb-ctl button:last-child{border:0}' +
        '.fisb-ctl button[aria-pressed=false]{color:#bbb;background:#f4f4f4}.fisb-ctl button.fisb-none{opacity:.45}' +
        '.fisb-text{font:11px/1.35 monospace;white-space:pre-wrap;margin:0 0 6px;width:max-content;max-width:420px}.fisb-text b{font-family:sans-serif}' +
        '.fisb-gs{color:#222;font:14px/14px sans-serif;text-shadow:0 0 2px #fff,0 0 2px #fff}';

    const POPUP = { minWidth: 260, maxWidth: 440, maxHeight: 320 };

    const hhmm = (ms) => new Date(ms).toISOString().slice(11, 16) + 'Z';
    const dayTime = (ms) => new Date(ms).toISOString().slice(5, 16).replace('T', ' ') + 'Z';
    const feet = (ft, agl) => (ft ? ft + ' ft' : agl ? 'SFC' : '0 ft');

    /** Canvas overlay for NEXRAD: CONUS underneath, regional on top. */
    function radarLayer(L, decoder) {
        return new (L.Layer.extend({
            onAdd(map) {
                const pane = map.getPane('fisb') || map.createPane('fisb');
                pane.style.zIndex = 350;
                pane.style.pointerEvents = 'none';
                this.canvas = L.DomUtil.create('canvas', 'leaflet-zoom-hide', pane);
                this.canvas.style.opacity = 0.65;
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
                for (const productId of [64, 63]) {
                    for (const block of (decoder.grids.get(productId) || new Map()).values()) {
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
                                if (RADAR_COLORS[value]) {
                                    const xa = Math.round(x0 + c * dx), xb = Math.round(x0 + end * dx);
                                    ctx.fillStyle = RADAR_COLORS[value];
                                    ctx.fillRect(xa, ys[r], xb - xa, ys[r + 1] - ys[r]);
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
            if (s.shape === 'point') continue;
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
     * @param {{stationsUrl?: string, position?: string, show?: object}} [options] show: {radar, airports, areas, stations}.
     */
    function createLayer(L, decoder, options) {
        const o = Object.assign({ stationsUrl: 'fisb_stations.js', position: 'topright' }, options);
        const show = Object.assign({ radar: true, airports: true, areas: true, stations: true }, o.show);
        const doc = root.document;
        const layer = L.layerGroup();
        const parts = { radar: radarLayer(L, decoder), airports: L.layerGroup(), areas: L.layerGroup(), stations: L.layerGroup() };
        const drawn = { airports: new Map(), areas: new Map(), stations: new Map() };
        const buttons = {};
        let timer = null, unsubscribe = null, stationsRequested = false;

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
                        marker.bindTooltip(() => textBlock(a.metar ? '' : a.id,
                            a.metar ? a.metar.text.replace(/\s+/g, ' ') : a.taf ? a.taf.text : a.notams.length + ' NOTAM'));
                        marker.bindPopup(() => {
                            const box = el('div');
                            if (a.metar) box.appendChild(textBlock('', a.metar.text));
                            if (a.taf) box.appendChild(textBlock('', a.taf.text));
                            for (const w of a.winds.sort((x, y) => x.timeMs - y.timeMs)) box.appendChild(textBlock('', w.text));
                            for (const n of a.notams) box.appendChild(textBlock('', n.text));
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
                            const style = { color, weight: 2, dashArray: active ? null : '6 5', fillOpacity: active ? 0.1 : 0.03 };
                            // Only the outline of a polygon reacts to the pointer, so large areas leave the map usable.
                            const edge = outline.shape === 'circle' ? L.circle(outline.center, Object.assign({ radius: outline.radiusNm * 1852 }, style)) :
                                L.polyline(outline.points, Object.assign({}, style, { fill: false }));
                            edge.bindTooltip(title, { sticky: true });
                            edge.bindPopup(() => {
                                const box = el('div');
                                box.appendChild(textBlock(title, times));
                                if (r.text) box.appendChild(textBlock('', r.text));
                                return box;
                            }, POPUP);
                            if (outline.shape !== 'polygon') return edge;
                            return L.featureGroup([L.polygon(outline.points, Object.assign({}, style, { stroke: false, interactive: false })), edge]);
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
            const airports = airportItems(), areas = areaItems(nowMs), stations = stationItems();
            sync('airports', airports);
            sync('areas', areas);
            sync('stations', stations);
            parts.radar.redraw();
            const radarTimes = [63, 64].map((id) => {
                let newest = 0;
                for (const b of (decoder.grids.get(id) || new Map()).values()) newest = Math.max(newest, b.timeMs);
                return newest;
            });
            const labels = {
                radar: 'NEXRAD' + (radarTimes[0] ? ' ' + hhmm(radarTimes[0]) : '') + (radarTimes[1] ? ' · CONUS ' + hhmm(radarTimes[1]) : ''),
                airports: 'METAR/TAF/NOTAM ' + airports.length,
                areas: 'TFR/SIGMET/AIRMET ' + areas.length,
                stations: 'FIS-B ' + stations.length,
            };
            const empty = { radar: !radarTimes[0] && !radarTimes[1], airports: !airports.length, areas: !areas.length, stations: !stations.length };
            for (const name in buttons) {
                buttons[name].title = labels[name];
                buttons[name].classList.toggle('fisb-none', empty[name]);
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
            const box = el('div', 'fisb-ctl leaflet-bar');
            const symbols = { radar: '☂', airports: '◉', areas: '⬡', stations: '▲' };
            for (const name in symbols) {
                const button = buttons[name] = el('button', '', symbols[name]);
                button.type = 'button';
                button.setAttribute('aria-pressed', show[name]);
                button.onclick = () => layer.setVisible(name, !show[name]);
                box.appendChild(button);
            }
            L.DomEvent.disableClickPropagation(box);
            return box;
        };

        /** Shows or hides one part: 'radar', 'airports', 'areas' or 'stations'. */
        layer.setVisible = (name, visible) => {
            show[name] = visible;
            if (visible) layer.addLayer(parts[name]); else layer.removeLayer(parts[name]);
            if (visible && name === 'areas') parts.areas.eachLayer((area) => area.bringToBack());
            if (buttons[name]) buttons[name].setAttribute('aria-pressed', visible);
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
        Decoder, createLayer, deinterleave, parseRawLine, hexToBytes, flightCategory, blockBounds, resolveTime, setStations, stationPosition,
        reportOutlines, PRODUCT_NAMES, RADAR_COLORS, CATEGORY_COLORS,
        decode: { uplinkHeader: decodeUplinkHeader, frames: splitFrames, apduHeader: decodeApduHeader, text: decodeText, twgo: decodeTwgo, grid: decodeGrid, crl: decodeCrl, dlac },
    };
    if (typeof module !== 'undefined' && module.exports) module.exports = api;
    else root.Fisb = api;
})(typeof window !== 'undefined' ? window : globalThis);
