// Tests for the paths that bring UAT uplinks to the weather layer: /uplink messages, AIRCRAFT_JSON_UAT_UPLINK lines,
// MapWeather, and the consoles' serial protocol choice and line routing. Runs in CI (web_ui_test job).
// Run: node --test firmware/adsbee_1090/esp/main/server/web/test/fisb_ingest.test.js
'use strict';
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const zlib = require('node:zlib');
const Fisb = require('../fisb.js');

const REPO = path.join(__dirname, '../../../../../../..');
const CONSOLES = ['adsbee_1090_console', 'adsbee_1421_console'];
const consoleHtml = (name) => fs.readFileSync(path.join(REPO, `software/${name}/${name}.html`), 'utf8');
const LINES = zlib.gunzipSync(fs.readFileSync(path.join(__dirname, 'fisb_data/sjc_20261011.txt.gz'))).toString().split('\n');
const PAYLOAD = Fisb.parseRawLine(LINES[0]).payload;

function uplinkMessage(rssi, timestampMs, extraBytes = 0) {
    const message = new Uint8Array(440 + extraBytes);
    message.set(PAYLOAD);
    const view = new DataView(message.buffer);
    view.setInt8(432, rssi);
    view.setUint32(436, timestampMs, true);
    return message;
}
const uplinkLine = (fields) => JSON.stringify(Object.assign({ uat_uplink: Buffer.from(PAYLOAD).toString('base64') }, fields));

test('parseUplinkMessage reads the fields by offset', () => {
    const uplink = Fisb.parseUplinkMessage(uplinkMessage(-87, 0xFEDCBA98).buffer);
    assert.deepStrictEqual([...uplink.payload], [...PAYLOAD]);
    assert.deepStrictEqual(uplink.meta, { deviceMs: 0xFEDCBA98, rssiDbm: -87 });
});

test('parseUplinkMessage ignores appended bytes, unknown RSSI and short messages', () => {
    const longer = Fisb.parseUplinkMessage(uplinkMessage(-128, 5, 12));
    assert.strictEqual(longer.payload.length, 432);
    assert.deepStrictEqual(longer.meta, { deviceMs: 5 });
    assert.strictEqual(Fisb.parseUplinkMessage(new Uint8Array(439)), null);
    // A view into a larger buffer.
    const padded = new Uint8Array(500);
    padded.set(uplinkMessage(-60, 7), 60);
    assert.deepStrictEqual(Fisb.parseUplinkMessage(padded.subarray(60)).meta, { deviceMs: 7, rssiDbm: -60 });
});

test('parseUplinkLine decodes the Base64 payload', () => {
    const uplink = Fisb.parseUplinkLine(uplinkLine({ rssi: -80, t: 123456 }) + '\r');
    assert.deepStrictEqual([...uplink.payload], [...PAYLOAD]);
    assert.deepStrictEqual(uplink.meta, { rssiDbm: -80, deviceMs: 123456 });
    assert.deepStrictEqual(Fisb.parseUplinkLine(uplinkLine({ t: 1 })).meta, { deviceMs: 1 });
});

test('parseUplinkLine rejects other and damaged lines', () => {
    const line = uplinkLine({ rssi: -80, t: 1 });
    assert.strictEqual(Fisb.parseUplinkLine('{"hex":"a1b2c3","lat":37.1}'), null);
    assert.strictEqual(Fisb.isUplinkLine('{"hex":"a1b2c3","lat":37.1}'), false);
    assert.strictEqual(Fisb.parseUplinkLine('OK'), null);
    for (const damaged of [line.slice(0, 300), line.replace('AA', '!!'), JSON.stringify({ uat_uplink: 'AAAA' })]) {
        assert.strictEqual(Fisb.isUplinkLine(damaged), true);
        assert.strictEqual(Fisb.parseUplinkLine(damaged), null);
    }
});

test('both transports give the decoder the same uplinks', () => {
    const viaSocket = new Fisb.Decoder(), viaSerial = new Fisb.Decoder();
    for (const raw of LINES.slice(0, 400).filter(Boolean)) {
        const payload = Fisb.parseRawLine(raw).payload;
        const message = new Uint8Array(440);
        message.set(payload);
        const a = Fisb.parseUplinkMessage(message);
        const b = Fisb.parseUplinkLine(JSON.stringify({ uat_uplink: Buffer.from(payload).toString('base64'), t: 1 }));
        viaSocket.ingestUplink(a.payload, { timestampMs: 1 });
        viaSerial.ingestUplink(b.payload, { timestampMs: 1 });
    }
    assert.ok(viaSocket.texts.size > 20);
    assert.deepStrictEqual([...viaSerial.texts.keys()], [...viaSocket.texts.keys()]);
    assert.deepStrictEqual(viaSerial.stats, viaSocket.stats);
});

// Stand-ins for the browser objects adsbee.js uses.
class FakeWebSocket {
    constructor(url) { this.url = url; this.closed = false; FakeWebSocket.opened.push(this); }
    close() { this.closed = true; if (this.onclose) this.onclose(); }
}
FakeWebSocket.opened = [];
const listeners = {};
const appended = [];
global.WebSocket = FakeWebSocket;
global.document = {
    hidden: false,
    head: { appendChild: (el) => { appended.push(el); setImmediate(() => { global.window.Fisb = fakeFisb; el.onload(); }); } },
    createElement: (tag) => ({ tag }),
    addEventListener: (type, fn) => { listeners[type] = fn; },
};
global.window = {};
global.L = {};
const layers = [];
const fakeFisb = global.Fisb = {
    Decoder: Fisb.Decoder,
    parseUplinkMessage: Fisb.parseUplinkMessage,
    createLayer: (L, decoder, options) => {
        const layer = { options, onMap: false, addTo(map) { this.onMap = true; map.layer = this; }, remove() { this.onMap = false; }, refresh() { } };
        layers.push(layer);
        return layer;
    },
};
const fakeMap = { hasLayer: (layer) => layer.onMap };
const { UplinkWebSocket, MapWeather } = require('../adsbee.js');
const settle = () => new Promise((resolve) => setImmediate(() => setImmediate(resolve)));

test('UplinkWebSocket delivers binary messages and reconnects until stopped', (t) => {
    t.mock.timers.enable({ apis: ['setTimeout'] });
    FakeWebSocket.opened.length = 0;
    const got = [];
    const socket = new UplinkWebSocket('ws://device/uplink');
    assert.strictEqual(FakeWebSocket.opened.length, 0);
    socket.start((uplink) => got.push(uplink));
    const first = FakeWebSocket.opened[0];
    assert.strictEqual(first.url, 'ws://device/uplink');
    assert.strictEqual(first.binaryType, 'arraybuffer');
    first.onmessage({ data: uplinkMessage(-70, 9).buffer });
    first.onmessage({ data: 'text' });
    first.onmessage({ data: new ArrayBuffer(10) });
    assert.strictEqual(got.length, 1);
    assert.strictEqual(got[0].meta.rssiDbm, -70);

    first.onclose();
    t.mock.timers.tick(5000);
    assert.strictEqual(FakeWebSocket.opened.length, 2);
    socket.stop();
    assert.strictEqual(FakeWebSocket.opened[1].closed, true);
    t.mock.timers.tick(60000);
    assert.strictEqual(FakeWebSocket.opened.length, 2);
});

test('MapWeather loads and connects nothing while off', async () => {
    appended.length = 0;
    delete global.window.Fisb;
    const calls = [];
    const source = { start: (fn) => { calls.push('start'); source.onUplink = fn; }, stop: () => calls.push('stop') };
    const weather = new MapWeather({ source, scriptUrl: 'fisb.js', stationsUrl: 'fisb_stations.js' });
    assert.strictEqual(weather.enabled, false);
    weather.attach(fakeMap);
    weather.setMapShown(true);
    await settle();
    assert.deepStrictEqual([calls, appended.length, layers.length], [[], 0, 0]);

    weather.setEnabled(true);
    await settle();
    assert.strictEqual(appended[0].src, 'fisb.js');
    assert.deepStrictEqual(calls, ['start']);
    assert.strictEqual(layers[0].onMap, true);
    assert.strictEqual(layers[0].options.stationsUrl, 'fisb_stations.js');
    source.onUplink({ payload: PAYLOAD, meta: {} });
    assert.strictEqual(weather.decoder.stats.uplinks, 1);

    // The source runs only while the map is shown, the page is visible and no update is in progress.
    weather.setMapShown(false);
    weather.setMapShown(true);
    global.document.hidden = true;
    listeners.visibilitychange();
    global.document.hidden = false;
    listeners.visibilitychange();
    weather.setPaused(true);
    weather.setPaused(false);
    await settle();
    assert.deepStrictEqual(calls, ['start', 'stop', 'start', 'stop', 'start', 'stop', 'start']);
    assert.strictEqual(layers[0].onMap, true);

    weather.setEnabled(false);
    await settle();
    assert.deepStrictEqual(calls.slice(-1), ['stop']);
    assert.strictEqual(layers[0].onMap, false);
    assert.strictEqual(appended.length, 1);
});

// Source of one method of an object literal in a console page, at the tab controller's indentation.
function methodSource(html, signature) {
    const begin = html.indexOf(`            ${signature} {`);
    assert.ok(begin >= 0, `${signature} not found`);
    const end = html.indexOf('\n            }', begin);
    return html.slice(begin, end + '\n            }'.length);
}

// Runs a console's applyMapProtocol() against firmware that does or does not know the uplink protocol.
function protocolHarness(name, { firmwareHasUplink, baud = 1000000 }) {
    const ctx = vm.createContext({
        sent: [], hints: [], notices: [],
        weatherSource: { onUplink: () => { } },
        WEATHER_MIN_BAUD: 230400,
        connectionManager: { _queryDeviceBaud: async () => baud },
        setWeatherHint: (text) => ctx.hints.push(text),
        atQueue: {
            send: async (command) => {
                ctx.sent.push(command.trim());
                if (/AIRCRAFT_JSON_UAT_UPLINK/.test(command) && !firmwareHasUplink) throw new Error('ERROR Invalid reporting protocol.');
            },
        },
    });
    vm.runInContext(`var tabController = {
        uplinkSupported: true,
        notice(text) { notices.push(text); },
        ${methodSource(consoleHtml(name), 'async applyMapProtocol()')}
    };`, ctx);
    return ctx;
}

for (const name of CONSOLES) {
    test(`${name} asks for uplinks only with weather on`, async () => {
        const ctx = protocolHarness(name, { firmwareHasUplink: true });
        await ctx.tabController.applyMapProtocol();
        assert.deepStrictEqual(ctx.sent, ['AT+PROTOCOL_OUT=CONSOLE,AIRCRAFT_JSON_UAT_UPLINK']);
        ctx.weatherSource.onUplink = null;
        await ctx.tabController.applyMapProtocol();
        assert.deepStrictEqual(ctx.sent.slice(1), ['AT+PROTOCOL_OUT=CONSOLE,AIRCRAFT_JSON']);
    });

    test(`${name} falls back to AIRCRAFT_JSON on older firmware`, async () => {
        const ctx = protocolHarness(name, { firmwareHasUplink: false });
        await ctx.tabController.applyMapProtocol();
        assert.deepStrictEqual(ctx.sent, ['AT+PROTOCOL_OUT=CONSOLE,AIRCRAFT_JSON_UAT_UPLINK', 'AT+PROTOCOL_OUT=CONSOLE,AIRCRAFT_JSON']);
        assert.strictEqual(ctx.tabController.uplinkSupported, false);
        assert.match(ctx.hints.at(-1), /firmware/i);
        await ctx.tabController.applyMapProtocol();
        assert.deepStrictEqual(ctx.sent.slice(2), ['AT+PROTOCOL_OUT=CONSOLE,AIRCRAFT_JSON']);
        assert.deepStrictEqual(ctx.notices, []);
    });

    test(`${name} never prints uplink lines`, () => {
        const ctx = vm.createContext({
            Fisb, printed: [], uplinks: [], ingested: [],
            atQueue: { tryConsume: () => false, current: null },
            weatherSource: { onUplink: (uplink) => ctx.uplinks.push(uplink) },
            aircraftStore: { ingest: (aircraft) => ctx.ingested.push(aircraft) },
            tabController: { mapStreamEngaged: false },
            flashController: { active: false },
            statsPanel: {}, serialStatus: {},
            appendToTerminal: (text) => ctx.printed.push(text),
        });
        vm.runInContext(`var lineRouter = { otaCapture: null, ${methodSource(consoleHtml(name), 'feed(line)')} };`, ctx);
        const line = uplinkLine({ rssi: -75, t: 42 });
        ctx.lineRouter.feed(line);
        ctx.lineRouter.feed(line.slice(0, 200));
        ctx.weatherSource.onUplink = null;
        ctx.lineRouter.feed(line);
        assert.strictEqual(ctx.uplinks.length, 1);
        assert.strictEqual(ctx.uplinks[0].meta.rssiDbm, -75);
        assert.deepStrictEqual(ctx.printed, []);

        ctx.lineRouter.feed('{"hex":"a1b2c3","lat":37.1,"lon":-122}');
        assert.strictEqual(ctx.ingested.length, 1);
        assert.strictEqual(ctx.printed.length, 1);
    });
}

test('adsbee_1421_console warns below 230400 baud', async () => {
    const slow = protocolHarness('adsbee_1421_console', { firmwareHasUplink: true, baud: 115200 });
    await slow.tabController.applyMapProtocol();
    assert.match(slow.hints.at(-1), /115200/);
    const fast = protocolHarness('adsbee_1421_console', { firmwareHasUplink: true, baud: 230400 });
    await fast.tabController.applyMapProtocol();
    assert.deepStrictEqual(fast.hints, ['']);
});

test('protocol lists include AIRCRAFT_JSON_UAT_UPLINK', () => {
    const pages = ['settings.js', 'adsbee.js'].map((file) => fs.readFileSync(path.join(__dirname, '..', file), 'utf8'));
    for (const text of [...pages, ...CONSOLES.map(consoleHtml)]) {
        const lists = text.match(/\[[^\]]*'AIRCRAFT_JSON'[^\]]*\]/g) || [];
        assert.ok(lists.length > 0);
        for (const list of lists) assert.match(list, /'AIRCRAFT_JSON_UAT_UPLINK'/);
    }
});
