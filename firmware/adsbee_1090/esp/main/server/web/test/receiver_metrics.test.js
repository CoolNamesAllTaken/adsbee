// Tests for the receiver metric cards built from aircraft_dictionary_metrics. Runs in CI (web_ui_test job).
// Run: node --test firmware/adsbee_1090/esp/main/server/web/test/receiver_metrics.test.js
'use strict';
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const { receiverMetricCards } = require('../adsbee.js');

const REPO = path.join(__dirname, '../../../../../../..');
const ADSBEE_SRC = fs.readFileSync(path.join(__dirname, '../adsbee.js'), 'utf8');
const CONSOLE = fs.readFileSync(path.join(REPO, 'software/adsbee_1090_console/adsbee_1090_console.html'), 'utf8');

// Shape of AircraftDictionary::Metrics::ToJSON() (firmware/common/adsb/aircraft_dictionary.hh).
const METRICS = {
    raw_squitter_frames: 10, valid_squitter_frames: 7, demods_1090: 50,
    raw_squitter_frames_by_source: [2, 3, 5, 0],
    num_mode_s_aircraft: 4,
    corrected_frames: {
        extended_squitter_1_bit: 3, extended_squitter_2_bit: 1, address_parity_1_bit: 2, address_parity_2_bit: 0,
        rejected: 5, skipped: 7,
    },
};

const block = (src) => {
    const m = /\/\/ BEGIN RECEIVER_METRICS[\s\S]*?\/\/ END RECEIVER_METRICS/.exec(src);
    assert.ok(m, 'RECEIVER_METRICS block missing');
    return m[0];
};

test('numbers pass through; arrays are skipped', () => {
    const cards = receiverMetricCards(METRICS);
    assert.deepStrictEqual(cards.raw_squitter_frames, { value: 10, tip: null });
    assert.deepStrictEqual(cards.num_mode_s_aircraft, { value: 4, tip: null });
    assert.ok(!('raw_squitter_frames_by_source' in cards));
});

test('corrected_frames is one card: corrected total, every count in the tooltip', () => {
    const { value, tip } = receiverMetricCards(METRICS).corrected_frames;
    assert.strictEqual(value, 6);  // Rejected and skipped frames were not corrected.
    assert.strictEqual(tip, 'extended_squitter_1_bit: 3\nextended_squitter_2_bit: 1\naddress_parity_1_bit: 2\n' +
        'address_parity_2_bit: 0\nrejected: 5\nskipped: 7');
});

test('other non-numeric values are skipped', () => {
    const cards = receiverMetricCards({ a: 1, b: 'x', c: null, d: { e: 1 }, f: true, corrected_frames: null });
    assert.deepStrictEqual(Object.keys(cards), ['a']);
    assert.deepStrictEqual(receiverMetricCards(undefined), {});
});

test('no card reads [object Object]', () => {
    const values = [];
    const make = () => {
        const titleEl = { title: '' };
        return { title: '', querySelector: () => titleEl, titleEl };
    };
    const ctx = vm.createContext({
        document: {
            getElementById: () => ({ appendChild() {}, removeChild() {} }), createElement: make,
        },
        WebSocket: function () {}, setInterval() {}, setTimeout() {},
        SparklineChart: function () { this.push = (v, unit) => values.push(`${v} ${unit}`); this.destroy = () => {}; },
    });
    vm.runInContext(`${ADSBEE_SRC}\nSparklineChart = this.SparklineChart; this.MetricsWebSocket = MetricsWebSocket;
        this.receiverMetricCards = receiverMetricCards;`, ctx);
    const ws = Object.create(ctx.MetricsWebSocket.prototype);
    ws.cards = { feed: {}, receiver: {} };
    ws.updateReceiverCards(ctx.receiverMetricCards(METRICS));
    const card = ws.cards.receiver.corrected_frames;
    assert.ok(values.every((v) => !v.includes('[object')), values.join(', '));
    assert.ok(values.includes('6 msg/s'));
    assert.match(card.card.title, /^extended_squitter_1_bit: 3\n/);
    assert.strictEqual(card.card.titleEl.title, card.card.title);
    assert.strictEqual(ws.cards.receiver.demods_1090.card.titleEl.title, 'demods_1090');
});

test('the 1090 console carries the same block and uses it', () => {
    assert.strictEqual(block(CONSOLE), block(ADSBEE_SRC),
        'Re-copy the RECEIVER_METRICS block from adsbee.js into software/adsbee_1090_console/adsbee_1090_console.html');
    assert.match(CONSOLE, /this\.updateReceiverCards\(receiverMetricCards\(data\['aircraft_dictionary_metrics'\]\)\)/);
    assert.match(CONSOLE, /setTip\(tip\) \{/);
});
