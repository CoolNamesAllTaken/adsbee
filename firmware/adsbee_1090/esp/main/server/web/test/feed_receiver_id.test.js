// Tests for the feed receiver ID: UUID form, AT+FEED_RECEIVER_ID? parsing, the editor field, feed card chips, and
// the copy in the 1090 console. Runs in CI (web_ui_test job).
// Run: node --test firmware/adsbee_1090/esp/main/server/web/test/feed_receiver_id.test.js
'use strict';
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const { receiverIdUuid, parseFeedReceiverIdLine, whereplaneMapUrl } = require('../adsbee.js');

const REPO = path.join(__dirname, '../../../../../../..');
const ADSBEE_SRC = fs.readFileSync(path.join(__dirname, '../adsbee.js'), 'utf8');
const CONSOLE = fs.readFileSync(path.join(REPO, 'software/adsbee_1090_console/adsbee_1090_console.html'), 'utf8');
const ID = '0bee00038172d18c';
const UUID = '0bee0003-8172-d18c-0bee-00038172d18c';
const CUSTOM = 'bee0aaaabbbbcccc';

const block = (src) => {
    const m = /\/\/ BEGIN FEED_RECEIVER_ID[\s\S]*?\/\/ END FEED_RECEIVER_ID/.exec(src);
    assert.ok(m, 'FEED_RECEIVER_ID block missing');
    return m[0];
};

test('the 1090 console carries the same receiver ID block', () => {
    assert.strictEqual(block(CONSOLE), block(ADSBEE_SRC),
        'Re-copy the FEED_RECEIVER_ID block from adsbee.js into software/adsbee_1090_console/adsbee_1090_console.html');
});

test('UUID form matches the one the Beast feed sends and the whereplane link', () => {
    assert.strictEqual(receiverIdUuid(ID), UUID);
    assert.strictEqual(receiverIdUuid(ID.toUpperCase()), UUID);
    assert.ok(whereplaneMapUrl('feed.whereplane.xyz', 'BEAST', ID).endsWith(UUID));
    for (const bad of ['', undefined, '0bee0003', `${ID}0`, '0bee00038172d18g']) assert.strictEqual(receiverIdUuid(bad), null);
});

test('parses AT+FEED_RECEIVER_ID? lines', () => {
    assert.deepStrictEqual(parseFeedReceiverIdLine(`+FEED_RECEIVER_ID=3(INDEX),${CUSTOM.toUpperCase()}(RECEIVER_ID),${ID}(DEFAULT)\r\n`),
        { index: 3, id: CUSTOM, defaultId: ID });
    // No EEPROM: no default.
    assert.deepStrictEqual(parseFeedReceiverIdLine(`FEED_RECEIVER_ID=0(INDEX),${ID}(RECEIVER_ID),(DEFAULT)`),
        { index: 0, id: ID, defaultId: '' });
    assert.strictEqual(parseFeedReceiverIdLine('ERROR Unknown command'), null);
});

// A small DOM: elements with children, classes, text and handlers.
function fakeDom() {
    const copied = [];
    const make = (tag) => {
        const el = {
            tag, children: [], style: {}, className: '', textContent: '', title: '', value: '', disabled: false,
            appendChild(c) { this.children.push(c); return c; },
            removeChild(c) { this.children = this.children.filter(x => x !== c); },
            replaceChildren(...cs) { this.children = cs; },
            insertBefore(c, ref) { const i = ref ? this.children.indexOf(ref) : -1; if (i < 0) this.children.push(c); else this.children.splice(i, 0, c); },
            replaceChild(n, o) { this.children[this.children.indexOf(o)] = n; },
            select() {}, focus() {},
        };
        el.classList = {
            add: (c) => { el.className = `${el.className} ${c}`.trim(); },
            remove: (c) => { el.className = el.className.split(' ').filter(x => x !== c).join(' '); },
        };
        return el;
    };
    const els = {};
    const document = {
        getElementById: (id) => (els[id] ||= Object.assign(make('div'), { id })),
        createElement: make,
        body: make('body'),
        execCommand: (cmd) => { if (cmd === 'copy') copied.push(document.body.children.at(-1).value); return true; },
    };
    return { document, copied, els };
}

const all = (el) => [el, ...el.children.flatMap(all)];
const find = (el, pred) => all(el).find(pred);
const button = (el, text) => find(el, (e) => e.tag === 'button' && e.textContent === text);
const tick = () => new Promise((r) => setImmediate(r));

function load(extra = {}) {
    const dom = fakeDom();
    const timers = [];
    const ctx = vm.createContext({
        HOST_URI: 'adsbee.local', document: dom.document, navigator: {}, window: { isSecureContext: false },
        setTimeout: (f) => timers.push(f), clearTimeout: () => {}, WebSocket: function () {}, ...extra,
    });
    vm.runInContext(`${ADSBEE_SRC}\nthis.ReceiverIdField = ReceiverIdField; this.FeedEditor = FeedEditor;
        this.MetricCard = MetricCard; this.receiverIdChip = receiverIdChip;`, ctx);
    return { ctx, dom };
}

test('field shows hex and UUID, copies both, and marks a custom ID', async () => {
    const { ctx, dom } = load();
    const el = dom.document.getElementById('feed-receiver-id');
    const field = new ctx.ReceiverIdField(el, { id: CUSTOM.toUpperCase(), onSet: async () => ({}) });
    assert.strictEqual(find(el, (e) => e.className === 'rid-hex').textContent, CUSTOM);
    assert.strictEqual(find(el, (e) => e.className === 'rid-uuid').textContent, receiverIdUuid(CUSTOM));
    assert.strictEqual(button(el, '↺'), undefined);  // Default unknown yet.
    field.setDefault(ID);
    assert.strictEqual(button(el, '↺').disabled, false);
    assert.ok(find(el, (e) => e.className === 'rid-custom').title.includes(ID));
    const copies = all(el).filter((e) => e.textContent === '⧉');
    await copies[0].onclick({ stopPropagation() {} });
    await copies[1].onclick({ stopPropagation() {} });
    assert.deepStrictEqual(dom.copied, [CUSTOM, receiverIdUuid(CUSTOM)]);
    field.id = ID;
    field.render();
    assert.strictEqual(button(el, '↺').disabled, true);
    assert.strictEqual(find(el, (e) => e.className === 'rid-custom'), undefined);
});

test('inline edit validates 16 hex digits and sets the lower-case ID', async () => {
    const { ctx, dom } = load();
    const el = dom.document.getElementById('feed-receiver-id');
    const calls = [];
    const field = new ctx.ReceiverIdField(el, {
        id: ID, defaultId: ID, onSet: async (v) => { calls.push(v); return { id: v, defaultId: ID }; },
    });
    button(el, '✎').onclick();
    const input = find(el, (e) => e.tag === 'input');
    for (const bad of ['0bee', 'xyz0000000000000', `${ID}00`]) {
        input.value = bad;
        input.oninput();
        assert.strictEqual(button(el, '✓').disabled, true, bad);
        assert.strictEqual(input.className, 'rid-input bad');
    }
    input.value = ` ${CUSTOM.toUpperCase()} `;
    input.oninput();
    assert.strictEqual(button(el, '✓').disabled, false);
    assert.strictEqual(find(el, (e) => e.className === 'rid-uuid').textContent, receiverIdUuid(CUSTOM));
    await button(el, '✓').onclick();
    assert.deepStrictEqual(calls, [CUSTOM]);
    assert.strictEqual(field.editing, false);
    assert.strictEqual(find(el, (e) => e.className === 'rid-hex').textContent, CUSTOM);
    // Reset.
    await button(el, '↺').onclick();
    assert.deepStrictEqual(calls, [CUSTOM, 'DEFAULT']);
});

test('a refused ID keeps the editor open with the reason', async () => {
    const { ctx, dom } = load();
    const el = dom.document.getElementById('feed-receiver-id');
    const field = new ctx.ReceiverIdField(el, { id: ID, defaultId: ID, onSet: async () => { throw new Error('nope'); } });
    button(el, '✎').onclick();
    const input = find(el, (e) => e.tag === 'input');
    input.value = CUSTOM;
    input.oninput();
    await button(el, '✓').onclick();
    assert.strictEqual(field.editing, true);
    assert.strictEqual(find(el, (e) => e.className === 'rid-msg').textContent, '✗ nope');
});

test('feed editor sends AT+FEED_RECEIVER_ID, saves, and reads the result back', async () => {
    const sent = [];
    let current = CUSTOM;
    const consoleWebSocket = {
        sendAndCapture: async (cmd) => {
            cmd = cmd.trim();
            sent.push(cmd);
            const set = /^AT\+FEED_RECEIVER_ID=2,(\w+)$/.exec(cmd);
            if (set) current = set[1] === 'DEFAULT' ? ID : set[1];
            if (cmd.startsWith('AT+FEED_RECEIVER_ID?')) {
                return [`+FEED_RECEIVER_ID=2(INDEX),${current}`, `(RECEIVER_ID),${ID}(DEFAULT)\r\n`];
            }
            return ['OK'];
        },
    };
    const feed = { index: 2, uri: 'feed.whereplane.xyz', port: 30004, active: 1, protocol: 'BEAST', receiver_id: CUSTOM, transport: 'TCP' };
    const { ctx, dom } = load({ fetch: async () => ({ ok: true, json: async () => feed }) });
    ctx.consoleWebSocket = consoleWebSocket;
    vm.runInContext('consoleWebSocket = this.consoleWebSocket;', ctx);
    for (const id of ['feed-protocol', 'feed-transport']) {
        Object.defineProperty(dom.document.getElementById(id), 'value', { get() { return id === 'feed-protocol' ? 'BEAST' : 'TCP'; }, set() {} });
    }
    await ctx.FeedEditor.open(2);
    await tick();
    const el = dom.els['feed-receiver-id'];
    assert.strictEqual(button(el, '↺').disabled, false);   // Default arrived from the query.
    assert.ok(dom.els['feed-map-link'].href.endsWith(receiverIdUuid(CUSTOM)));
    await button(el, '↺').onclick();
    assert.deepStrictEqual(sent, ['AT+FEED_RECEIVER_ID?2', 'AT+FEED_RECEIVER_ID=2,DEFAULT', 'AT+SETTINGS=SAVE',
        'AT+FEED_RECEIVER_ID?2']);
    assert.strictEqual(find(el, (e) => e.className === 'rid-hex').textContent, ID);
    assert.ok(dom.els['feed-map-link'].href.endsWith(UUID));  // The map link follows the new ID.
});

test('feed cards show the ID; a click copies it without opening the editor', async () => {
    const { ctx, dom } = load({ SparklineChart: function () { this.push = () => {}; this.destroy = () => {}; } });
    vm.runInContext('SparklineChart = this.SparklineChart;', ctx);
    const opened = [];
    ctx.FeedEditor.open = (slot) => opened.push(slot);
    const container = dom.document.getElementById('feed-metrics-container');
    const card = new ctx.MetricCard(container, 'feed.adsb.fi', 'msg/s', 4);
    card.setReceiverId(ID);
    const chip = find(card.card, (e) => e.className === 'rid-chip');
    assert.strictEqual(chip.textContent, ID);
    assert.ok(chip.title.includes(UUID));
    let stopped = false;
    await chip.onclick({ stopPropagation() { stopped = true; } });
    assert.ok(stopped);
    assert.deepStrictEqual(dom.copied, [ID]);
    assert.deepStrictEqual(opened, []);
    card.setReceiverId(CUSTOM);
    assert.strictEqual(all(card.card).filter((e) => e.className === 'rid-chip').length, 1);
});

test('console feed editor queries and sets the ID over AT', () => {
    assert.ok(CONSOLE.includes('id="feed-receiver-id"'));
    assert.match(CONSOLE, /sendCommand\(`AT\+FEED_RECEIVER_ID\?\$\{slot\}`/);
    assert.match(CONSOLE, /sendCommand\(`AT\+FEED_RECEIVER_ID=\$\{slot\},\$\{value\}`/);
    assert.match(CONSOLE, /receiverIdChip\(args\[5\]\)/);  // Serial feed cards.
});
