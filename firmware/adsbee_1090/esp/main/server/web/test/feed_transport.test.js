// Tests for the transport and MQTT options in the feed editor. Runs in CI (web_ui_test job).
// Run: node --test firmware/adsbee_1090/esp/main/server/web/test/feed_transport.test.js
'use strict';
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');

const ADSBEE_SRC = fs.readFileSync(path.join(__dirname, '../adsbee.js'), 'utf8');

// FeedEditor from adsbee.js against a fake DOM, /api/feed and console.
function loadFeedEditor(feed) {
    const els = {};
    const sent = [];
    const get = (id) => (els[id] ||= { id, value: '', checked: false, style: {}, textContent: '', innerHTML: '' });
    const ctx = vm.createContext({
        HOST_URI: 'adsbee.local',
        document: { getElementById: get },
        fetch: async () => ({ ok: true, json: async () => feed }),
        setTimeout: () => {},
    });
    vm.runInContext(`${ADSBEE_SRC}\nthis.FeedEditor = FeedEditor;`, ctx);
    ctx.consoleWebSocket = { sendAndCapture: async (cmd) => { sent.push(cmd.trim()); } };
    vm.runInContext('consoleWebSocket = this.consoleWebSocket;', ctx);
    // Fake <select>s take their value from the selected option written into innerHTML.
    for (const id of ['feed-protocol', 'feed-transport']) {
        Object.defineProperty(get(id), 'value', {
            get() { return (/value="([^"]+)" selected/.exec(this.innerHTML) || [])[1] || ''; },
            set(v) { this.innerHTML = this.innerHTML.replace(' selected', '').replace(`value="${v}"`, `value="${v}" selected`); },
        });
    }
    return { FeedEditor: ctx.FeedEditor, get, sent };
}

const MQTT_FEED = {
    index: 3, uri: 'broker.lan', port: 1883, active: 1, protocol: 'AIRCRAFT_JSON', receiver_id: 'BEE0000123456789',
    transport: 'MQTT', mqtt: { topic_prefix: 'home', username: 'bee', has_password: true, tls: false, qos: 1 },
};

test('MQTT feed shows its options and topics, and saves both commands', async () => {
    const { FeedEditor, get, sent } = loadFeedEditor(MQTT_FEED);
    await FeedEditor.open(3);
    assert.strictEqual(get('feed-mqtt').style.display, '');
    assert.strictEqual(get('feed-mqtt-password').placeholder, '(unchanged)');
    assert.match(get('feed-mqtt-topics').textContent, /home\/bee0000123456789\/aircraft_json/);

    await FeedEditor.save();
    assert.deepStrictEqual(sent, [
        'AT+FEED=3,broker.lan,1883,1,AIRCRAFT_JSON,MQTT',
        'AT+FEED_MQTT=3,home,bee,,0,1',  // Empty password keeps the stored one.
        'AT+SETTINGS=SAVE',
    ]);
});

test('clearing the username clears the password', async () => {
    const { FeedEditor, get, sent } = loadFeedEditor(MQTT_FEED);
    await FeedEditor.open(3);
    get('feed-mqtt-username').value = '';
    get('feed-mqtt-prefix').value = '';
    await FeedEditor.save();
    assert.strictEqual(sent[1], 'AT+FEED_MQTT=3,-,-,-,0,1');
});

test('TCP and UDP feeds hide the MQTT options and send no AT+FEED_MQTT', async () => {
    for (const transport of [undefined, 'UDP']) {
        const { FeedEditor, get, sent } = loadFeedEditor(
            { index: 1, uri: '192.168.1.255', port: 4000, active: 1, protocol: 'GDL90', receiver_id: '', transport });
        await FeedEditor.open(1);
        assert.strictEqual(get('feed-mqtt').style.display, 'none');
        await FeedEditor.save();
        assert.deepStrictEqual(sent, [`AT+FEED=1,192.168.1.255,4000,1,GDL90,${transport || 'TCP'}`, 'AT+SETTINGS=SAVE']);
    }
});
