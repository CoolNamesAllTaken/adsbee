// Tests for the feed performance tooltip by the Feeds heading. Runs in CI (web_ui_test job).
// Run: node --test firmware/adsbee_1090/esp/main/server/web/test/feed_tip.test.js
'use strict';
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const path = require('node:path');

const REPO = path.join(__dirname, '../../../../../../..');
const INDEX = fs.readFileSync(path.join(__dirname, '../index.html'), 'utf8');
const STYLE = fs.readFileSync(path.join(__dirname, '../style.css'), 'utf8');
const CONSOLE = fs.readFileSync(path.join(REPO, 'software/adsbee_1090_console/adsbee_1090_console.html'), 'utf8');

const tipLine = (html) => html.split('\n').find(l => l.includes('id="feed-tip"'));
const tipCss = (css) => css.slice(css.indexOf('.info-tip {'), css.indexOf('.feed-slot-badge {'));

test('feeds heading has an info symbol with a one-sentence tooltip', () => {
    const header = INDEX.slice(INDEX.indexOf('class="feed-metrics-header"'), INDEX.indexOf('id="add-feed-btn"'));
    assert.match(header, /id="feed-count"[\s\S]*id="feed-tip" class="info-tip" tabindex="0"/);
    const tip = /data-tip="([^"]+)"/.exec(tipLine(INDEX))[1];
    assert.match(tip, /^Fewer feeds carry higher message rates/);
    assert.strictEqual(tip.match(/\.(\s|$)/g).length, 1);
    assert.ok(tip.length <= 140, tip);
});

test('tooltip text is shown on hover and on focus', () => {
    assert.match(tipCss(STYLE), /\.info-tip:hover::after,\s*\.info-tip:focus::after \{\s*content: attr\(data-tip\);/);
});

test('adsbee_1090_console carries the same symbol and style', () => {
    assert.strictEqual(tipLine(CONSOLE), tipLine(INDEX), 'Re-copy the feed-tip line from index.html');
    assert.strictEqual(tipCss(CONSOLE), tipCss(STYLE), 'Re-copy the .info-tip rules from style.css');
});
