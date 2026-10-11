// Checks that the standalone consoles carry exact copies of fisb.js, fisb_stations.js and the weather classes in
// adsbee.js. Runs in CI (web_ui_test job).
// Run: node --test firmware/adsbee_1090/esp/main/server/web/test/fisb_drift.test.js
'use strict';
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const path = require('node:path');

const REPO = path.join(__dirname, '../../../../../../..');
const source = (name) => fs.readFileSync(path.join(__dirname, '..', name), 'utf8');
const consoleHtml = (name) => fs.readFileSync(path.join(REPO, `software/${name}/${name}.html`), 'utf8');

// A class declaration at the given indentation, up to its closing brace.
function classSource(text, name, indent = '') {
    const begin = text.indexOf(`${indent}class ${name} {`);
    assert.ok(begin >= 0, `class ${name} not found`);
    const end = `\n${indent}}\n`;
    const body = text.slice(begin, text.indexOf(end, begin) + end.length);
    return body.split('\n').map((line) => line.slice(line.startsWith(indent) ? indent.length : 0)).join('\n');
}

for (const name of ['adsbee_1090_console', 'adsbee_1421_console']) {
    for (const file of ['fisb.js', 'fisb_stations.js']) {
        test(`${name} carries an exact copy of ${file}`, () => {
            const lines = consoleHtml(name).split('\n');
            const b = lines.findIndex((l) => l.includes(`══ BEGIN VENDORED ${file} `));
            const e = lines.findIndex((l, i) => i > b && l.includes(`══ END VENDORED ${file} `));
            assert.ok(b >= 0 && e > b, `VENDORED ${file} markers not found`);
            // The block is the file wrapped in <script> and </script> lines.
            const copy = lines.slice(b + 2, e - 1).join('\n') + '\n';
            assert.strictEqual(copy, source(file), `Re-copy ${file} into software/${name}/${name}.html`);
        });
    }
}

for (const [name, className, indent] of [['adsbee_1090_console', 'UplinkWebSocket', ''], ['adsbee_1090_console', 'MapWeather', ''],
                                         ['adsbee_1421_console', 'MapWeather', '        ']]) {
    test(`${name} carries an exact copy of ${className}`, () => {
        assert.strictEqual(classSource(consoleHtml(name), className, indent), classSource(source('adsbee.js'), className),
            `Re-copy class ${className} from adsbee.js into software/${name}/${name}.html`);
    });
}
