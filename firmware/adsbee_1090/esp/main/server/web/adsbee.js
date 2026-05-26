const METRIC_UNITS = {
    'num_mode_s_aircraft': 'aircraft',
    'num_uat_aircraft':    'aircraft',
};

class ConsoleWebSocket {
    constructor(url) {
        this.url = url;
        this.paused = false;
        this.captureCallback = null;
        this._reconnectTimer = null;
        this.init();
    }

    init() {
        this.ws = new WebSocket(this.url)
        this.attachEventHandlers();
    }

    attachEventHandlers() {
        // Connection opened
        this.ws.addEventListener('open', () => {
            console.log(`Connected to ${this.url}`);
        });

        // Listen for messages
        this.ws.addEventListener('message', (event) => {
            const dispatch = (text) => {
                appendToTerminal(text);
                if (this.captureCallback) this.captureCallback(text);
            };
            if (typeof event.data === 'string') {
                dispatch(event.data);
            } else if (event.data instanceof Blob) {
                const reader = new FileReader();
                reader.onload = () => dispatch(reader.result);
                reader.readAsText(event.data);
            } else if (event.data instanceof ArrayBuffer) {
                dispatch(new TextDecoder().decode(event.data));
            }
        });

        // Connection closed (both clean and unclean closes)
        this.ws.addEventListener('close', (event) => {
            console.log(`Connection closed. Code: ${event.code}, Reason: ${event.reason}`);
            appendToTerminal(`Connection closed. Code: ${event.code}\n`);
            this.attemptReconnect();
        });

        // Connection error
        this.ws.addEventListener('error', (error) => {
            console.error('WebSocket error:', error);
            // Don't call attemptReconnect here as the close event will be fired after error
        });
    }

    send(message) {
        if (this.ws && this.ws.readyState === WebSocket.OPEN) {
            this.ws.send(message);
            console.log(`Sent message: ${message}`);
            return true;
        } else {
            console.warn('Cannot send message - connection is not open');
            return false;
        }
    }

    // Send a command and collect incoming messages until one contains `terminator`.
    // 'OK' and 'ERROR' are matched as whole trimmed lines; anything else as a substring.
    sendAndCapture(command, terminator, timeoutMs = 5000) {
        return new Promise((resolve, reject) => {
            const captured = [];
            const isLineTerminator = (terminator === 'OK' || terminator === 'ERROR');
            const matches = (text) => isLineTerminator
                ? text.split(/[\r\n]+/).some(l => l.trim() === terminator)
                : text.includes(terminator);

            const timer = setTimeout(() => {
                this.captureCallback = null;
                reject(new Error(`Response timeout after ${timeoutMs} ms.`));
            }, timeoutMs);

            this.captureCallback = (text) => {
                captured.push(text);
                if (text.split(/[\r\n]+/).some(l => l.trim() === 'ERROR')) {
                    clearTimeout(timer);
                    this.captureCallback = null;
                    reject(new Error(`ERROR response: ${text.trim()}`));
                } else if (matches(text)) {
                    clearTimeout(timer);
                    this.captureCallback = null;
                    resolve(captured);
                }
            };

            this.send(command);
        });
    }

    attemptReconnect() {
        if (this._reconnectTimer) return;
        this._reconnectTimer = setTimeout(() => {
            this._reconnectTimer = null;
            if (!this.paused && (!this.ws || this.ws.readyState === WebSocket.CLOSED)) {
                this.init();
            }
        }, WS_CONFIG.reconnectDelayMs);
    }

    pause() { this.paused = true; if (this.ws) this.ws.close(); }
    resume() { if (this.paused) { this.paused = false; this.init(); } }

    close(code, reason) {
        if (this.ws) {
            this.ws.close(code, reason);
        }
    }

    getState() {
        const states = {
            0: 'CONNECTING',
            1: 'OPEN',
            2: 'CLOSING',
            3: 'CLOSED'
        };
        return states[this.ws ? this.ws.readyState : 3];
    }

    // Method to manually trigger reconnection
    reconnect() {
        if (this.ws) {
            this.ws.close();
        } else {
            this.attemptReconnect();
        }
    }

}

class SparklineChart {
    constructor(id, windowSeconds = 20) {
        this.svg = document.getElementById(id);
        this.windowSeconds = windowSeconds;
        this.buffer = [];
        this.valueEl = this.svg.parentNode.querySelector('.metric-value');
        this._createPaths();
        this._startRAF();
    }

    _createPaths() {
        const area = document.createElementNS('http://www.w3.org/2000/svg', 'path');
        const line = document.createElementNS('http://www.w3.org/2000/svg', 'path');
        area.classList.add('area');
        this.svg.appendChild(area);
        this.svg.appendChild(line);
        this.linePath = line;
        this.areaPath = area;
    }

    _startRAF() {
        const tick = () => {
            this._render();
            this._rafId = requestAnimationFrame(tick);
        };
        this._rafId = requestAnimationFrame(tick);
    }

    push(value, unit = 'msg/s') {
        this.buffer.push({ value, ts: performance.now() });
        this.valueEl.textContent = `${value} ${unit}`;
        const cutoff = performance.now() - (this.windowSeconds + 5) * 1000;
        while (this.buffer.length > 1 && this.buffer[0].ts < cutoff) this.buffer.shift();
    }

    _render() {
        const now = performance.now();
        const windowMs = this.windowSeconds * 1000;
        const startMs = now - windowMs;

        // Collect visible points; prepend one point before the window so the
        // line reaches the left edge instead of starting mid-chart.
        const pts = [];
        for (let i = 0; i < this.buffer.length; i++) {
            if (this.buffer[i].ts >= startMs) {
                if (i > 0 && pts.length === 0) pts.push(this.buffer[i - 1]);
                pts.push(this.buffer[i]);
            }
        }
        if (pts.length < 2) return;

        const max = Math.max(...pts.map(p => p.value), 1);
        const toXY = p => [
            ((p.ts - startMs) / windowMs) * 100,
            30 - (p.value / max) * 28,
        ];
        const coords = pts.map(toXY);
        const lineCmds = coords.map((p, i) => `${i === 0 ? 'M' : 'L'}${p[0].toFixed(2)},${p[1].toFixed(2)}`).join(' ');
        const areaCmds = `${lineCmds} L${coords[coords.length - 1][0].toFixed(2)},30 L${coords[0][0].toFixed(2)},30 Z`;

        this.linePath.setAttribute('d', lineCmds);
        this.areaPath.setAttribute('d', areaCmds);
    }

    destroy() {
        if (this._rafId) { cancelAnimationFrame(this._rafId); this._rafId = null; }
    }
}

class MetricCard {
    constructor(container, label, unit = 'msg/s', feedSlot = null) {
        this.container = container;
        this.label = label;
        this.unit = unit;
        this.feedSlot = feedSlot;
        this.id = `chart-${this.labelToID(label)}`;

        const card = document.createElement('div');
        card.className = 'metrics-card';
        if (feedSlot !== null) {
            card.classList.add('editable');
            card.onclick = () => FeedEditor.open(feedSlot);
        }
        const slotBadge = feedSlot !== null
            ? `<span class="feed-slot-badge">#${feedSlot}</span>`
            : '';
        card.innerHTML = `
  <div class="metric-title" title="${label}">${label}${slotBadge}</div>
  <div class="metric-value">0 ${unit}</div>
  <svg class="sparkline" id="${this.id}" viewBox="0 0 100 30"></svg>
`;
        this.card = card;
        this.container.appendChild(card);
        this.chart = new SparklineChart(this.id);
    }

    destroy() {
        this.chart.destroy();
        this.container.removeChild(this.card);
    }

    labelToID(label) {
        return label.replace(/[^a-zA-Z0-9]/g, '-');
    }

    update(value) {
        this.chart.push(value, this.unit);
    }
}

class MetricsWebSocket {
    constructor(url) {
        this.url = url;
        this.paused = false;
        this.cards = {
            'feed': {},
            'receiver': {}
        };
        this.feedSlotMap = {};
        this.connect();
        this.feedsCountEl = document.getElementById('feed-count');
        this.container = document.getElementById('metrics-container');
    }

    updateReceiverCards(data) {
        const parentLabel = 'receiver';
        const container = document.getElementById('receiver-metrics-container');
        Object.keys(this.cards[parentLabel]).forEach(label => {
            if (!data.hasOwnProperty(label)) this.cards[parentLabel][label].destroy();
        });
        Object.entries(data).forEach(([label, value]) => {
            if (!this.cards[parentLabel][label]) {
                const unit = METRIC_UNITS[label] || 'msg/s';
                this.cards[parentLabel][label] = new MetricCard(container, label, unit);
            }
            this.cards[parentLabel][label].update(value);
        });
    }

    updateFeedCards(data) {
        const parentLabel = 'feed';
        const container = document.getElementById('feed-metrics-container');
        Object.keys(this.cards[parentLabel]).forEach(label => {
            if (!data.hasOwnProperty(label)) this.cards[parentLabel][label].destroy();
        });
        Object.entries(data).forEach(([label, value]) => {
            if (!this.cards[parentLabel][label]) {
                const slot = this.feedSlotMap[label] ?? null;
                this.cards[parentLabel][label] = new MetricCard(container, label, 'msg/s', slot);
            }
            this.cards[parentLabel][label].update(value);
        });
    }

    updateDeviceStatus(deviceStatus) {
        const container = document.getElementById('device-status-cards-container');

        // Clear existing content
        container.innerHTML = '';

        // Create cards for each device
        Object.entries(deviceStatus).forEach(([deviceName, status]) => {
            const card = document.createElement('div');
            card.className = 'device-status-card';

            let statusHtml = `<div class="device-card">
                                <div class="device-status-title">${deviceName.toUpperCase()}</div>`;

            // Add status information
            Object.entries(status).forEach(([key, value]) => {
                let displayKey = key.replace(/_/g, ' ').replace(/\b\w/g, l => l.toUpperCase());
                let displayValue = value;

                // Format specific values
                if (key.includes('uptime_ms')) {
                    displayKey = 'Uptime';
                    displayValue = `${Math.floor(value / 1000)}s`;
                } else if (key.includes('temperature')) {
                    displayKey = 'Temperature';
                    displayValue = `${value}\u00B0C`;
                } else if (key.includes('usage_percent')) {
                    displayKey = displayKey.replace(' Percent', '');
                    displayValue = `${value}%`;
                } else if (key.includes('heap_free_bytes')) {
                    displayKey = 'Free Heap';
                    displayValue = `${value} B`;
                } else if (key.includes('heap_largest_free_block_bytes')) {
                    displayKey = 'Largest Free Block';
                    displayValue = `${value} B`;
                }

                statusHtml += `<div class="status-item">
                                    <span class="status-key">${displayKey}:</span>
                                    <span class="status-value">${displayValue}</span>
                                </div>`;
            });
            statusHtml += `</div>`;

            card.innerHTML = statusHtml;
            container.appendChild(card);
        });
    }

    connect() {
        this.ws = new WebSocket(this.url);

        this.pingInterval = setInterval(() => {
            if (this.ws && this.ws.readyState === WebSocket.OPEN) {
                this.ws.send('ping');
            }
        }, 60000);

        this.ws.onopen = () => {
            console.log('Connected to WebSocket');
        };

        this.ws.onclose = () => {
            clearInterval(this.pingInterval);
            console.log('Disconnected from WebSocket');
            setTimeout(() => { if (!this.paused) this.connect(); }, 3000);
        };

        this.ws.onerror = (error) => {
            console.error('WebSocket error:', error);
        };

        this.ws.onmessage = (event) => {
            try {
                const data = JSON.parse(event.data);

                if (data.hasOwnProperty('aircraft_dictionary_metrics')) {
                    const dictionaryMetrics = Object.fromEntries(
                        Object.entries(data['aircraft_dictionary_metrics']).filter(([key, value]) => !Array.isArray(value))
                    );
                    this.updateReceiverCards(dictionaryMetrics);
                }
                if (data.hasOwnProperty('server_metrics')) {
                    const serverMetrics = data['server_metrics'];
                    this._feedUris = serverMetrics['feed_uri'];
                    const feedMetrics = {};
                    for (let i = 0; i < serverMetrics['feed_uri'].length; i++) {
                        if (serverMetrics['feed_uri'][i] === '') continue;
                        feedMetrics[serverMetrics['feed_uri'][i]] = serverMetrics['feed_mps'][i];
                        this.feedSlotMap[serverMetrics['feed_uri'][i]] = i;
                    }
                    this.updateFeedCards(feedMetrics);
                    this.feedsCountEl.textContent = `Feeds: ${Object.keys(feedMetrics).length}`;
                    const addBtn = document.getElementById('add-feed-btn');
                    if (addBtn) addBtn.disabled = (this.getFirstEmptySlot() === -1);
                }
                if (data.hasOwnProperty('device_status')) {
                    const deviceStatus = data['device_status'];
                    // console.log('Device Status:', deviceStatus);
                    this.updateDeviceStatus(deviceStatus);
                }
            } catch (error) {
                console.error('Error parsing WebSocket message:', error);
            }
        };
    }

    getFirstEmptySlot() {
        if (!this._feedUris) return 0;
        for (let i = 0; i < this._feedUris.length; i++) {
            if (this._feedUris[i] === '') return i;
        }
        return -1;
    }

    pause() { this.paused = true; if (this.ws) this.ws.close(); }
    resume() { if (this.paused) { this.paused = false; this.connect(); } }

    close(code, reason) {
        if (this.ws) {
            this.ws.close(code, reason);
        }
    }
}

class FeedEditor {
    static PROTOCOLS = ['NONE', 'RAW', 'BEAST', 'BEAST_NO_UAT', 'BEAST_NO_UAT_UPLINK',
                        'CSBEE', 'MAVLINK1', 'MAVLINK2', 'GDL90', 'AIRCRAFT_JSON'];

    static parseFeedResponse(text) {
        const m = text.match(/\+FEED=(\d+)\(INDEX\),([^,]*)\(URI\),(\d+)\(PORT\),(\d+)\(ACTIVE\),(\w+)\(PROTOCOL\)/);
        if (!m) return null;
        return { index: +m[1], uri: m[2], port: +m[3], active: m[4] === '1', protocol: m[5] };
    }

    static async open(feedSlot) {
        const modal = document.getElementById('feed-modal');
        const statusEl = document.getElementById('feed-modal-status');
        statusEl.textContent = 'Loading...';
        document.getElementById('feed-form').style.display = 'none';
        modal.style.display = 'flex';

        let current = null;
        try {
            const resp = await fetch(`http://${HOST_URI}/api/feed?index=${feedSlot}`);
            if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
            current = await resp.json();
        } catch (e) {
            statusEl.textContent = `Error: ${e.message}`;
            return;
        }

        document.getElementById('feed-slot').value = current.index;
        document.getElementById('feed-uri').value = current.uri;
        document.getElementById('feed-port').value = current.port;
        document.getElementById('feed-active').checked = !!current.active;
        const sel = document.getElementById('feed-protocol');
        sel.innerHTML = FeedEditor.PROTOCOLS
            .map(p => `<option value="${p}"${p === current.protocol ? ' selected' : ''}>${p}</option>`)
            .join('');
        statusEl.textContent = '';
        document.getElementById('feed-form').style.display = '';
    }

    static close() {
        document.getElementById('feed-modal').style.display = 'none';
    }

    static openFirstEmpty() {
        const slot = metricsWebSocket ? metricsWebSocket.getFirstEmptySlot() : 0;
        if (slot === -1) return;
        FeedEditor.open(slot);
    }

    static async remove() {
        const slot     = document.getElementById('feed-slot').value;
        const statusEl = document.getElementById('feed-modal-status');
        statusEl.textContent = 'Removing...';
        try {
            await consoleWebSocket.sendAndCapture(`AT+FEED=${slot},-,0,0,NONE\r\n`, 'OK', 5000);
            await consoleWebSocket.sendAndCapture(`AT+SETTINGS=SAVE\r\n`, 'OK', 5000);
            statusEl.textContent = 'Removed.';
            setTimeout(() => FeedEditor.close(), 800);
        } catch (e) {
            statusEl.textContent = `Error: ${e.message}`;
        }
    }

    static async save() {
        const slot     = document.getElementById('feed-slot').value;
        const uri      = document.getElementById('feed-uri').value.trim();
        const port     = document.getElementById('feed-port').value;
        const active   = document.getElementById('feed-active').checked ? 1 : 0;
        const protocol = document.getElementById('feed-protocol').value;
        const statusEl = document.getElementById('feed-modal-status');

        statusEl.textContent = 'Saving...';
        try {
            await consoleWebSocket.sendAndCapture(`AT+FEED=${slot},${uri},${port},${active},${protocol}\r\n`, 'OK', 5000);
            await consoleWebSocket.sendAndCapture(`AT+SETTINGS=SAVE\r\n`, 'OK', 5000);
            statusEl.textContent = 'Saved.';
            setTimeout(() => FeedEditor.close(), 800);
        } catch (e) {
            statusEl.textContent = `Error: ${e.message}`;
        }
    }
}

class ADSBeeAT {
    static MS_PER_SEC = 1000;
    static ERROR_BUFFER_FLUSH_INTERVAL_MS = 1000; // How long to wait after a parse error to let the error message print.

    messageQueue = [];

    constructor(url = HOST_URI) {
        if (!url) {
            throw new Error('URL is required');
        }
        this.url = url;
        this.ws = null;
        this.lastCmdTimestamp = Date.now();

        this.decoder = new TextDecoder('utf-8');
    }

    async connect() {
        return new Promise((resolve, reject) => {
            this.connectTimestamp = Date.now();
            this.ws = new WebSocket(`ws://${this.url}/console`);
            this.ws.binaryType = 'arraybuffer';

            this.ws.onmessage = (event) => {
                const decoded_message = this.decoder.decode(event.data);
                console.log("ADSBeeAT received message:", decoded_message);
                this.messageQueue.push(decoded_message);
            };

            this.ws.onopen = () => {
                resolve();
            };

            this.ws.onerror = (error) => reject(error);

            this.ws.onclose = (event) => {
                reject(new Error(`WebSocket closed (code ${event.code})`));
            };
        });
    }

    async disconnect() {
        if (this.ws) {
            this.ws.close();
            this.ws = null;
        }
    }

    getMsTimestamp() {
        return Math.floor((Date.now() - this.connectTimestamp));
    }

    async getUptimeSec() {
        const response = await this.sendCmd('AT+UPTIME?\r\n', 0, true, true, '+UPTIME');
        for (const line of response) {
            const match = line.match(/\+UPTIME=(\d+)/);
            if (match) {
                return parseInt(match[1]);
            }
        }
        return null;
    }

    async flushInputBuffer(flushTimeoutMs = 10) {
        await new Promise(resolve => setTimeout(resolve, flushTimeoutMs));
        this.messageQueue = [];
    }

    async receiveResponse(printResponse = false, waitForResponse = false, responseToWaitFor = 'OK', maxCumulativeTimeoutMs = 6000) {
        const CPP_AT_PARSE_ERROR_FLUSH_INTERVAL_MS = 1000; // How long to wait after a parse error to let the error message print.
        const RECEIVE_LOOP_PERIOD_MS = 10; // How often to check for new messages.
        const decodedResponse = [];

        const cumulativeTimeout = Date.now() + maxCumulativeTimeoutMs;

        while (waitForResponse) {
            if (Date.now() > cumulativeTimeout) {
                throw new Error(`Response timeout after ${maxCumulativeTimeoutMs} ms.`);
            }

            if (waitForResponse && this.messageQueue.length > 0) {
                const decoded_message = this.messageQueue.shift();
                // Match on individual lines so ambient log messages like "[ERROR] ..."
                // or strings containing "OK" don't cause false positives.
                // Use substring match for the expected terminator (handles both 'OK'
                // and custom prefixes like '+FEED='), but match ERROR strictly on a
                // whole line so ambient log lines like "[ERROR] ..." don't false-trigger.
                if (decoded_message.includes(responseToWaitFor)) {
                    waitForResponse = false;
                } else if (decoded_message.split(/[\r\n]+/).some(l => l.trim() === 'ERROR')) {
                    // Catch AT command errors (standalone ERROR response line).
                    this.flushInputBuffer(ADSBeeAT.ERROR_BUFFER_FLUSH_INTERVAL_MS);
                    throw new Error(`ERROR response: ${decoded_message}`);
                } else if (decoded_message.includes('CppAT::')) {
                    // Catch CppAT parse errors.
                    await new Promise(resolve => setTimeout(resolve, CPP_AT_PARSE_ERROR_FLUSH_INTERVAL_MS));
                    this.flushInputBuffer(ADSBeeAT.ERROR_BUFFER_FLUSH_INTERVAL_MS);
                    throw new Error(`CppAT parse error: ${decoded_message}`);
                }

                // Received a decoded message without errors.
                let logStr = '';
                try {
                    decodedResponse.push(decoded_message);
                    logStr = `Response (+${this.getMsTimestamp() - this.lastCmdTimestamp} ms): \t\t${decoded_message}`;
                } catch {
                    logStr = `Non-ASCII response (+${this.getMsTimestamp() - this.lastCmdTimestamp} ms): \t${raw}`;
                }

                if (printResponse && logStr) {
                    console.log(logStr);
                }
            }

            // Wait for a timeout so that we don't block the event loop.
            if (this.messageQueue.length > 0) {
                continue; // If we have messages, don't wait.
            }
            await new Promise(resolve => setTimeout(resolve, RECEIVE_LOOP_PERIOD_MS));

        }

        return decodedResponse;
    }

    /**
     * Send an AT command to the ADSBee device.
     * @param[in] cmdStr The AT command string to send.
     * @param[in] delay_ms Delay in milliseconds after sending the command.
     * @param[in] printResponse Whether to print the response to the console.
     * @param[in] waitForOkOrError Whether to wait for an OK or ERROR response before returning.
     * @param[in] maxCumulativeTimeoutMs Maximum cumulative timeout in milliseconds.
     * @return A promise that resolves with the decoded_message response lines.
     */
    async sendCmd(cmdStr, delay_ms = 10, printResponse = false, waitForResponse = false, responseToWaitFor = 'OK', maxCumulativeTimeoutMs = 6000) {
        this.lastCmdTimestamp = this.getMsTimestamp();

        if (printResponse) {
            console.log(`Command (${this.getMsTimestamp()} ms): \t${cmdStr.trim()}`);
        }

        if (this.ws.readyState !== WebSocket.OPEN) {
            await this.disconnect();
            await this.connect();
        }
        this.ws.send(new TextEncoder().encode(cmdStr));

        let attempts = 0;
        const maxAttempts = 3;

        while (attempts < maxAttempts) {
            attempts++;
            try {
                return await this.receiveResponse(printResponse, waitForResponse, responseToWaitFor, maxCumulativeTimeoutMs);
            } catch (error) {
                if (error.message.includes('Response timeout')) {
                    console.log(`Response timeout detected (attempt ${attempts}/${maxAttempts}), reconnecting...`);
                    await this.disconnect();
                    await this.connect();

                    if (attempts >= maxAttempts) {
                        throw error;
                    }
                    // Retry the send operation
                    this.ws.send(new TextEncoder().encode(cmdStr));
                } else {
                    throw error;
                }
            }
        }
    }

    /**
     * Send raw bytes to the ADSBee device.
     * @param {Uint8Array} data The data to send.
     * @param {boolean} printResponse Whether to print the response to the console.
     * @return A promise that resolves with the decoded_message response lines.
     */
    async sendBytes(data, printResponse = false, waitForOkOrError = false) {
        const RESPONSE_TO_WAIT_FOR = 'OK';
        const RESPONSE_TIMEOUT_MS = 3000;
        if (this.ws.readyState !== WebSocket.OPEN) {
            throw new Error(`Response timeout: WebSocket not open (readyState=${this.ws.readyState})`);
        }
        this.ws.send(data);
        return await this.receiveResponse(printResponse, waitForOkOrError, RESPONSE_TO_WAIT_FOR, RESPONSE_TIMEOUT_MS);
    }

    /**
     * Silence the console by silencing logs and turning off any output protocols. Call this before sending data
     * for firmware updates.
     */
    async silenceConsole() {
        await this.sendCmd("AT+LOG_LEVEL=ERRORS\r\n", 0, true, true);
        await this.sendCmd("AT+PROTOCOL_OUT=CONSOLE,NONE\r\n", 0, true, true);
    }

    /**
     * Get the flash partition that can currently be read from / written to (e.g. the flash partition that is
     * not currently being executed from).
     * @return The current OTA flash partition.
     */
    async otaGetFlashPartition() {
        const decodedResponse = await this.sendCmd("AT+OTA=GET_PARTITION\r\n", 0, true, true);

        for (const line of decodedResponse) {
            const match = line.match(/Partition: (\d+)/);
            if (match) {
                return parseInt(match[1]);
            }
        }
        return null;
    }

    /**
     * Write bytes to the current OTA flash partition.
     * @param {number} offset The offset in bytes to write to.
     * @param {Uint8Array} data The data to write.
     */
    async otaWriteBytes(offset, data) {
        const crc32 = this.calculateCRC32(data);
        const cmdResponse = await this.sendCmd(`AT+OTA=WRITE,${offset.toString(16)},${data.length},${crc32.toString(16)}\r\n`, 0, true, true, "READY");
        for (const line of cmdResponse) {
            if (line.includes('ERROR')) {
                // Flush remaining lines then throw the error.
                await this.flushInputBuffer(ADSBeeAT.ERROR_BUFFER_FLUSH_INTERVAL_MS);
                throw new Error(`Command failed with error: ${line}`);
            }
        }
        const dataResponse = await this.sendBytes(data, true, true);
        for (const line of dataResponse) {
            if (line.includes('ERROR')) {
                // Flush remaining lines then throw the error.
                await this.flushInputBuffer(ADSBeeAT.ERROR_BUFFER_FLUSH_INTERVAL_MS);
                throw new Error(`Data transfer failed with error: ${line}`);
            }
        }
    }

    /**
     * Erase bytes from the current OTA flash partition.
     * @param {number} offsetBytes The offset in bytes to erase from.
     * @param {number} lenBytes The length in bytes to erase.
     */
    async otaErase(offsetBytes = NaN, lenBytes = NaN) {
        const ERASE_TIMEOUT_MS = 20000; // Allow 20 seconds for flash erase to complete.
        if (!isNaN(offsetBytes) && !isNaN(lenBytes)) {
            await this.sendCmd(`AT+OTA=ERASE,${offsetBytes.toString(16)},${lenBytes}\r\n`, 0, true, true, "OK", ERASE_TIMEOUT_MS);
        } else {
            // Allow 20 seconds for flash erase to complete.
            await this.sendCmd("AT+OTA=ERASE\r\n", 0, true, true, "OK", ERASE_TIMEOUT_MS);
        }
    }

    /**
     * Write a file to the current OTA flash partition.
     * @param {File} file The file to write.
     */
    async otaWriteFile(file) {
        const HEADER_SIZE_BYTES = 5 * 4;
        const APP_OFFSET_BYTES = 4 * 1024;
        // Going larger than this can cause the heap to explode on the ESP32.
        const WRITE_CHUNK_BYTES = 0x1000 * 3;
        const MAX_ATTEMPTS_PER_CHUNK = 3;

        const partition = await this.otaGetFlashPartition();

        if (partition === null) {
            throw new Error("Failed to get OTA partition from ADSBee.");
        }

        const fileData = await this.readFile(file);
        const dataView = new DataView(fileData.buffer);

        const numPartitions = dataView.getUint32(0, true);
        if (partition > numPartitions) {
            throw new Error(`Partition ${partition} is out of range. Only ${numPartitions} partitions available.`);
        }

        const offset = dataView.getUint32(4 + 4 * partition, true);
        const contents = fileData.slice(offset);
        const headerContents = contents.slice(0, HEADER_SIZE_BYTES);
        const appLenBytes = dataView.getUint32(offset + 8, true);

        await this.otaErase(0, appLenBytes + HEADER_SIZE_BYTES);

        // Write the header
        await this.otaWriteBytes(0, headerContents);

        // Write the application in chunks
        for (let i = HEADER_SIZE_BYTES; i < HEADER_SIZE_BYTES + appLenBytes; i += WRITE_CHUNK_BYTES) {
            const offsetBytes = (i - HEADER_SIZE_BYTES) + APP_OFFSET_BYTES;
            let success = false;
            let attempts = 0;
            while (!success && attempts < MAX_ATTEMPTS_PER_CHUNK) {
                try {
                    if (attempts > 0) {
                        // We are here on a retry, so erase the chunk first.
                        await this.otaErase(offsetBytes, WRITE_CHUNK_BYTES);
                    }
                    const chunk = contents.slice(i, Math.min(i + WRITE_CHUNK_BYTES, HEADER_SIZE_BYTES + appLenBytes));
                    await this.otaWriteBytes(offsetBytes, chunk);
                    success = true;
                } catch (error) {
                    console.error(error);
                    console.error(`Failed to write chunk at offset ${offsetBytes}. Retrying (${attempts + 1}/${MAX_ATTEMPTS_PER_CHUNK})... `);
                    attempts++; // Wait to erase until the next loop so that we can re-use the try-catch and don't erase before final failure if the first few retry attempts also fail.
                }
            }
        }

        // Verify and boot the new partition
        await this.sendCmd("AT+OTA=VERIFY\r\n", 0, true, true);
    }

    /**
     * Boot the current OTA flash partition.
     */
    async otaBoot() {
        await this.sendCmd("AT+OTA=BOOT\r\n", 0, true);
    }

    /**
     * Read a file as an ArrayBuffer.
     * @param {File} file The file to read.
     * @return {Promise<Uint8Array>} A promise that resolves with the file data as an ArrayBuffer.
     */
    async readFile(file) {
        return new Promise((resolve, reject) => {
            const reader = new FileReader();
            reader.onload = () => resolve(new Uint8Array(reader.result));
            reader.onerror = reject;
            reader.readAsArrayBuffer(file);
        });
    }

    /**
     * Calculate the CRC32 checksum of a Uint8Array.
     * @param {Uint8Array} data The data to calculate the CRC32 checksum for.
     * @return {number} The CRC32 checksum.
     */
    calculateCRC32(data) {
        let crc = 0xFFFFFFFF;
        for (let i = 0; i < data.length; i++) {
            crc = (crc >>> 8) ^ ADSBeeAT.crcTable[(crc ^ data[i]) & 0xFF];
        }
        return (crc ^ 0xFFFFFFFF) >>> 0;
    }

    static crcTable = (() => {
        const table = new Uint32Array(256);
        for (let i = 0; i < 256; i++) {
            let c = i;
            for (let j = 0; j < 8; j++) {
                c = ((c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1));
            }
            table[i] = c;
        }
        return table;
    })();
}

class FirmwareUploader {
    constructor(adsbeeUrl) {
        this.adsbeeUrl = adsbeeUrl;
        this.uploadButton = document.getElementById('uploadButton');
        this.fileInput = document.getElementById('fileInput');

        this.setupEventListeners();
    }

    setupEventListeners() {
        this.uploadButton.addEventListener('click', () => {
            this.fileInput.click();
        });

        this.fileInput.addEventListener('change', async (event) => {
            const file = event.target.files[0];
            if (file) {
                await this.uploadFirmware(file);
            }
            this.fileInput.value = '';
        });
    }

    setUploadingState(isUploading) {
        this.uploadButton.disabled = isUploading;
        if (isUploading) {
            this.uploadButton.innerHTML = '<span class="spinner"></span> Uploading...';
        } else {
            this.uploadButton.innerHTML = 'Upload Firmware';
        }
    }

    showModal() {
        const log = document.getElementById('firmware-modal-log');
        if (log) log.innerHTML = '';
        document.getElementById('firmware-modal').style.display = 'flex';
    }

    appendToModalLog(text) {
        const log = document.getElementById('firmware-modal-log');
        if (!log) return;
        const trimmed = text.trim();
        if (!trimmed) return;
        const line = document.createElement('div');
        line.textContent = trimmed;
        log.appendChild(line);
        while (log.children.length > 100) {
            log.removeChild(log.firstChild);
        }
        log.scrollTop = log.scrollHeight;
    }

    hideModal() {
        document.getElementById('firmware-modal').style.display = 'none';
    }

    setModalStatus(text) {
        document.getElementById('firmware-modal-status').textContent = text;
    }

    updateProgress(percent) {
        document.getElementById('firmware-modal-fill').style.width = `${percent}%`;
        document.getElementById('firmware-modal-text').textContent = `${percent}%`;
        if (percent === 0) {
            this.setModalStatus('Erasing flash...');
        } else if (percent < 100) {
            this.setModalStatus('Writing firmware...');
        } else {
            this.setModalStatus('Verifying & rebooting...');
        }
    }

    showSuccess() {
        this.uploadButton.innerHTML = 'Upload Complete';
        this.setModalStatus('Upload complete! Device is rebooting.');
        setTimeout(() => {
            this.uploadButton.innerHTML = 'Upload Firmware';
            this.hideModal();
        }, 5000);
    }

    showError(message) {
        this.uploadButton.innerHTML = 'Upload Failed';
        this.setModalStatus(`Upload failed: ${message}`);
        setTimeout(() => {
            this.uploadButton.innerHTML = 'Upload Firmware';
            this.hideModal();
        }, 5000);
    }

    async uploadFirmware(file) {
        let originalOtaWriteBytes = NaN;
        let adsbee = null;
        const origConsoleLog = console.log;
        try {
            this.setUploadingState(true);
            this.updateProgress(0);
            this.showModal();
            console.log = (...args) => {
                origConsoleLog.apply(console, args);
                this.appendToModalLog(args.join(' '));
            };

            adsbee = new ADSBeeAT(this.adsbeeUrl);
            await adsbee.connect();

            const totalSize = file.size / 2; // Two firmware images in file, we're only flashing one.
            let uploadedSize = 0;

            // Override otaWriteBytes to track progress
            originalOtaWriteBytes = adsbee.otaWriteBytes.bind(adsbee);
            adsbee.otaWriteBytes = async (offset, data) => {
                await originalOtaWriteBytes(offset, data);
                uploadedSize += data.length;
                const progress = Math.min(Math.round((uploadedSize / totalSize) * 100), 100);
                this.updateProgress(progress);
            };

            await adsbee.flushInputBuffer();
            await adsbee.silenceConsole();
            await adsbee.flushInputBuffer();

            // Receiver already gets disabled during data chunk transfers, but this simplifies it a bit.
            await adsbee.sendCmd('AT+RX_ENABLE=0\r\n', 0, true, true);

            // Pause other WebSocket clients to prevent httpd async queue contention during OTA.
            consoleWebSocket.pause();
            metricsWebSocket.pause();

            await adsbee.otaWriteFile(file);
            await adsbee.otaBoot();

            this.updateProgress(100);
            this.showSuccess();

        } catch (error) {
            console.error('Firmware upload failed:', error);
            this.showError(error.message || 'Failed to upload firmware. Please try again.');
        } finally {
            console.log = origConsoleLog;
            this.setUploadingState(false);
            if (adsbee && !isNaN(originalOtaWriteBytes)) {
                adsbee.otaWriteBytes = originalOtaWriteBytes;
            }
            if (adsbee) await adsbee.disconnect();
            consoleWebSocket.resume();
            metricsWebSocket.resume();
        }
    }
}

class SettingsManager {
    constructor(adsbeeUrl) {
        this.adsbeeUrl = adsbeeUrl;
        this.downloadButton = document.getElementById('downloadSettings');
        this.restoreButton = document.getElementById('restoreSettings');
        this.settingsFileInput = document.getElementById('settingsFile');

        this.setupEventListeners();
    }

    setupEventListeners() {
        this.downloadButton.addEventListener('click', () => {
            this.downloadSettings();
        });

        this.restoreButton.addEventListener('click', () => {
            this.settingsFileInput.click();
        });

        this.settingsFileInput.addEventListener('change', async (event) => {
            const file = event.target.files[0];
            if (file) {
                await this.restoreSettings(file);
            }
            this.settingsFileInput.value = '';
        });
    }

    async downloadSettings() {
        const adsbee = new ADSBeeAT(this.adsbeeUrl);
        await adsbee.connect();
        const response = await adsbee.sendCmd('AT+SETTINGS?DUMP\r\n', 0, true, true);

        // Only keep lines starting with AT+
        const settingsLines = response.filter(line => line.startsWith('AT+'));

        const blob = new Blob([settingsLines.join('\n')], { type: 'text/plain' });
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = `adsbee_${new Date().toISOString().replace(/[:.]/g, '-')}.settings`;
        a.click();
        URL.revokeObjectURL(url);
    }

    async restoreSettings(file) {
        const adsbee = new ADSBeeAT(this.adsbeeUrl);
        await adsbee.connect();

        const text = await file.text();
        const commands = text.split('\n').filter(line => line.trim());

        for (const command of commands) {
            try {
                await adsbee.sendCmd(command + '\r\n', 0, true, true);
            } catch (error) {
                throw new Error(`Failed executing command: ${command} - ${error.message}`);
            }
        }
    }
}

// ─── Altitude colour (tar1090-inspired) ──────────────────────────────────────
function acAltColor(altFt) {
    if (altFt == null) return '#888888';
    if (altFt <  1000) return '#FF2222';
    if (altFt <  3000) return '#FF6B00';
    if (altFt <  7000) return '#FFB300';
    if (altFt < 12000) return '#CCDF00';
    if (altFt < 20000) return '#00E676';
    if (altFt < 30000) return '#00B0FF';
    if (altFt < 40000) return '#7C4DFF';
    return '#E040FB';
}

// ─── AircraftWebSocket ────────────────────────────────────────────────────────
class AircraftWebSocket {
    constructor(url) {
        this.url = url;
        this.paused = false;
        this.onMessage = null;
        this.ws = null;
        this._timer = null;
        this._connect();
    }

    _connect() {
        if (this.paused) return;
        this.ws = new WebSocket(this.url);
        this.ws.onopen  = () => console.log('[AircraftWS] connected');
        this.ws.onmessage = (ev) => {
            if (!this.onMessage) return;
            try { this.onMessage(JSON.parse(ev.data)); } catch (_) {}
        };
        this.ws.onclose = () => {
            clearTimeout(this._timer);
            this._timer = setTimeout(() => { if (!this.paused) this._connect(); }, 3000);
        };
        this.ws.onerror = (e) => console.error('[AircraftWS] error', e);
    }

    pause()  { this.paused = true;  clearTimeout(this._timer); if (this.ws) this.ws.close(); }
    resume() { if (!this.paused) return; this.paused = false; this._connect(); }
    close(code, reason) { this.paused = true; clearTimeout(this._timer); if (this.ws) this.ws.close(code, reason); }
}

// ─── AircraftStore ────────────────────────────────────────────────────────────
const kMaxTrailPoints = 500;

class AircraftStore {
    constructor() {
        this.aircraft    = new Map();  // hex → latest merged data
        this.trails      = new Map();  // hex → [{lat, lon, alt}]
        this._seenNow    = new Set();  // hexes seen since last sweep
        this._seenPrev   = new Set();  // hexes seen during the previous sweep interval
    }

    ingest(ac) {
        if (!ac.hex) return;
        const prev = this.aircraft.get(ac.hex) || {};
        this.aircraft.set(ac.hex, { ...prev, ...ac });
        this._seenNow.add(ac.hex);
        if (ac.lat != null && ac.lon != null) {
            const t = this.trails.get(ac.hex) || [];
            t.push({ lat: ac.lat, lon: ac.lon, alt: ac.alt_baro ?? null });
            if (t.length > kMaxTrailPoints) t.shift();
            this.trails.set(ac.hex, t);
        }
    }

    // Remove any aircraft absent from both this interval and the previous one,
    // then rotate the seen-sets. The two-interval window tolerates timing skew
    // between the server's 1 Hz send and the client's 1 Hz tick.
    sweep() {
        for (const hex of this.aircraft.keys()) {
            if (!this._seenNow.has(hex) && !this._seenPrev.has(hex)) {
                this.aircraft.delete(hex);
                this.trails.delete(hex);
            }
        }
        this._seenPrev = this._seenNow;
        this._seenNow  = new Set();
    }

    all() { return [...this.aircraft.values()]; }
}

// ─── RadarMap ─────────────────────────────────────────────────────────────────
class RadarMap {
    constructor(containerId, store) {
        this.containerId        = containerId;
        this.store              = store;
        this.map                = null;
        this.markers            = new Map();   // hex → L.Marker
        this.trailLines         = new Map();   // hex → L.LayerGroup
        this.selectedHex        = null;
        this.onSelectionChanged = null;        // (hex | null) → void
        this._ready             = false;
        this._offline           = false;
        this._autoCenter        = true;
    }

    async init() {
        if (this._ready || this._offline) return;
        try {
            await this._loadLeaflet();
            this._initMap();
            this._ready = true;
        } catch (_) {
            this._offline = true;
            const el = document.getElementById(this.containerId);
            if (el) el.innerHTML = '<div class="map-offline-banner">Map tiles require internet access — aircraft data is still live in the table below.</div>';
        }
    }

    _loadLeaflet() {
        return new Promise((resolve, reject) => {
            if (window.L) { resolve(); return; }
            const tid = setTimeout(reject, 8000);
            const link = document.createElement('link');
            link.rel = 'stylesheet';
            link.href = 'https://unpkg.com/leaflet@1.9.4/dist/leaflet.css';
            document.head.appendChild(link);
            const script = document.createElement('script');
            script.src = 'https://unpkg.com/leaflet@1.9.4/dist/leaflet.js';
            script.onload  = () => { clearTimeout(tid); resolve(); };
            script.onerror = () => { clearTimeout(tid); reject(); };
            document.head.appendChild(script);
        });
    }

    _initMap() {
        this.map = L.map(this.containerId, { preferCanvas: true }).setView([20, 0], 2);
        L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
            attribution: '© <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a>',
            maxZoom: 18,
        }).addTo(this.map);
    }

    invalidate() {
        if (this.map) setTimeout(() => this.map.invalidateSize(), 0);
    }

    _makeIcon(color, track, isGround, isSelected) {
        const ring = isSelected ? '<circle cx="16" cy="16" r="15" fill="none" stroke="white" stroke-width="2" opacity="0.7"/>' : '';
        if (isGround) {
            const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="32" height="32" viewBox="0 0 32 32">` +
                ring +
                `<rect x="7" y="7" width="18" height="18" rx="3" transform="rotate(45 16 16)" fill="#888888" stroke="rgba(0,0,0,0.5)" stroke-width="1.2"/>` +
                `</svg>`;
            return L.divIcon({ html: svg, className: '', iconSize: [32, 32], iconAnchor: [16, 16] });
        }
        const rot = (track != null) ? track : 0;
        const svg = `<svg xmlns="http://www.w3.org/2000/svg" width="32" height="32" viewBox="0 0 32 32">` +
            ring +
            `<g transform="rotate(${rot},16,16)">` +
            `<polygon points="16,2 23,27 16,22 9,27" fill="${color}" stroke="rgba(0,0,0,0.5)" stroke-width="1.2"/>` +
            `</g></svg>`;
        return L.divIcon({ html: svg, className: '', iconSize: [32, 32], iconAnchor: [16, 16] });
    }

    selectAircraft(hex) {
        if (this.selectedHex === hex) {
            this._clearTrail(this.selectedHex);
            this.selectedHex = null;
            this._hideInfoPanel();
            if (this.onSelectionChanged) this.onSelectionChanged(null);
        } else {
            if (this.selectedHex) this._clearTrail(this.selectedHex);
            this.selectedHex = hex;
            this._drawTrail(hex);
            const ac = this.store.aircraft.get(hex);
            if (ac) this._showInfoPanel(ac);
            if (this.onSelectionChanged) this.onSelectionChanged(hex);
        }
    }

    deselect() {
        if (this.selectedHex) this._clearTrail(this.selectedHex);
        this.selectedHex = null;
        this._hideInfoPanel();
        if (this.onSelectionChanged) this.onSelectionChanged(null);
    }

    _clearTrail(hex) {
        if (this.trailLines.has(hex)) {
            this.trailLines.get(hex).remove();
            this.trailLines.delete(hex);
        }
    }

    update() {
        if (!this._ready) return;
        const live = new Set();

        for (const ac of this.store.all()) {
            if (ac.lat == null || ac.lon == null) continue;
            live.add(ac.hex);
            const color    = acAltColor(ac.alt_baro);
            const isGround = !!ac.on_ground;
            const isSel    = ac.hex === this.selectedHex;
            const icon     = this._makeIcon(color, ac.track, isGround, isSel);

            if (this.markers.has(ac.hex)) {
                const m = this.markers.get(ac.hex);
                m.setLatLng([ac.lat, ac.lon]);
                m.setIcon(icon);
            } else {
                const hex = ac.hex;
                const m = L.marker([ac.lat, ac.lon], { icon })
                    .addTo(this.map)
                    .on('click', () => this.selectAircraft(hex));
                this.markers.set(hex, m);
            }
        }

        // Refresh trail and info panel for selected aircraft each tick
        if (this.selectedHex && this.store.aircraft.has(this.selectedHex)) {
            this._drawTrail(this.selectedHex);
            const ac = this.store.aircraft.get(this.selectedHex);
            if (ac) this._showInfoPanel(ac);
        }

        // Auto-fit view on first aircraft
        if (this._autoCenter && this.markers.size > 0) {
            try {
                const bounds = L.featureGroup([...this.markers.values()]).getBounds();
                if (bounds.isValid()) {
                    this.map.fitBounds(bounds, { padding: [50, 50], maxZoom: 9 });
                    this._autoCenter = false;
                }
            } catch (_) {}
        }

        // Remove markers for gone aircraft
        for (const hex of [...this.markers.keys()]) {
            if (!live.has(hex)) {
                this.markers.get(hex).remove();
                this.markers.delete(hex);
                this._clearTrail(hex);
                if (hex === this.selectedHex) this.deselect();
            }
        }
    }

    _drawTrail(hex) {
        if (!this._ready) return;
        this._clearTrail(hex);
        const pts = this.store.trails.get(hex);
        if (!pts || pts.length < 2) return;
        const group = L.layerGroup().addTo(this.map);
        for (let i = 0; i < pts.length - 1; i++) {
            const p1 = pts[i], p2 = pts[i + 1];
            L.polyline([[p1.lat, p1.lon], [p2.lat, p2.lon]], {
                color: acAltColor(p1.alt), weight: 2, opacity: 0.75
            }).addTo(group);
        }
        this.trailLines.set(hex, group);
    }

    _showInfoPanel(ac) {
        const panel  = document.getElementById('aircraft-sidebar');
        const title  = document.getElementById('sidebar-title');
        const fields = document.getElementById('sidebar-fields');
        if (!panel) return;
        if (title) title.textContent = (ac.flight || '').trim() || ac.hex;

        const defs = [
            ['hex',          'ICAO',          v => v],
            ['flight',       'Callsign',      v => v.trim() || null],
            ['squawk',       'Squawk',        v => v],
            ['type',         'Type',          v => v],
            ['category',     'Category',      v => v],
            ['on_ground',    'On ground',     v => v ? 'Yes' : null],
            ['alt_baro',     'Alt baro',      v => v.toLocaleString() + ' ft'],
            ['alt_geom',     'Alt geom',      v => v.toLocaleString() + ' ft'],
            ['gs',           'Speed',         v => Math.round(v) + ' kt'],
            ['track',        'Track',         v => v.toFixed(1) + '°'],
            ['mag_heading',  'Mag heading',   v => v.toFixed(1) + '°'],
            ['true_heading', 'True heading',  v => v.toFixed(1) + '°'],
            ['baro_rate',    'Vert rate',     v => v.toLocaleString() + ' fpm'],
            ['geom_rate',    'Geom rate',     v => v.toLocaleString() + ' fpm'],
            ['lat',          'Latitude',      v => v.toFixed(5)],
            ['lon',          'Longitude',     v => v.toFixed(5)],
            ['rssi',         'RSSI',          v => v.toFixed(1) + ' dBm'],
            ['messages',     'Messages',      v => v.toLocaleString()],
            ['nic',          'NIC',           v => String(v)],
            ['nic_baro',     'NIC baro',      v => String(v)],
            ['nac_p',        'NAC p',         v => String(v)],
            ['nac_v',        'NAC v',         v => String(v)],
            ['sil',          'SIL',           v => String(v)],
            ['gva',          'GVA',           v => String(v)],
            ['sda',          'SDA',           v => String(v)],
            ['version',      'ADS-B version', v => String(v)],
            ['alert',        'Alert',         v => v ? 'Yes' : null],
            ['spi',          'SPI (Ident)',   v => v ? 'Yes' : null],
            ['emergency',    'Emergency',     v => v],
        ];

        const rows = [];
        for (const [key, label, fmt] of defs) {
            const raw = ac[key];
            if (raw == null || raw === '') continue;
            let val;
            try { val = fmt(raw); } catch (_) { val = String(raw); }
            if (val == null || val === '') continue;
            rows.push(`<span class="info-label">${label}</span><span class="info-value">${val}</span>`);
        }

        if (fields) fields.innerHTML = rows.join('');
        panel.style.display = 'flex';
        this.invalidate();
    }

    _hideInfoPanel() {
        const panel = document.getElementById('aircraft-sidebar');
        if (panel) panel.style.display = 'none';
        this.invalidate();
    }
}

// ─── AircraftTable ────────────────────────────────────────────────────────────
class AircraftTable {
    constructor(tbodyId, store, onSelect) {
        this.tbody       = document.getElementById(tbodyId);
        this.store       = store;
        this.onSelect    = onSelect;   // (hex) → void
        this.selectedHex = null;
    }

    update() {
        if (!this.tbody) return;
        const acs = this.store.all().sort((a, b) => {
            const aa = a.alt_baro ?? -Infinity;
            const bb = b.alt_baro ?? -Infinity;
            return bb - aa;
        });

        const rows = new Map();
        for (const row of this.tbody.querySelectorAll('tr[data-hex]')) rows.set(row.dataset.hex, row);

        const seen = new Set();
        for (const ac of acs) {
            seen.add(ac.hex);
            const cs    = (ac.flight || '').trim();
            const sqwk  = ac.squawk  ?? '';
            const alt   = ac.alt_baro != null ? ac.alt_baro.toLocaleString() : '';
            const gs    = ac.gs       != null ? Math.round(ac.gs)            : '';
            const hdg   = ac.track    != null ? Math.round(ac.track) + '°'  : '';
            const lat   = ac.lat      != null ? ac.lat.toFixed(4)            : '';
            const lon   = ac.lon      != null ? ac.lon.toFixed(4)            : '';
            const rssi  = ac.rssi     != null ? ac.rssi.toFixed(1)           : '';
            const color = acAltColor(ac.alt_baro);

            if (rows.has(ac.hex)) {
                const r = rows.get(ac.hex);
                const c = r.querySelectorAll('td');
                c[0].style.color = color; c[0].textContent = ac.hex;
                c[1].textContent = cs;   c[2].textContent = sqwk;
                c[3].textContent = alt;  c[4].textContent = gs;
                c[5].textContent = hdg;  c[6].textContent = lat;
                c[7].textContent = lon;  c[8].textContent = rssi;
                r.classList.toggle('trail-active', this.selectedHex === ac.hex);
            } else {
                const r = document.createElement('tr');
                r.dataset.hex = ac.hex;
                r.innerHTML = `<td style="color:${color};font-family:monospace">${ac.hex}</td>` +
                    `<td>${cs}</td><td>${sqwk}</td><td>${alt}</td><td>${gs}</td>` +
                    `<td>${hdg}</td><td>${lat}</td><td>${lon}</td><td>${rssi}</td>`;
                r.addEventListener('click', () => {
                    if (this.onSelect) this.onSelect(ac.hex);
                });
                this.tbody.appendChild(r);
            }
        }

        for (const [hex, row] of rows) {
            if (!seen.has(hex)) {
                row.remove();
                if (this.selectedHex === hex) this.selectedHex = null;
            }
        }
    }

    setSelected(hex) {
        this.selectedHex = hex;
        if (!this.tbody) return;
        for (const row of this.tbody.querySelectorAll('tr[data-hex]')) {
            row.classList.toggle('trail-active', row.dataset.hex === hex);
        }
    }
}
