const METRIC_UNITS = {
    'num_mode_s_aircraft': 'aircraft',
    'num_uat_aircraft':    'aircraft',
};

class ConsoleWebSocket {
    constructor(url) {
        this.url = url;
        this.paused = false;
        this.captureCallback = null;
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
        setTimeout(() => {
            if (!this.paused) this.init();
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
    constructor(id, maxPoints = 20) {
        this.svg = document.getElementById(id);
        this.maxPoints = maxPoints;
        this.points = Array(maxPoints).fill(0);
        this.valueEl = this.svg.parentNode.querySelector('.metric-value');
        this.createPaths();
    }

    createPaths() {
        const line = document.createElementNS('http://www.w3.org/2000/svg', 'path');
        const area = document.createElementNS('http://www.w3.org/2000/svg', 'path');
        area.classList.add('area');
        this.svg.appendChild(area);
        this.svg.appendChild(line);
        this.linePath = line;
        this.areaPath = area;
    }

    update(value, unit = 'msg/s') {
        this.points.push(value);
        this.points.shift();
        this.valueEl.textContent = `${value} ${unit}`;

        const max = Math.max(...this.points, 1);
        const points = this.points.map((p, i) => [
            (i / (this.maxPoints - 1)) * 100,
            30 - (p / max) * 30
        ]);

        const line = points.map((p, i) => `${i === 0 ? 'M' : 'L'} ${p[0]} ${p[1]}`).join(' ');
        this.linePath.setAttribute('d', line);

        const area = line + ` L ${points[points.length - 1][0]} 30 L 0 30 Z`;
        this.areaPath.setAttribute('d', area);
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
        card.innerHTML = `
  <div class="metric-title" title="${label}">${label}</div>
  <div class="metric-value">0 ${unit}</div>
  <svg class="sparkline" id="${this.id}" viewBox="0 0 100 30"></svg>
`;
        this.card = card;
        this.container.appendChild(card);
        this.chart = new SparklineChart(this.id);
    }

    destroy() {
        this.container.removeChild(this.card);
        delete this.chart;
    }

    labelToID(label) {
        return label.replace(/[^a-zA-Z0-9]/g, '-');
    }

    update(value) {
        this.chart.update(value, this.unit);
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

        this.ws.onopen = () => {
            console.log('Connected to WebSocket');
        };

        this.ws.onclose = () => {
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
                    const feedMetrics = {};
                    for (let i = 0; i < serverMetrics['feed_uri'].length; i++) {
                        if (serverMetrics['feed_uri'][i] === '') continue;
                        feedMetrics[serverMetrics['feed_uri'][i]] = serverMetrics['feed_mps'][i];
                        this.feedSlotMap[serverMetrics['feed_uri'][i]] = i;
                    }
                    this.updateFeedCards(feedMetrics);
                    this.feedsCountEl.textContent = `Feeds: ${Object.keys(feedMetrics).length}`;
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
                        'CSBEE', 'MAVLINK1', 'MAVLINK2', 'GDL90'];

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

    static async save() {
        const slot     = document.getElementById('feed-slot').value;
        const uri      = document.getElementById('feed-uri').value.trim();
        const port     = document.getElementById('feed-port').value;
        const active   = document.getElementById('feed-active').checked ? 1 : 0;
        const protocol = document.getElementById('feed-protocol').value;
        const statusEl = document.getElementById('feed-modal-status');

        statusEl.textContent = 'Saving...';
        const adsbee = new ADSBeeAT(HOST_URI);
        try {
            await adsbee.connect();
            await adsbee.sendCmd(`AT+FEED=${slot},${uri},${port},${active},${protocol}\r\n`, 0, true, true, 'OK', 5000);
            await adsbee.sendCmd(`AT+SETTINGS=SAVE\r\n`, 0, true, true, 'OK', 5000);
            statusEl.textContent = 'Saved.';
            setTimeout(() => FeedEditor.close(), 800);
        } catch (e) {
            statusEl.textContent = `Error: ${e.message}`;
        } finally {
            await adsbee.disconnect();
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
        this.progressContainer = document.getElementById('progressContainer');
        this.progressFill = document.getElementById('progressFill');
        this.progressText = document.getElementById('progressText');
        this.successAlert = document.getElementById('successAlert');
        this.errorAlert = document.getElementById('errorAlert');

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
            this.progressContainer.style.display = 'block';
        } else {
            this.uploadButton.innerHTML = 'Upload Firmware';
            this.progressContainer.style.display = 'none';
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
        this.progressFill.style.width = `${percent}%`;
        this.progressText.textContent = `${percent}%`;
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
        this.successAlert.style.display = 'block';
        this.errorAlert.style.display = 'none';
        this.uploadButton.innerHTML = 'Upload Complete';
        this.setModalStatus('Upload complete! Device is rebooting.');
        setTimeout(() => {
            this.successAlert.style.display = 'none';
            this.uploadButton.innerHTML = 'Upload Firmware';
            this.hideModal();
        }, 5000);
    }

    showError(message) {
        this.errorAlert.textContent = message;
        this.errorAlert.style.display = 'block';
        this.successAlert.style.display = 'none';
        this.uploadButton.innerHTML = 'Upload Failed';
        this.setModalStatus(`Upload failed: ${message}`);
        setTimeout(() => {
            this.errorAlert.style.display = 'none';
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
