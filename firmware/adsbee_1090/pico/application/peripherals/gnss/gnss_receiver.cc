#include "gnss_receiver.hh"

#include "comms.hh"             // For comms_manager (UART I/O + baud) and CONSOLE_* logging.
#include "hal.hh"               // For get_time_since_boot_ms().
#include "hardware/watchdog.h"  // For watchdog_update() during the blocking boot-delay wait.

void GNSSReceiver::ClaimUart() {
    // Bring the GNSS UART up to a known state. uart0 is shared with the ESP32 flasher (GPIO 16/17),
    // which calls uart_deinit(uart0) when it finishes; claim the GNSS pins (GPIO 0/1) and
    // (re)initialize the peripheral here so a prior ESP32 flash cannot leave the GNSS link dead.
    //
    // Fully reset the peripheral before re-init. On a cold boot (no ESP32 flash) uart0 has already
    // been brought up by CommsManager::Init() -- and, until we re-baud below, at a rate that doesn't
    // match the module, so its RX FIFO has been filling with framing-error garbage. uart_init() on an
    // already-live uart0 does not reliably clear that latched state, which corrupts the first probe.
    // uart_deinit() first mirrors the clean-peripheral state the ESP32 flasher's DeInit() hands us on
    // the post-flash path (which is why GNSS bring-up is reliable there but flaky on cold boot).
    uart_deinit(config_.uart_handle);
    gpio_set_function(config_.uart_tx_pin, GPIO_FUNC_UART);
    gpio_set_function(config_.uart_rx_pin, GPIO_FUNC_UART);
    uart_set_translate_crlf(config_.uart_handle, false);
    uart_init(config_.uart_handle, GetDefaultBaudrate());

    // Drain any bytes left in the RX FIFO from before the re-init so the first UBX-MON-VER probe
    // reads a clean stream (mirrors the flasher's EnterBootloader() flush).
    while (uart_is_readable(config_.uart_handle)) {
        (void)uart_getc(config_.uart_handle);
    }
}

bool GNSSReceiver::Init() {
    // No module populated on this board: don't touch any GNSS hardware (UART, enable pin, baud). Report
    // unhealthy so the application uses its non-GNSS position source; Update() stays a harmless no-op.
    if (!IsModulePresent()) {
        healthy_ = false;
        return false;
    }

    ClaimUart();

    // Power on the module via the active-low enable pin (if connected) and wait for it to boot.
    if (config_.enable_pin != UINT16_MAX) {
        gpio_init(config_.enable_pin);
        gpio_set_dir(config_.enable_pin, GPIO_OUT);
        SetEnable(true);

        // The enable pin gates VCC/VCC_IO, so the module cold-boots here. Busy-wait the
        // receiver-specific boot delay before sending configuration. Poke the watchdog while we wait:
        // this runs before the main super-loop's first PokeWatchdog(), so a multi-second boot delay
        // must not starve the (already-live) watchdog.
        uint32_t enable_timestamp_ms = get_time_since_boot_ms();
        while (get_time_since_boot_ms() - enable_timestamp_ms < GetBootDelayMs()) {
            watchdog_update();
            tight_loop_contents();
        }
    }

    // Match our UART baud to the receiver's default so we can talk to it.
    comms_manager.SetBaudRate(SettingsManager::kGNSSUART, GetDefaultBaudrate());

    // Send receiver-specific configuration. SendInitCommands() also serves as the liveness check:
    // if the module does not acknowledge, we mark it unhealthy and let the application fall back to
    // its non-GNSS position source.
    healthy_ = SendInitCommands();
    if (!healthy_) {
        CONSOLE_WARNING("GNSSReceiver::Init",
                        "GNSS module did not respond; GNSS position source will be unavailable.");
        return false;
    }

    CONSOLE_INFO("GNSSReceiver::Init", "GNSS module configured at %lu baud.",
                 static_cast<unsigned long>(GetDefaultBaudrate()));
    return true;
}

bool GNSSReceiver::Update() {
    // Skip while the GNSS pins are handed over to the ESP32 flasher; uart0 is not ours right now.
    if (suspended_) return true;

    // Stamp the parser with the current time so applied fixes carry a freshness timestamp.
    uint32_t now_ms = get_time_since_boot_ms();
    parser_.SetTimestampMs(now_ms);

    // Drain all currently available bytes from the GNSS UART.
    char c;
    while (comms_manager.iface_getc(SettingsManager::kGNSSUART, c)) {
        NMEAParser::SentenceType result = parser_.IngestByte(c);
        // TEMPORARY: also feed the byte to the receiver-specific binary sniffer (UBX for ublox).
        DebugIngestByte(c);
        // TEMPORARY debug instrumentation (remove once root cause found).
        debug_total_rx_bytes_++;
        if (result != NMEAParser::kSentenceNone) {
            debug_last_sentence_ = result;
            if (result == NMEAParser::kSentenceGGA) debug_gga_count_++;
            if (result == NMEAParser::kSentenceRMC) debug_rmc_count_++;
            if (result == NMEAParser::kSentenceChecksumFail) debug_cksum_fail_count_++;
        }
    }

    // TEMPORARY periodic debug print (remove once root cause found). Uses ungated CONSOLE_PRINTF so
    // it shows regardless of the configured log level.
    if (now_ms - debug_last_print_timestamp_ms_ >= kDebugPrintIntervalMs) {
        debug_last_print_timestamp_ms_ = now_ms;
        const GNSSFix& f = parser_.fix();
        CONSOLE_PRINTF(
            "GNSS dbg: healthy=%d rx_bytes=%lu last_sentence=%d gga=%lu rmc=%lu cksum_fail=%lu | "
            "fix: valid=%d q=%u sats=%u lat=%.5f lon=%.5f age_ms=%lu hasfix=%d\r\n",
            healthy_, static_cast<unsigned long>(debug_total_rx_bytes_), static_cast<int>(debug_last_sentence_),
            static_cast<unsigned long>(debug_gga_count_), static_cast<unsigned long>(debug_rmc_count_),
            static_cast<unsigned long>(debug_cksum_fail_count_), f.valid, f.fix_quality, f.num_satellites,
            f.latitude_deg, f.longitude_deg,
            static_cast<unsigned long>(now_ms - f.last_update_timestamp_ms), HasValidFix());
    }

    // TEMPORARY: periodically dump module RF/antenna status (ublox UBX-MON-RF) to diagnose 0-sats.
    // Throttled harder than the counter print because polling UBX briefly competes with the NMEA drain.
    if (healthy_ && now_ms - debug_last_rf_dump_timestamp_ms_ >= kDebugRfDumpIntervalMs) {
        debug_last_rf_dump_timestamp_ms_ = now_ms;
        DebugDumpModuleStatus();
    }
    return true;
}

void GNSSReceiver::SuspendForUartHandover() {
    // Nothing to park if the module never came up: its pins aren't driving UART0 with real traffic,
    // and skipping avoids stalling the flash path on boards with no GNSS.
    if (!healthy_ || suspended_) return;
    suspended_ = true;
    // De-mux the GNSS pins from uart0 so the module can no longer drive UART0 RX. On RP2040 a
    // GPIO's function select determines which peripheral input can see it; leaving GPIO 1 on
    // GPIO_FUNC_UART would keep feeding the module's byte stream into the shared UART0 RX FIFO and
    // corrupt the ESP-ROM bootloader handshake once the flasher claims GPIO 16/17. Park the pins
    // as plain SIO inputs. The module stays powered (enable pin untouched) so its BBR stays warm.
    gpio_set_function(config_.uart_rx_pin, GPIO_FUNC_SIO);
    gpio_set_function(config_.uart_tx_pin, GPIO_FUNC_SIO);
    gpio_set_dir(config_.uart_rx_pin, GPIO_IN);
    gpio_set_dir(config_.uart_tx_pin, GPIO_IN);
}

void GNSSReceiver::ResumeAfterUartHandover() {
    if (!suspended_) return;  // Not handed over.
    // Re-claim the GNSS pins and re-init uart0 (the flasher's DeInit() called uart_deinit(uart0)).
    ClaimUart();
    comms_manager.SetBaudRate(SettingsManager::kGNSSUART, GetDefaultBaudrate());
    // The module kept running throughout, so no re-power/boot delay is needed. Re-assert only the
    // runtime message-output config (cheap, non-destructive) so NMEA output resumes.
    ResendRuntimeConfig();
    suspended_ = false;
}

void GNSSReceiver::SetEnable(bool enabled) {
    if (config_.enable_pin == UINT16_MAX) return;  // Not connected.
    // Active low: driving the pin low turns on the high-side power switch (module powered).
    gpio_put(config_.enable_pin, !enabled);
}

bool GNSSReceiver::HasValidFix() const {
    if (!healthy_) return false;
    const GNSSFix& f = parser_.fix();
    if (!f.valid) return false;
    return (get_time_since_boot_ms() - f.last_update_timestamp_ms) < kFixStaleTimeoutMs;
}
