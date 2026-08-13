#include "comms.hh"

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "hal.hh"

/* clang-format off */
#include <ti/devices/DeviceFamily.h>
#include DeviceFamily_constructPath(inc/hw_memmap.h)
#include DeviceFamily_constructPath(driverlib/uart.h)
/* clang-format on */

static const CommsManager::ReportSink kReportingSinks[] = {SettingsManager::SerialInterface::kConsole};
static const uint16_t kNumReportingSinks = sizeof(kReportingSinks) / sizeof(CommsManager::ReportSink);

CommsManager::CommsManager(CommsManagerConfig config)
    : config_(config), at_parser_(CppAT(at_command_list, at_command_list_num_commands, true)) {}

void CommsManager::uart_write_callback(UART2_Handle handle, void* buf, size_t count, void* userArg,
                                       int_fast16_t status) {
    static_cast<CommsManager*>(userArg)->uart_tx_busy_ = false;
}

bool CommsManager::OpenUART(uint32_t baud) {
    UART2_Params uart_params;
    UART2_Params_init(&uart_params);
    uart_params.baudRate = baud;
    uart_params.writeMode = UART2_Mode_CALLBACK;
    uart_params.writeCallback = uart_write_callback;
    uart_params.userArg = this;
    uart_handle_ = UART2_open(config_.uart_index, &uart_params);
    if (uart_handle_ == NULL) {
        return false;
    }
    UART2_rxEnable(uart_handle_);
    return true;
}

bool CommsManager::Init() {
    if (!OpenUART(config_.uart_baud_rate)) {
        while (1);
    }
    return true;
}

bool CommsManager::SetBaudRate(uint32_t baud) {
    if (!IsAllowedBaudRate(baud)) {
        return false;
    }
    if (baud == config_.uart_baud_rate) {
        return true;
    }

    // Let any queued response (e.g. the "OK" for AT+BAUD_RATE) reach the host intact at the old baud
    // before the line reconfigures.
    DrainConsoleTx();

    UART2_close(uart_handle_);
    uart_tx_busy_ = false;  // The write callback will not fire after close.
    config_.uart_baud_rate = baud;
    if (!OpenUART(baud)) {
        // Deterministic params make reopen failure effectively impossible, but fall back to the
        // boot default rather than hanging the console.
        config_.uart_baud_rate = SettingsManager::Settings::kDefaultUARTBaudRate;
        if (!OpenUART(config_.uart_baud_rate)) {
            while (1);
        }
    }
    // Discard any garbage clocked in at the mismatched rate (e.g. a trailing newline from the host).
    UART2_flushRx(uart_handle_);

    // Mirror the live value so settings queries display it; AT+SETTINGS=SAVE persists it and
    // SettingsManager::Apply() re-applies it at boot.
    settings_manager.settings.baud_rates[SettingsManager::SerialInterface::kConsole] = config_.uart_baud_rate;
    return baud == config_.uart_baud_rate;
}

bool CommsManager::DrainConsoleTx(uint32_t timeout_ms) {
    // Each stage gets its own budget rather than sharing one deadline: the stages wait on unrelated
    // events, and a slow first stage must not starve the second. The hardware stage is the one that
    // matters for STANDBY (it gates the UART's power constraint), so it is exactly the one that must
    // not be skipped after a long DMA wait.

    // Software side: wait for the in-flight CALLBACK-mode write (if any) to complete. Worst pending
    // chunk is kPrintfBufferMaxSize (1000 B), ~87 ms at 115200.
    uint32_t deadline_ms = get_time_since_boot_ms() + timeout_ms;
    while (uart_tx_busy_ && get_time_since_boot_ms() < deadline_ms) {
    }
    // Hardware side: the write callback fires on DMA completion, not when the bytes have left the
    // wire — up to a FIFO's worth can still be in flight. UARTBusy() stays set until the last stop
    // bit is shifted out.
    deadline_ms = get_time_since_boot_ms() + timeout_ms;
    while (UARTBusy(UART0_BASE) && get_time_since_boot_ms() < deadline_ms) {
    }
    return !uart_tx_busy_ && !UARTBusy(UART0_BASE);
}

bool CommsManager::Suspend() {
    // Release the PowerCC26XX_DISALLOW_STANDBY constraint that UART2_rxEnable() holds while RX is on,
    // so the MCU can reach STANDBY. TX is left intact so console logging still flushes before sleep.
    UART2_rxDisable(uart_handle_);
    return true;
}

bool CommsManager::Resume() {
    // Re-arm console UART reception after wake.
    UART2_rxEnable(uart_handle_);
    return true;
}

bool CommsManager::Update() {
    UpdateAT();

    uint32_t timestamp_ms = get_time_since_boot_ms();
    if (timestamp_ms - last_raw_report_check_timestamp_ms_ > kRawReportingCheckIntervalMs) {
        last_raw_report_check_timestamp_ms_ = timestamp_ms;  // Proceed with update and record timestamp.

        // Calculate how much buffer space the current packets would need.
        uint16_t required_buffer_len = CompositeArray::CalculateRawPacketsBufferLength(
            &mode_s_packet_reporting_queue, &uat_adsb_packet_reporting_queue, &uat_uplink_packet_reporting_queue);

        // Only forward packets if buffer would be full or if max reporting interval has elapsed.
        bool buffer_would_be_full = required_buffer_len >= CompositeArray::RawPackets::kMaxLenBytes;
        bool max_interval_elapsed = (timestamp_ms - last_raw_report_timestamp_ms_) >= kRawReportingMaxIntervalMs;

        if (buffer_would_be_full || max_interval_elapsed) {
            // Update the last report timestamp now that we're actually sending packets.
            last_raw_report_timestamp_ms_ = timestamp_ms;

            // Don't deplete the packet queues until we are ready to report!
            uint8_t packets_to_report_buf[CompositeArray::RawPackets::kMaxLenBytes] = {0};
            CompositeArray::RawPackets packets_to_report = CompositeArray::PackRawPacketsBuffer(
                packets_to_report_buf, sizeof(packets_to_report_buf), &mode_s_packet_reporting_queue,
                &uat_adsb_packet_reporting_queue, &uat_uplink_packet_reporting_queue);

            // Interfaces to send reports on.
            UpdateReporting(kReportingSinks, settings_manager.settings.reporting_protocols, kNumReportingSinks,
                            &packets_to_report);
        }
    }
    return true;
}

int CommsManager::console_printf(const char* format, ...) {
    va_list args;
    va_start(args, format);
    int res = console_vprintf(format, args);
    va_end(args);
    return res;
}

int CommsManager::console_level_printf(SettingsManager::LogLevel level, const char* format, ...) {
    if (settings_manager.settings.log_level < level) return 0;
    va_list args;
    va_start(args, format);
    int res = console_vprintf(format, args);
    va_end(args);
    return res;
}

// int CommsManager::console_printf(const char* fmt, ...) {
//     char string[255];
//     va_list args;
//     va_start(args, fmt);
//     uint16_t len = vsprintf(string, fmt, args);
//     va_end(args);
//     uint16_t len_written = UART2_write(uart_handle_, string, len);
//     return len_written;
// }

int CommsManager::console_vprintf(const char* fmt, va_list args) {
    char buf[kPrintfBufferMaxSize];
    int len = vsnprintf(buf, kPrintfBufferMaxSize, fmt, args);
    if (len <= 0) return len;
    return iface_puts(SettingsManager::SerialInterface::kConsole, buf, /*blocking=*/true) ? len : -1;
}

int CommsManager::iface_printf(SettingsManager::SerialInterface iface, const char* format, ...) {
    va_list args;
    va_start(args, format);
    int res = iface_vprintf(iface, format, args);
    va_end(args);
    return res;
}

int CommsManager::iface_vprintf(SettingsManager::SerialInterface iface, const char* format, va_list args) {
    char buf[kPrintfBufferMaxSize];

    // Formatted print to buffer.
    int res = vsnprintf(buf, kPrintfBufferMaxSize, format, args);
    if (res <= 0) {
        return res;  // vsnprintf failed.
    }
    // Send buffer to interface, then manually push messages (otherwise they only pop out when the buffer gets full).
    if (iface_puts(iface, buf)) {
        return res;  // Return number of characters written.
    }

    return -1;  // puts failed.
}

bool CommsManager::iface_write(SettingsManager::SerialInterface iface, const void* buf, size_t len, bool blocking) {
    switch (iface) {
        case SettingsManager::kConsole: {
            // Send in chunks no larger than the single static TX buffer. Reporting batches can exceed
            // kPrintfBufferMaxSize under heavy load; chunking lets the whole batch through instead of
            // dropping it. The per-chunk busy-wait gates reuse of uart_tx_buf_ until the previous
            // chunk's write callback fires.
            const uint8_t* p = static_cast<const uint8_t*>(buf);
            size_t remaining = len;
            bool ok = true;
            while (remaining > 0) {
                size_t chunk = remaining > kPrintfBufferMaxSize ? kPrintfBufferMaxSize : remaining;
                while (uart_tx_busy_) {
                }
                memcpy(uart_tx_buf_, p, chunk);
                uart_tx_busy_ = true;
                int_fast16_t status = UART2_write(uart_handle_, uart_tx_buf_, chunk, nullptr);
                ok &= (status == UART2_STATUS_SUCCESS);
                p += chunk;
                remaining -= chunk;
            }
            if (blocking) {
                while (uart_tx_busy_) {
                }
            }
            return ok;
        }
        case SettingsManager::kNumSerialInterfaces:
        default:
            CONSOLE_WARNING("CommsManager::iface_write", "Unrecognized iface %d.", iface);
            return false;
    }
    return false;
}

bool CommsManager::iface_putc(SettingsManager::SerialInterface iface, char c, bool blocking) {
    return iface_write(iface, &c, 1, blocking);
}

bool CommsManager::iface_getc(SettingsManager::SerialInterface iface, char& c) {
    switch (iface) {
        // case SettingsManager::kCommsUART:
        //     if (uart_is_readable_within_us(config_.comms_uart_handle, config_.uart_timeout_us)) {
        //         c = uart_getc(config_.comms_uart_handle);
        //         return true;
        //     }
        //     return false;  // No chars to read.
        //     break;
        // case SettingsManager::kGNSSUART:
        //     if (uart_is_readable_within_us(config_.gnss_uart_handle, config_.uart_timeout_us)) {
        //         c = uart_getc(config_.gnss_uart_handle);
        //         return true;
        //     }
        //     return false;  // No chars to read.
        //     break;
        case SettingsManager::kConsole: {
            if (UART2_getRxCount(uart_handle_) == 0) {
                return false;  // No chars to read.
            }
            size_t bytes_read;
            int_fast16_t status = UART2_read(uart_handle_, &c, 1, &bytes_read);
            if (status == UART2_STATUS_SUCCESS && bytes_read == 1) {
                return true;
            }
            return false;  // Failed to read character.
            break;
        }
        case SettingsManager::kNumSerialInterfaces:
        default:
            CONSOLE_WARNING("CommsManager::iface_getc", "Unrecognized iface %d.", iface);
            return false;  // Didn't match an interface.
            break;
    }
    return false;  // Should never get here.
}

bool CommsManager::iface_puts(SettingsManager::SerialInterface iface, const char* buf, bool blocking) {
    return iface_write(iface, buf, strlen(buf), blocking);
}