#include "comms.hh"

#include <cstdarg>  // For debug printf.
#include <cstdio>   // Regular pico/stdio.h doesn't support vprint functions.

#include "pico/stdlib.h"

const char CommsManager::ConsoleVerbosityStrs[CommsManager::LogLevel::kNumVerbosityLevels]
                                             [CommsManager::kConsoleVerbosityStrMaxLen] = {"SILENT", "ERRORS",
                                                                                           "WARNINGS", "LOGS"};
const char CommsManager::SerialInterfaceStrs[CommsManager::SerialInterface::kNumSerialInterfaces]
                                            [CommsManager::kSerialInterfaceStrMaxLen] = {"CONSOLE", "COMMS_UART",
                                                                                         "GNSS_UART"};
const char CommsManager::ReportingProtocolStrs[CommsManager::ReportingProtocol::kNumProtocols]
                                              [CommsManager::kReportingProtocolStrMaxLen] = {
                                                  "NONE", "RAW", "RAW_VALIDATED", "MAVLINK1", "MAVLINK2", "GDL90"};

bool CommsManager::Init() {
    InitAT();
    InitReporting();

    gpio_set_function(config_.comms_uart_tx_pin, GPIO_FUNC_UART);
    gpio_set_function(config_.comms_uart_rx_pin, GPIO_FUNC_UART);
    uart_set_translate_crlf(config_.comms_uart_handle, false);
    uart_init(config_.comms_uart_handle, kDefaultCommsUARTBaudrate);

    gpio_set_function(config_.gnss_uart_tx_pin, GPIO_FUNC_UART);
    gpio_set_function(config_.gnss_uart_rx_pin, GPIO_FUNC_UART);
    uart_set_translate_crlf(config_.gnss_uart_handle, false);
    uart_init(config_.gnss_uart_handle, kDefaultGNSSUARTBaudrate);

    // Initialize ESP32 GPIOs.
    // Don't mess with ESP32 wifi pin until we're ready to try firmware updates.
    // gpio_init(config_.esp32_enable_pin);
    // gpio_set_dir(config_.esp32_enable_pin, GPIO_OUT);
    // gpio_put(config_.esp32_enable_pin, 0);  // Disable ESP32.

    // Don't mess with ESP32 boot pin until we're ready to try firmware updates.
    // gpio_init(config_.esp32_gpio0_boot_pin);
    // gpio_set_dir(config_.esp32_gpio0_boot_pin, GPIO_OUT);
    // gpio_put(config_.esp32_gpio0_boot_pin, 1);  // Disable ESP32 download boot mode.

    stdio_init_all();
    stdio_set_translate_crlf(&stdio_usb, false);

    return true;
}

bool CommsManager::Update() {
    UpdateAT();
    UpdateReporting();
    return true;
}

int CommsManager::console_printf(const char *format, ...) {
    if (console_verbosity == kSilent) return 0;
    va_list args;
    va_start(args, format);
    int res = vprintf(format, args);
    va_end(args);
    return res;
}

int CommsManager::console_level_printf(LogLevel level, const char *format, ...) {
    if (console_verbosity < level) return 0;
    va_list args;
    va_start(args, format);
    int res = vprintf(format, args);
    va_end(args);
    return res;
}

int CommsManager::iface_printf(SerialInterface iface, const char *format, ...) {
    char buf[kPrintfBufferMaxSize];
    va_list args;
    va_start(args, format);
    int res = vsnprintf(buf, kPrintfBufferMaxSize, format, args);
    va_end(args);
    if (res <= 0) {
        return res;  // vsnprintf failed.
    }
    if (iface_puts(iface, buf)) {
        return res;  // Return number of characters written.
    }

    return -1;  // puts failed.
}

bool CommsManager::iface_putc(SerialInterface iface, char c) {
    switch (iface) {
        case kCommsUART:
            uart_putc_raw(config_.comms_uart_handle, c);
            return true;  // Function is void so we won't know if it succeeds.
            break;
        case kGNSSUART:
            uart_putc_raw(config_.gnss_uart_handle, c);
            return true;  // Function is void so we won't know if it succeeds.
            break;
        case kConsole:
            return putchar(c) >= 0;
            break;
        case kNumSerialInterfaces:
        default:
            CONSOLE_WARNING("CommsManager::iface_putc: Unrecognized iface %d.", iface);
            return false;
    }
    return false;  // Should never get here.
}

bool CommsManager::iface_getc(SerialInterface iface, char &c) {
    switch (iface) {
        case kCommsUART:
            if (uart_is_readable_within_us(config_.comms_uart_handle, config_.uart_timeout_us)) {
                c = uart_getc(config_.comms_uart_handle);
                return true;
            }
            return false;  // No chars to read.
            break;
        case kGNSSUART:
            if (uart_is_readable_within_us(config_.gnss_uart_handle, config_.uart_timeout_us)) {
                c = uart_getc(config_.gnss_uart_handle);
                return true;
            }
            return false;  // No chars to read.
            break;
        case kConsole: {
            int ret = getchar_timeout_us(config_.uart_timeout_us);
            if (ret >= 0) {
                c = (char)ret;
                return true;
            }
            return false;  // Failed to read character.
            break;
        }
        case kNumSerialInterfaces:
        default:
            CONSOLE_WARNING("CommsManager::iface_getc: Unrecognized iface %d.", iface);
            return false;  // Didn't match an interface.
            break;
    }
    return false;  // Should never get here.
}

bool CommsManager::iface_puts(SerialInterface iface, const char *buf) {
    switch (iface) {
        case kCommsUART:
            uart_puts(config_.comms_uart_handle, buf);
            return true;  // Function is void so we won't know if it succeeds.
            break;
        case kGNSSUART:
            uart_puts(config_.gnss_uart_handle, buf);
            return true;  // Function is void so we won't know if it succeeds.
            break;
        case kConsole:
            return puts(buf) >= 0;
            break;
        case kNumSerialInterfaces:
        default:
            CONSOLE_WARNING("CommsManager::iface_puts: Unrecognized iface %d.", iface);
            return false;  // Didn't match an interface.
            break;
    }
    return false;  // Should never get here.
}

bool CommsManager::SetWiFiEnabled(bool new_wifi_enabled) {
    if (new_wifi_enabled != wifi_enabled_) {
        // if (new_wifi_enabled) {
        //     CONSOLE_PRINTF("Enabling WiFi...\r\n");
        //     gpio_put(config_.esp32_enable_pin, 1);
        // } else {
        //     CONSOLE_PRINTF("Disabling WiFi...\r\n");
        //     gpio_put(config_.esp32_enable_pin, 0);
        // }
        wifi_enabled_ = new_wifi_enabled;
    }

    return true;
}