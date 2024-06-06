#include "comms.hh"

#include <cstdarg>  // For debug printf.
#include <cstdio>   // Regular pico/stdio.h doesn't support vprint functions.

#include "pico/stdlib.h"

const char CommsManager::SerialInterfaceStrs[CommsManager::SerialInterface::kNumSerialInterfaces]
                                            [CommsManager::kSerialInterfaceStrMaxLen] = {"CONSOLE", "COMMS_UART",
                                                                                         "GNSS_UART"};
const char CommsManager::ReportingProtocolStrs[CommsManager::ReportingProtocol::kNumProtocols]
                                              [CommsManager::kReportingProtocolStrMaxLen] = {
                                                  "NONE", "RAW", "RAW_VALIDATED", "MAVLINK", "GDL90"};

bool CommsManager::Init() {
    InitAT();

    gpio_set_function(config_.comms_uart_tx_pin, GPIO_FUNC_UART);
    gpio_set_function(config_.comms_uart_rx_pin, GPIO_FUNC_UART);
    uart_set_translate_crlf(config_.comms_uart_handle, false);
    uart_init(config_.comms_uart_handle, kDefaultCommsUARTBaudrate);

    gpio_set_function(config_.gnss_uart_tx_pin, GPIO_FUNC_UART);
    gpio_set_function(config_.gnss_uart_rx_pin, GPIO_FUNC_UART);
    uart_set_translate_crlf(config_.gnss_uart_handle, false);
    uart_init(config_.gnss_uart_handle, kDefaultGNSSUARTBaudrate);

    stdio_init_all();
    stdio_set_translate_crlf(&stdio_usb, false);

    return true;
}

bool CommsManager::Update() {
    UpdateAT();
    return true;
}

int CommsManager::console_printf(const char *format, ...) {
    if (at_config_mode_ == ATConfigMode::kConfig) return 0;
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
            CONSOLE_PRINTF("CommsManager::iface_putc: Unrecognized iface %d.\r\n", iface);
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
            CONSOLE_PRINTF("CommsManager::iface_getc: Unrecognized iface %d.\r\n", iface);
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
            CONSOLE_PRINTF("CommsManager::iface_puts: Unrecognized iface %d.\r\n", iface);
            return false;  // Didn't match an interface.
            break;
    }
    return false;  // Should never get here.
}