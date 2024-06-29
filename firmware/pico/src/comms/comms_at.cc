#include <stdio.h>  // for printing

#include <cstring>   // for strcat
#include <iostream>  // for AT command ingestion

#include "ads_bee.hh"
#include "comms.hh"
#include "eeprom.hh"
#include "main.hh"
#include "pico/stdlib.h"  // for getchar etc
#include "settings.hh"

#ifdef HARDWARE_UNIT_TESTS
#include "hardware_unit_tests.hh"
#endif

// For mapping cpp_at_printf
#include <cstdarg>
// #include "printf.h" // for using custom printf defined in printf.h
#include <cstdio>  // for using regular printf

/** CppAT Printf Override **/
int CppAT::cpp_at_printf(const char *format, ...) {
    va_list args;
    va_start(args, format);
    int res = vprintf(format, args);
    va_end(args);
    return res;
}

/** AT Command Callback Functions **/

CPP_AT_CALLBACK(CommsManager::ATBaudrateCallback) {
    switch (op) {
        case '?':
            CPP_AT_CMD_PRINTF("=%d(COMMS),%d(GNSS)", comms_uart_baudrate_, gnss_uart_baudrate_);
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            if (!(CPP_AT_HAS_ARG(0) && CPP_AT_HAS_ARG(1))) {
                CPP_AT_ERROR(
                    "Requires two arguments: AT+BAUDRATE=<iface>,<baudrate> where <iface> can be one of [COMMS, "
                    "GNSS].");
            }
            SerialInterface iface;
            if (args[0].compare("COMMS") == 0) {
                iface = kCommsUART;
            } else if (args[0].compare("GNSS") == 0) {
                iface = kGNSSUART;
            } else {
                CPP_AT_ERROR("Invalid interface. Must be one of [COMMS, GNSS].");
            }
            uint32_t baudrate;
            CPP_AT_TRY_ARG2NUM(1, baudrate);
            if (!SetBaudrate(iface, baudrate)) {
                CPP_AT_ERROR("Unable to set baudrate %d on interface %d.", baudrate, iface);
            }
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR();  // Should never get here.
}

CPP_AT_CALLBACK(CommsManager::ATConsoleVerbosityCallback) {
    switch (op) {
        case '?':
            // AT+CONFIG mode query.
            CPP_AT_CMD_PRINTF("=%s", ConsoleVerbosityStrs[console_verbosity]);
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // AT+CONFIG set command.
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Need to specify a config mode to run.");
            }
            for (uint16_t i = 0; i < kNumVerbosityLevels; i++) {
                if (args[0].compare(ConsoleVerbosityStrs[i]) == 0) {
                    console_verbosity = static_cast<LogLevel>(i);
                    CPP_AT_SUCCESS();
                }
            }
            CPP_AT_ERROR("Verbosity level %s not recognized.", args[0].data());
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATProtocolCallback) {
    switch (op) {
        case '?':
            // Print out reporting protocols for CONSOLE and COMMS_UART.
            for (uint16_t iface = 0; iface < SerialInterface::kGNSSUART; iface++) {
                CPP_AT_CMD_PRINTF("=%s,%s", SerialInterfaceStrs[iface],
                                  ReportingProtocolStrs[reporting_protocols_[iface]]);
            }
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // Set the reporting protocol for a given interface.
            if (!(CPP_AT_HAS_ARG(0) && CPP_AT_HAS_ARG(1))) {
                CPP_AT_ERROR("Requires two arguments: AT+PROTOCOL=<iface>,<protocol>.");
            }

            // Match the selected serial interface. Don't allow selection of the GNSS interface.
            SerialInterface selected_iface = SerialInterface::kNumSerialInterfaces;
            for (uint16_t iface = 0; iface < SerialInterface::kGNSSUART; iface++) {
                if (args[0].compare(SerialInterfaceStrs[iface]) == 0) {
                    selected_iface = static_cast<SerialInterface>(iface);
                    break;
                }
            }
            if (selected_iface == kNumSerialInterfaces) {
                CPP_AT_ERROR("Invalid serial interface %s.", args[0].data());
            }

            // Match the selected protocol.
            ReportingProtocol selected_protocol = ReportingProtocol::kNumProtocols;
            for (uint16_t protocol = 0; protocol < ReportingProtocol::kNumProtocols; protocol++) {
                if (args[1].compare(ReportingProtocolStrs[protocol]) == 0) {
                    selected_protocol = static_cast<ReportingProtocol>(protocol);
                    break;
                }
            }
            if (selected_protocol == kNumProtocols) {
                CPP_AT_ERROR("Invalid reporting protocol %s.", args[1].data());
            }

            // Assign the selected protocol to the selected interface.
            reporting_protocols_[selected_iface] = selected_protocol;
            CPP_AT_SUCCESS();
            break;
    }

    CPP_AT_ERROR();  // Should never get here.
}

CPP_AT_HELP_CALLBACK(CommsManager::ATProtocolHelpCallback) {
    CPP_AT_PRINTF("\tSet the reporting protocol used on a given serial interface:\r\n");
    CPP_AT_PRINTF("\tAT+PROTOCOL=<iface>,<protocol>\r\n\t<iface> = ");
    for (uint16_t iface = 0; iface < kGNSSUART; iface++) {
        CPP_AT_PRINTF("%s ", SerialInterfaceStrs[iface]);
    }
    CPP_AT_PRINTF("\r\n\t<protocol> = ");
    for (uint16_t protocol = 0; protocol < kNumProtocols; protocol++) {
        CPP_AT_PRINTF("%s ", ReportingProtocolStrs[protocol]);
    }
    CPP_AT_PRINTF("\r\n\tQuery the reporting protocol used on all interfaces:\r\n");
    CPP_AT_PRINTF("\tAT+PROTOCOL?\r\n\t+PROTOCOL=<iface>,<protocol>\r\n\t...\r\n");
}

CPP_AT_CALLBACK(CommsManager::ATRxGainCallback) {
    switch (op) {
        case '=':
            if (CPP_AT_HAS_ARG(0)) {
                int rx_gain;
                CPP_AT_TRY_ARG2NUM(0, rx_gain);
                if (!ads_bee.SetRxGain(rx_gain)) {
                    CPP_AT_ERROR("Failed while setting rx gain to %d.", rx_gain);
                }
                CPP_AT_SUCCESS();
            }
            CPP_AT_ERROR("Received operator '%c' but no args.", op);
            break;
        case '?':
            CPP_AT_CMD_PRINTF("=%d(%d)", ads_bee.GetRxGain(), ads_bee.ReadRxGain());
            CPP_AT_SILENT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATSettingsCallback) {
    switch (op) {
        case '=':
            // Note: Don't allow settings modification from here, do it directly through other commands.
            if (CPP_AT_HAS_ARG(0)) {
                if (args[0].compare("SAVE") == 0) {
                    if (!settings_manager.Save()) {
                        CPP_AT_ERROR("Error while writing to EEPROM.");
                    }
                } else if (args[0].compare("LOAD") == 0) {
                    if (!settings_manager.Load()) {
                        CPP_AT_ERROR("Error while reading from EEPROM.");
                    }
                } else if (args[0].compare("RESET") == 0) {
                    settings_manager.ResetToDefaults();
                }
                CPP_AT_SUCCESS();
            }
            CPP_AT_ERROR("No arguments provided.");
            break;
        case '?':
            CPP_AT_CMD_PRINTF("=%d(tl_lo_mv),%d(tl_hi_mv),%d(rx_gain)\r\n", settings_manager.settings.tl_lo_mv,
                              settings_manager.settings.tl_hi_mv, settings_manager.settings.rx_gain);
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATTLReadCallback) {
    switch (op) {
        case '?':
            // Read command.
            CPP_AT_CMD_PRINTF("=%d,%d\r\n", ads_bee.ReadTLLoMilliVolts(), ads_bee.ReadTLHiMilliVolts());
            CPP_AT_SILENT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

/**
 * AT+TL_SET Callback
 * AT+TL_SET=<mtl_lo_mv>,<mtl_hi_mv>
 *  mtl_lo_mv = Low trigger value, mV.
 *  mtl_hi_mv = High trigger value, mV.
 * AT+TL_SET?
 * +TL_SET=
 */
CPP_AT_CALLBACK(CommsManager::ATTLSetCallback) {
    switch (op) {
        case '?':
            // AT+TL_SET value query.
            CPP_AT_CMD_PRINTF("=%d,%d\r\n", ads_bee.GetTLLoMilliVolts(), ads_bee.GetTLHiMilliVolts());
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // Attempt setting LO TL value, in milliVolts, if first argument is not blank.
            if (CPP_AT_HAS_ARG(0)) {
                uint16_t new_mtl_lo_mv;
                CPP_AT_TRY_ARG2NUM(0, new_mtl_lo_mv);
                if (!ads_bee.SetTLLoMilliVolts(new_mtl_lo_mv)) {
                    CPP_AT_ERROR("Failed to set mtl_lo_mv.");
                }
            }
            // Attempt setting HI TL value, in milliVolts, if second argument is not blank.
            if (CPP_AT_HAS_ARG(1)) {
                // Set HI TL value, in milliVolts.
                uint16_t new_mtl_hi_mv;
                CPP_AT_TRY_ARG2NUM(1, new_mtl_hi_mv);
                if (!ads_bee.SetTLHiMilliVolts(new_mtl_hi_mv)) {
                    CPP_AT_ERROR("Failed to set mtl_hi_mv.");
                }
            }
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

/**
 * Takes a password as a string and fills a buffer with the corresponding number of asterix.
 * @param[in] password_buf Buffer to read the password from. Must be at least password_len+1 chars.
 * @param[out] redacted_password_buf Buffer to write the asterix to. Must be at least password_len+1 chars.
 * @param[in] buf_len Maximum allowable number of characteers in the password. Used to guard against falling off the end
 * of the string. Not used for actually finding ther number of asterix to print.
 */
void redact_password(char *password_buf, char *redacted_password_buf, uint16_t buf_len) {
    uint16_t password_len = MIN(strlen(password_buf), buf_len);
    memset(redacted_password_buf, '*', password_len);
    redacted_password_buf[password_len] = '\0';
}

CPP_AT_CALLBACK(CommsManager::ATWiFiCallback) {
    switch (op) {
        case '?': {
            char redacted_password[kWiFiPasswordMaxLen + 1];
            redact_password(wifi_password, redacted_password, kWiFiPasswordMaxLen);
            CPP_AT_CMD_PRINTF("=%d,%s,%s\r\n", static_cast<uint16_t>(wifi_enabled_), wifi_ssid, redacted_password);
            CPP_AT_SILENT_SUCCESS();
            break;
        }
        case '=': {
            if (CPP_AT_HAS_ARG(0)) {
                bool new_wifi_enabled = false;
                CPP_AT_TRY_ARG2NUM(0, new_wifi_enabled);
                if (CPP_AT_HAS_ARG(1)) {
                    strncpy(wifi_ssid, args[1].data(), kWiFiSSIDMaxLen);
                    wifi_ssid[kWiFiSSIDMaxLen] = '\0';
                    CPP_AT_CMD_PRINTF(": ssid=%s\r\n", wifi_ssid);
                }
                if (CPP_AT_HAS_ARG(2)) {
                    strncpy(wifi_password, args[2].data(), kWiFiPasswordMaxLen);
                    wifi_password[kWiFiPasswordMaxLen] = '\0';
                    char redacted_password[kWiFiPasswordMaxLen];
                    redact_password(wifi_password, redacted_password, kWiFiPasswordMaxLen);
                    CPP_AT_CMD_PRINTF(": password=%s\r\n", redacted_password);
                }

                if (SetWiFiEnabled(new_wifi_enabled)) {
                    CPP_AT_SUCCESS();
                } else {
                    CPP_AT_ERROR("Seting wifi_enabled=%d failed.", new_wifi_enabled);
                }
                break;
            }
        }
        default: {
            CPP_AT_ERROR("Operator %c not supported.", op);
        }
    }
    CPP_AT_ERROR();  // Should never get here.
}

static const CppAT::ATCommandDef_t at_command_list[] = {
    {.command_buf = "+BAUDRATE",
     .min_args = 0,
     .max_args = 2,
     .help_string_buf = "AT+BAUDRATE=<iface>,<baudrate>\r\n\tSet the baud rate of a serial "
                        "interface.\r\n\tAT+BAUDRATE=COMMS,115200\r\n\tAT+BAUDRATE=GNSS,9600\r\n\tAT_BAUDRATE?",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATBaudrateCallback, comms_manager)},
    {.command_buf = "+LOG_LEVEL",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "AT+LOG_LEVEL=<console_verbosity>\r\n\tSet how much stuff gets printed to the "
                        "console.\r\n\tconsole_verbosity = [SILENT ERRORS WARNINGS LOGS]",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATConsoleVerbosityCallback, comms_manager)},
    {.command_buf = "+PROTOCOL",
     .min_args = 0,
     .max_args = 2,
     .help_callback = CPP_AT_BIND_MEMBER_HELP_CALLBACK(CommsManager::ATProtocolHelpCallback, comms_manager),
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATProtocolCallback, comms_manager)},
    {.command_buf = "+RX_GAIN",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "Set value of Rx Gain Digipot.\r\n\t"
                        "AT+RX_GAIN=<rx_gain>\r\n\tAT+RX_GAIN?\r\n\t+RX_GAIN=<rx_gain>.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATRxGainCallback, comms_manager)

    },
    {.command_buf = "+SETTINGS",
     .min_args = 0,
     .max_args = 3,
     .help_string_buf = "Load or save nonvolatile settings.\r\n\tAT+SETTINGS=<op>\r\n\t<op> = LOAD SAVE\r\n"
                        "\tDisplay nonvolatile settings.\r\n\tAT+SETTINGS?\r\n\t+SETTINGS=...\r\n\t",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATSettingsCallback, comms_manager)},
#ifdef HARDWARE_UNIT_TESTS
    {.command_buf = "+TEST",
     .min_args = 0,
     .max_args = 0,
     .help_string_buf = "Run hardware self-tests.",
     .callback = ATTestCallback},
#endif
    {.command_buf = "+TL_READ",
     .min_args = 0,
     .max_args = 0,
     .help_string_buf = "Read ADC counts and mV values for high and low TL thresholds. Call with no ops nor arguments, "
                        "AT+TL_READ.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATTLReadCallback, comms_manager)},
    {.command_buf = "+TL_SET",
     .min_args = 0,
     .max_args = 2,
     .help_string_buf =
         "Set HI and LO trigger level thresholds for RF power detector.\r\n\tAT+TLSet=<tl_lo_mv_>,<tl_hi_mv_>"
         "\tQuery trigger level.\r\n\tAT+TL_SET?\r\n\t+TLSet=<tl_lo_mv_>,<tl_hi_mv_>.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATTLSetCallback, comms_manager)},
    {.command_buf = "+WIFI",
     .min_args = 0,
     .max_args = 3,
     .help_string_buf = "Set WiFi parameters.\r\n\tAT+WIFI=<enabled[0 1]>,<ssid[str]>,<password[str]>\r\n\t"
                        "Get WiFi parameters.\r\n\tAT+WIFI?\r\n\t+WIFI=<enabled[0 1]>,<ssid[str]>,<***[str]>",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATWiFiCallback, comms_manager)},
};

CommsManager::CommsManager(CommsManagerConfig config_in)
    : config_(config_in),
      at_parser_(CppAT(at_command_list, sizeof(at_command_list) / sizeof(at_command_list[0]), true)) {}

bool CommsManager::InitAT() {
    // Initialize AT command parser with statically allocated list of AT commands.

    return true;
}

bool CommsManager::UpdateAT() {
    static char at_command_buf[kATCommandBufMaxLen];
    // Check for new AT commands. Process up to one line per loop.
    int c = getchar_timeout_us(0);
    while (c != PICO_ERROR_TIMEOUT) {
        char buf[2] = {static_cast<char>(c), '\0'};
        strcat(at_command_buf, buf);
        if (c == '\n') {
            at_parser_.ParseMessage(std::string_view(at_command_buf));
            at_command_buf[0] = '\0';  // clear command buffer
        }
        c = getchar_timeout_us(0);
    }
    return true;
}