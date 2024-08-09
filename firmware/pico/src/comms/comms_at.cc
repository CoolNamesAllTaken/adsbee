#include <stdio.h>  // for printing

#include <cstring>   // for strcat
#include <iostream>  // for AT command ingestion

#include "ads_bee.hh"
#include "comms.hh"
#include "eeprom.hh"
#include "esp32_flasher.hh"
#include "main.hh"
#include "pico/stdlib.h"  // for getchar etc
#include "settings.hh"
#include "spi_coprocessor.hh"  // For init / de-init before and after flashing ESP32.

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
            SettingsManager::SerialInterface iface;
            if (args[0].compare("COMMS") == 0) {
                iface = SettingsManager::kCommsUART;
            } else if (args[0].compare("GNSS") == 0) {
                iface = SettingsManager::kGNSSUART;
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

CPP_AT_CALLBACK(CommsManager::ATLogLevelCallback) {
    switch (op) {
        case '?':
            // AT+CONFIG mode query.
            CPP_AT_CMD_PRINTF("=%s", SettingsManager::ConsoleLogLevelStrs[log_level]);
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // AT+CONFIG set command.
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Need to specify a config mode to run.");
            }
            for (uint16_t i = 0; i < SettingsManager::kNumLogLevels; i++) {
                if (args[0].compare(SettingsManager::ConsoleLogLevelStrs[i]) == 0) {
                    log_level = static_cast<SettingsManager::LogLevel>(i);
                    CPP_AT_SUCCESS();
                }
            }
            CPP_AT_ERROR("Verbosity level %s not recognized.", args[0].data());
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

void ATFeedHelpCallback() {
    CPP_AT_PRINTF(
        "AT+FEED=<feed_index>,<feed_uri>,<feed_port>,<active>,<protocol>\r\n\tSet details for a "
        "network feed.\r\n\tfeed_index = [0-%d], feed_uri = ip address or URL, feed_port = [0-65535], "
        "active = [0 1], protocol = [BEAST].\r\n\t\r\n\tAT+FEED?\r\n\tPrint details for all "
        "feeds.\r\n\t\r\n\tAT+FEED?<feed_index>\r\n\tPrint details for a specific feed.\r\n\tfeed_index = [0-%d]",
        SettingsManager::kMaxNumFeeds - 1, SettingsManager::kMaxNumFeeds - 1);
}

CPP_AT_CALLBACK(CommsManager::ATFeedCallback) {
    switch (op) {
        case '?':
            if (CPP_AT_HAS_ARG(0)) {
                // Querying info about a specific feed.
                uint16_t feed_index = UINT16_MAX;
                CPP_AT_TRY_ARG2NUM(0, feed_index);
                if (feed_index >= SettingsManager::kMaxNumFeeds) {
                    CPP_AT_ERROR("Feed number must be between 0-%d, no details for feed with index %d.",
                                 SettingsManager::kMaxNumFeeds - 1, feed_index);
                }
                CPP_AT_CMD_PRINTF(
                    "=%d(FEED_INDEX),%s(FEED_URI),%d(FEED_PORT),%d(ACTIVE),%s(PROTOCOL)", feed_index,
                    settings_manager.settings.feed_uris[feed_index], settings_manager.settings.feed_ports[feed_index],
                    settings_manager.settings.feed_is_active[feed_index],
                    SettingsManager::ReportingProtocolStrs[settings_manager.settings.feed_protocols[feed_index]]);
            } else {
                // Querying info about all feeds.
                for (uint16_t i = 0; i < SettingsManager::kMaxNumFeeds; i++) {
                    CPP_AT_CMD_PRINTF(
                        "=%d(FEED_INDEX),%s(FEED_URI),%d(FEED_PORT),%d(ACTIVE),%s(PROTOCOL)", i,
                        settings_manager.settings.feed_uris[i], settings_manager.settings.feed_ports[i],
                        settings_manager.settings.feed_is_active[i],
                        SettingsManager::ReportingProtocolStrs[settings_manager.settings.feed_protocols[i]]);
                }
            }
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // Setting feed information for a specific feed.
            uint16_t feed_index = UINT16_MAX;
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Feed index is required for setting feed information.");
            }
            CPP_AT_TRY_ARG2NUM(0, feed_index);
            if (feed_index >= SettingsManager::kMaxNumFeeds) {
                CPP_AT_ERROR("Feed index must be between 0-%d, no details for feed with index %d.",
                             SettingsManager::kMaxNumFeeds - 1, feed_index);
            }
            // Set FEED_URI.
            if (CPP_AT_HAS_ARG(1)) {
                strncpy(settings_manager.settings.feed_uris[feed_index], args[1].data(),
                        SettingsManager::kFeedURIMaxNumChars);
                settings_manager.settings.feed_uris[feed_index][SettingsManager::kFeedURIMaxNumChars] = '\0';
            }
            // Set FEED_PORT
            if (CPP_AT_HAS_ARG(2)) {
                CPP_AT_TRY_ARG2NUM(2, settings_manager.settings.feed_ports[feed_index]);
            }
            // Set ACTIVE
            if (CPP_AT_HAS_ARG(3)) {
                uint8_t is_active;
                CPP_AT_TRY_ARG2NUM(3, settings_manager.settings.feed_is_active[feed_index]);
            }
            // Set PROTOCOL
            if (CPP_AT_HAS_ARG(4)) {
                SettingsManager::ReportingProtocol feed_protocol;
                for (uint16_t i = 0; i < SettingsManager::ReportingProtocol::kNumProtocols; i++) {
                    if (args[4].compare(SettingsManager::ReportingProtocolStrs[i]) == 0) {
                        feed_protocol = static_cast<SettingsManager::ReportingProtocol>(i);
                    }
                }
                // Check that the selected prototcol is valid for use with feeders.
                if (!(feed_protocol == SettingsManager::ReportingProtocol::kBeast ||
                      feed_protocol == SettingsManager::ReportingProtocol::kNoReports)) {
                    CPP_AT_ERROR("Protocol %s is not supported for network feeds.",
                                 SettingsManager::ReportingProtocolStrs[feed_protocol]);
                }
                settings_manager.settings.feed_protocols[feed_index] = feed_protocol;
            }
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATFlashESP32Callback) {
    if (!esp32.DeInit()) {
        CPP_AT_ERROR("CommsManager::ATFlashESP32Callback", "Error while de-initializing ESP32 before flashing.");
    }
    if (!esp32_flasher.FlashESP32()) {
        CPP_AT_ERROR("CommsManager::ATFlashESP32Callback", "Error while flashing ESP32.");
    }
    if (!esp32.Init()) {
        CPP_AT_ERROR("CommsManager::ATFlashESP32Callback", "Error while re-initializing ESP32 after flashing.");
    }

    CONSOLE_INFO("CommsManager::ATFlashESP32Callback", "ESP32 successfully flashed.");
    CPP_AT_SUCCESS();
}

CPP_AT_CALLBACK(CommsManager::ATProtocolCallback) {
    switch (op) {
        case '?':
            // Print out reporting protocols for CONSOLE and COMMS_UART.
            for (uint16_t iface = 0; iface < SettingsManager::SerialInterface::kGNSSUART; iface++) {
                CPP_AT_CMD_PRINTF("=%s,%s", SettingsManager::SerialInterfaceStrs[iface],
                                  SettingsManager::ReportingProtocolStrs[reporting_protocols_[iface]]);
            }
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // Set the reporting protocol for a given interface.
            if (!(CPP_AT_HAS_ARG(0) && CPP_AT_HAS_ARG(1))) {
                CPP_AT_ERROR("Requires two arguments: AT+PROTOCOL=<iface>,<protocol>.");
            }

            // Match the selected serial interface. Don't allow selection of the GNSS interface.
            SettingsManager::SerialInterface selected_iface = SettingsManager::SerialInterface::kNumSerialInterfaces;
            for (uint16_t iface = 0; iface < SettingsManager::SerialInterface::kGNSSUART; iface++) {
                if (args[0].compare(SettingsManager::SerialInterfaceStrs[iface]) == 0) {
                    selected_iface = static_cast<SettingsManager::SerialInterface>(iface);
                    break;
                }
            }
            if (selected_iface == SettingsManager::kNumSerialInterfaces) {
                CPP_AT_ERROR("Invalid serial interface %s.", args[0].data());
            }

            // Match the selected protocol.
            SettingsManager::ReportingProtocol selected_protocol = SettingsManager::ReportingProtocol::kNumProtocols;
            for (uint16_t protocol = 0; protocol < SettingsManager::ReportingProtocol::kNumProtocols; protocol++) {
                if (args[1].compare(SettingsManager::ReportingProtocolStrs[protocol]) == 0) {
                    selected_protocol = static_cast<SettingsManager::ReportingProtocol>(protocol);
                    break;
                }
            }
            if (selected_protocol == SettingsManager::kNumProtocols) {
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
    for (uint16_t iface = 0; iface < SettingsManager::kGNSSUART; iface++) {
        CPP_AT_PRINTF("%s ", SettingsManager::SerialInterfaceStrs[iface]);
    }
    CPP_AT_PRINTF("\r\n\t<protocol> = ");
    for (uint16_t protocol = 0; protocol < SettingsManager::kNumProtocols; protocol++) {
        CPP_AT_PRINTF("%s ", SettingsManager::ReportingProtocolStrs[protocol]);
    }
    CPP_AT_PRINTF("\r\n\tQuery the reporting protocol used on all interfaces:\r\n");
    CPP_AT_PRINTF("\tAT+PROTOCOL?\r\n\t+PROTOCOL=<iface>,<protocol>\r\n\t...\r\n");
}

CPP_AT_CALLBACK(CommsManager::ATRxEnableCallback) {
    switch (op) {
        case '=':
            if (CPP_AT_HAS_ARG(0)) {
                bool receiver_enabled;
                CPP_AT_TRY_ARG2NUM(0, receiver_enabled);
                ads_bee.SetReceiverEnable(receiver_enabled);
                CPP_AT_SUCCESS();
            }
            break;
        case '?':
            CPP_AT_CMD_PRINTF("=%d", ads_bee.ReceiverIsEnabled());
            CPP_AT_SILENT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
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
            char redacted_password[SettingsManager::kWiFiPasswordMaxLen + 1];
            redact_password(wifi_password, redacted_password, SettingsManager::kWiFiPasswordMaxLen);
            CPP_AT_CMD_PRINTF("=%d,%s,%s\r\n", static_cast<uint16_t>(wifi_enabled_), wifi_ssid, redacted_password);
            CPP_AT_SILENT_SUCCESS();
            break;
        }
        case '=': {
            if (CPP_AT_HAS_ARG(1)) {
                strncpy(wifi_ssid, args[1].data(), SettingsManager::kWiFiSSIDMaxLen);
                wifi_ssid[SettingsManager::kWiFiSSIDMaxLen] = '\0';
                CPP_AT_CMD_PRINTF(": ssid=%s\r\n", wifi_ssid);
            }
            if (CPP_AT_HAS_ARG(2)) {
                strncpy(wifi_password, args[2].data(), SettingsManager::kWiFiPasswordMaxLen);
                wifi_password[SettingsManager::kWiFiPasswordMaxLen] = '\0';
                char redacted_password[SettingsManager::kWiFiPasswordMaxLen];
                redact_password(wifi_password, redacted_password, SettingsManager::kWiFiPasswordMaxLen);
                CPP_AT_CMD_PRINTF(": password=%s\r\n", redacted_password);
            }

            if (CPP_AT_HAS_ARG(0)) {
                bool new_wifi_enabled = false;
                CPP_AT_TRY_ARG2NUM(0, new_wifi_enabled);
                if (SetWiFiEnabled(new_wifi_enabled)) {
                    CPP_AT_SUCCESS();
                } else {
                    CPP_AT_ERROR("Seting wifi_enabled=%d failed.", new_wifi_enabled);
                }
            }

            break;
        }
        default: {
            CPP_AT_ERROR("Operator %c not supported.", op);
        }
    }
    CPP_AT_ERROR();  // Should never get here.
}

const CppAT::ATCommandDef_t at_command_list[] = {
    {.command_buf = "+BAUDRATE",
     .min_args = 0,
     .max_args = 2,
     .help_string_buf = "AT+BAUDRATE=<iface>,<baudrate>\r\n\tSet the baud rate of a serial "
                        "interface.\r\n\tAT+BAUDRATE=COMMS,115200\r\n\tAT+BAUDRATE=GNSS,9600\r\n\tAT_BAUDRATE?",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATBaudrateCallback, comms_manager)},
    {.command_buf = "+LOG_LEVEL",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "AT+LOG_LEVEL=<log_level>\r\n\tSet how much stuff gets printed to the "
                        "console.\r\n\tconsole_verbosity = [SILENT ERRORS WARNINGS LOGS]",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATLogLevelCallback, comms_manager)},
    {.command_buf = "+FEED",
     .min_args = 0,
     .max_args = 5,
     .help_callback = ATFeedHelpCallback,
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATFeedCallback, comms_manager)},
    {.command_buf = "+FLASH_ESP32",
     .min_args = 0,
     .max_args = 0,
     .help_string_buf = "AT+FLASH_ESP32\r\n\tTriggers a firmware update of the ESP32 from the firmware image stored in "
                        "the RP2040's flash memory.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATFlashESP32Callback, comms_manager)},
    {.command_buf = "+PROTOCOL",
     .min_args = 0,
     .max_args = 2,
     .help_callback = CPP_AT_BIND_MEMBER_HELP_CALLBACK(CommsManager::ATProtocolHelpCallback, comms_manager),
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATProtocolCallback, comms_manager)},
    {.command_buf = "+RX_ENABLE",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "RX_ENABLE=<enabled [1,0]>\r\n\tOK\r\n\tEnables or disables the receiver from receiving "
                        "messages.\r\n\tAT+RX_ENABLE?\r\n\t+RX_ENABLE=<enabled [1,0]>\r\n\tQuery whether the "
                        "recevier is enabled.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATRxEnableCallback, comms_manager)

    },
    {.command_buf = "+RX_GAIN",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf =
         "Set or query value of Rx Gain Digipot.\r\n\t"
         "AT+RX_GAIN=<rx_gain>\r\n\tAT+RX_GAIN?\r\n\t+RX_GAIN=<rx_gain_commanded>(<Actual rx_gain_actual>).",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATRxGainCallback, comms_manager)

    },
    {.command_buf = "+SETTINGS",
     .min_args = 0,
     .max_args = 3,
     .help_string_buf = "Load, save, or reset nonvolatile settings.\r\n\tAT+SETTINGS=<op [LOAD SAVE RESET]>\r\n\t"
                        "Display nonvolatile settings.\r\n\tAT+SETTINGS?\r\n\t+SETTINGS=...\r\n\t",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATSettingsCallback, comms_manager)},
#ifdef HARDWARE_UNIT_TESTS
    {.command_buf = "+TEST",
     .min_args = 0,
     .max_args = 1,
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
const uint16_t at_command_list_num_commands = sizeof(at_command_list) / sizeof(at_command_list[0]);

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