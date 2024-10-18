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

const uint32_t kDeviceInfoProgrammingPassword = 0xDEDBEEF;  // This is intended to stop people from accidentally
                                                            // modifying serial number information on their device.

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
            CPP_AT_CMD_PRINTF("=%d(COMMS_UART),%d(GNSS_UART)", comms_uart_baudrate_, gnss_uart_baudrate_);
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            if (!(CPP_AT_HAS_ARG(0) && CPP_AT_HAS_ARG(1))) {
                CPP_AT_ERROR(
                    "Requires two arguments: AT+BAUDRATE=<iface>,<baudrate> where <iface> can be one of [COMMS_UART, "
                    "GNSS_UART].");
            }
            SettingsManager::SerialInterface iface;
            if (args[0].compare("COMMS_UART") == 0) {
                iface = SettingsManager::kCommsUART;
            } else if (args[0].compare("GNSS_UART") == 0) {
                iface = SettingsManager::kGNSSUART;
            } else {
                CPP_AT_ERROR("Invalid interface. Must be one of [COMMS_UART, GNSS_UART].");
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

CPP_AT_CALLBACK(CommsManager::ATBiasTeeEnableCallback) {
    switch (op) {
        case '?':
            CPP_AT_CMD_PRINTF("=%d", adsbee.BiasTeeIsEnabled());
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            if (!(CPP_AT_HAS_ARG(0))) {
                CPP_AT_ERROR("Requires an argument (0 or 1). AT+BIAS_TEE_ENABLED=<enabled>");
            }
            bool enabled;
            CPP_AT_TRY_ARG2NUM(0, enabled);
            adsbee.SetBiasTeeEnable(enabled);
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR();
}

CPP_AT_CALLBACK(CommsManager::ATESP32EnableCallback) {
    switch (op) {
        case '?':
            CPP_AT_CMD_PRINTF("=%d", esp32.IsEnabled());
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Requires an argument (0 or 1). AT+ESP32_ENABLED=<enabled>");
            }
            bool enabled;
            bool already_enabled = esp32.IsEnabled();
            CPP_AT_TRY_ARG2NUM(0, enabled);
            if (enabled && !already_enabled) {
                esp32.Init();
            } else if (!enabled && already_enabled) {
                esp32.DeInit();
            }
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR();
}

CPP_AT_CALLBACK(CommsManager::ATDeviceInfoCallback) {
    switch (op) {
        case '?': {
            SettingsManager::DeviceInfo device_info;
            if (!settings_manager.GetDeviceInfo(device_info)) {
                CPP_AT_ERROR("Error while retrieving device info.");
            }
            device_info.part_code[SettingsManager::DeviceInfo::kPartCodeLen] =
                '\0';  // Use caution in case part code is invalid.
            CPP_AT_PRINTF("Part Code: %s\r\n", device_info.part_code);
            CPP_AT_PRINTF("RP2040 Firmware Version: %d.%d.%d\r\n", object_dictionary.kFirmwareVersionMajor,
                          object_dictionary.kFirmwareVersionMinor, object_dictionary.kFirmwareVersionPatch);

            if (esp32.IsEnabled()) {
                uint32_t esp32_firmware_version;
                if (!esp32.Read(ObjectDictionary::kAddrFirmwareVersion, esp32_firmware_version)) {
                    CPP_AT_ERROR("ESP32 firmware version read failed!");
                }
                CPP_AT_PRINTF("ESP32 Firmware Version: %d.%d.%d\r\n", esp32_firmware_version >> 16,
                              (esp32_firmware_version >> 8) & 0xFF, esp32_firmware_version & 0xFF);
            } else {
                CPP_AT_PRINTF("ESP32 Firmware Version: Not Available (ESP32 Disabled)\r\n");
            }

            CPP_AT_SILENT_SUCCESS();
            break;
        }
        case '=': {
            // AT+DEVICE_INFO=<programming_password>,<device_info_version>,<part_code>
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Missing programming password.");
            } else {
                uint32_t programming_password;
                CPP_AT_TRY_ARG2NUM_BASE(0, programming_password, 16);
                if (programming_password != kDeviceInfoProgrammingPassword) {
                    CPP_AT_ERROR("Programming password 0x%x does not match.", programming_password);
                }
                // Program device information here.
                SettingsManager::DeviceInfo device_info;
                settings_manager.GetDeviceInfo(device_info);  // Override existing info, if fields are provided.
                if (CPP_AT_HAS_ARG(1)) {
                    CPP_AT_TRY_ARG2NUM(1, device_info.device_info_version);
                }
                if (CPP_AT_HAS_ARG(2)) {
                    // Copy part code while guarding against part codes that are too long.
                    strncpy(device_info.part_code, args[2].data(), SettingsManager::DeviceInfo::kPartCodeLen);
                    device_info.part_code[SettingsManager::DeviceInfo::kPartCodeLen] = '\0';
                }
                if (settings_manager.SetDeviceInfo(device_info)) {
                    CPP_AT_SUCCESS();
                }
                CPP_AT_ERROR("Error while attempting to set device info.");
            }
            break;
        }
    }
    CPP_AT_ERROR();
}

void ATFeedHelpCallback() {
    CPP_AT_PRINTF(
        "\tAT+FEED=<feed_index>,<feed_uri>,<feed_port>,<active>,<protocol>\r\n\tSet details for a "
        "network feed.\r\n\tfeed_index = [0-%d], feed_uri = ip address or URL, feed_port = [0-65535], "
        "active = [0 1], protocol = [BEAST].\r\n\t\r\n\tAT+FEED?\r\n\tPrint details for all "
        "feeds.\r\n\t\r\n\tAT+FEED?<feed_index>\r\n\tPrint details for a specific feed.\r\n\tfeed_index = [0-%d]",
        SettingsManager::Settings::kMaxNumFeeds - 1, SettingsManager::Settings::kMaxNumFeeds - 1);
}

CPP_AT_CALLBACK(CommsManager::ATFeedCallback) {
    switch (op) {
        case '?':
            if (CPP_AT_HAS_ARG(0)) {
                // Querying info about a specific feed.
                uint16_t feed_index = UINT16_MAX;
                CPP_AT_TRY_ARG2NUM(0, feed_index);
                if (feed_index >= SettingsManager::Settings::kMaxNumFeeds) {
                    CPP_AT_ERROR("Feed number must be between 0-%d, no details for feed with index %d.",
                                 SettingsManager::Settings::kMaxNumFeeds - 1, feed_index);
                }
                CPP_AT_CMD_PRINTF(
                    "=%d(FEED_INDEX),%s(FEED_URI),%d(FEED_PORT),%d(ACTIVE),%s(PROTOCOL)", feed_index,
                    settings_manager.settings.feed_uris[feed_index], settings_manager.settings.feed_ports[feed_index],
                    settings_manager.settings.feed_is_active[feed_index],
                    SettingsManager::kReportingProtocolStrs[settings_manager.settings.feed_protocols[feed_index]]);
            } else {
                // Querying info about all feeds.
                for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
                    CPP_AT_CMD_PRINTF(
                        "=%d(FEED_INDEX),%s(FEED_URI),%d(FEED_PORT),%d(ACTIVE),%s(PROTOCOL)", i,
                        settings_manager.settings.feed_uris[i], settings_manager.settings.feed_ports[i],
                        settings_manager.settings.feed_is_active[i],
                        SettingsManager::kReportingProtocolStrs[settings_manager.settings.feed_protocols[i]]);
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
            if (feed_index >= SettingsManager::Settings::kMaxNumFeeds) {
                CPP_AT_ERROR("Feed index must be between 0-%d, no details for feed with index %d.",
                             SettingsManager::Settings::kMaxNumFeeds - 1, feed_index);
            }
            // Set FEED_URI.
            if (CPP_AT_HAS_ARG(1)) {
                strncpy(settings_manager.settings.feed_uris[feed_index], args[1].data(),
                        SettingsManager::Settings::kFeedURIMaxNumChars);
                settings_manager.settings.feed_uris[feed_index][SettingsManager::Settings::kFeedURIMaxNumChars] = '\0';
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
                    if (args[4].compare(SettingsManager::kReportingProtocolStrs[i]) == 0) {
                        feed_protocol = static_cast<SettingsManager::ReportingProtocol>(i);
                    }
                }
                // Check that the selected prototcol is valid for use with feeders.
                if (!(feed_protocol == SettingsManager::ReportingProtocol::kBeast ||
                      feed_protocol == SettingsManager::ReportingProtocol::kNoReports)) {
                    CPP_AT_ERROR("Protocol %s is not supported for network feeds.",
                                 SettingsManager::kReportingProtocolStrs[feed_protocol]);
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

CPP_AT_CALLBACK(CommsManager::ATLogLevelCallback) {
    switch (op) {
        case '?':
            // AT+CONFIG mode query.
            CPP_AT_CMD_PRINTF("=%s", SettingsManager::kConsoleLogLevelStrs[log_level]);
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // AT+CONFIG set command.
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Need to specify a config mode to run.");
            }
            for (uint16_t i = 0; i < SettingsManager::kNumLogLevels; i++) {
                if (args[0].compare(SettingsManager::kConsoleLogLevelStrs[i]) == 0) {
                    log_level = static_cast<SettingsManager::LogLevel>(i);
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
            for (uint16_t iface = 0; iface < SettingsManager::SerialInterface::kGNSSUART; iface++) {
                CPP_AT_CMD_PRINTF("=%s,%s", SettingsManager::kSerialInterfaceStrs[iface],
                                  SettingsManager::kReportingProtocolStrs[reporting_protocols_[iface]]);
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
                if (args[0].compare(SettingsManager::kSerialInterfaceStrs[iface]) == 0) {
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
                if (args[1].compare(SettingsManager::kReportingProtocolStrs[protocol]) == 0) {
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
        CPP_AT_PRINTF("%s ", SettingsManager::kSerialInterfaceStrs[iface]);
    }
    CPP_AT_PRINTF("\r\n\t<protocol> = ");
    for (uint16_t protocol = 0; protocol < SettingsManager::kNumProtocols; protocol++) {
        CPP_AT_PRINTF("%s ", SettingsManager::kReportingProtocolStrs[protocol]);
    }
    CPP_AT_PRINTF("\r\n\tQuery the reporting protocol used on all interfaces:\r\n");
    CPP_AT_PRINTF("\tAT+PROTOCOL?\r\n\t+PROTOCOL=<iface>,<protocol>\r\n\t...\r\n");
}

CPP_AT_CALLBACK(CommsManager::ATRebootCallback) {
    adsbee.Reboot();
    CPP_AT_SUCCESS();  // There is a slight delay (1s) while the watchdog runs out, which allows this line to print.
}

CPP_AT_CALLBACK(CommsManager::ATRxEnableCallback) {
    switch (op) {
        case '=':
            if (CPP_AT_HAS_ARG(0)) {
                bool receiver_enabled;
                CPP_AT_TRY_ARG2NUM(0, receiver_enabled);
                adsbee.SetReceiverEnable(receiver_enabled);
                CPP_AT_SUCCESS();
            }
            break;
        case '?':
            CPP_AT_CMD_PRINTF("=%d", adsbee.ReceiverIsEnabled());
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
            settings_manager.Print();
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATTLReadCallback) {
    switch (op) {
        case '?':
            // Read command.
            CPP_AT_CMD_PRINTF("=%d\r\n", adsbee.ReadTLMilliVolts());
            CPP_AT_SILENT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

/**
 * AT+TL_SET Callback
 * AT+TL_SET=<tl_mv>
 *  tl_mv = Trigger Level, in milliVolts.
 * AT+TL_SET?
 * +TL_SET=
 */
CPP_AT_CALLBACK(CommsManager::ATTLSetCallback) {
    switch (op) {
        case '?':
            // AT+TL_SET value query.
            CPP_AT_CMD_PRINTF("=%d\r\n", adsbee.GetTLMilliVolts());
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // Attempt setting LO TL value, in milliVolts, if first argument is not blank.
            if (CPP_AT_HAS_ARG(0)) {
                if (args[0].compare("LEARN") == 0) {
                    // Starting a new trigger level learning session.
                    adsbee.StartTLLearning();
                } else {
                    // Assigning trigger level manually.
                    uint16_t new_tl_mv;
                    CPP_AT_TRY_ARG2NUM(0, new_tl_mv);
                    if (!adsbee.SetTLMilliVolts(new_tl_mv)) {
                        CPP_AT_ERROR("Failed to set tl_mv.");
                    }
                }
            }
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATWiFiAPCallback) {
    switch (op) {
        case '?': {
            char redacted_password[SettingsManager::Settings::kWiFiPasswordMaxLen + 1];
            CPP_AT_CMD_PRINTF("=%d,%s,%s\r\n", wifi_ap_ssid, wifi_ap_password);
            CPP_AT_SILENT_SUCCESS();
            break;
        }
        case '=': {
            if (CPP_AT_HAS_ARG(0)) {
                CPP_AT_TRY_ARG2NUM(0, wifi_ap_enabled);
                CPP_AT_CMD_PRINTF(": wifi_ap_enabled=%d\r\n", wifi_ap_enabled);
            }
            if (CPP_AT_HAS_ARG(1)) {
                strncpy(wifi_ap_ssid, args[1].data(), SettingsManager::Settings::kWiFiSSIDMaxLen);
                wifi_ap_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen] = '\0';
                CPP_AT_CMD_PRINTF(": wifi_ap_ssid=%s\r\n", wifi_ap_ssid);
            }
            if (CPP_AT_HAS_ARG(2)) {
                strncpy(wifi_ap_password, args[2].data(), SettingsManager::Settings::kWiFiPasswordMaxLen);
                wifi_ap_password[SettingsManager::Settings::kWiFiPasswordMaxLen] = '\0';
                CPP_AT_CMD_PRINTF(": wifi_ap_password=%s\r\n", wifi_ap_password);
            }
            if (CPP_AT_HAS_ARG(3)) {
                uint8_t channel;
                CPP_AT_TRY_ARG2NUM(3, channel);
                if (channel > SettingsManager::kWiFiAPChannelMax) {
                    CPP_AT_ERROR("WiFi channel out of range, must be <= %d.", SettingsManager::kWiFiAPChannelMax);
                }
                wifi_ap_channel = channel;
                CPP_AT_CMD_PRINTF(": wifi_ap_channel = %d\r\n", wifi_ap_channel);
            }
            CPP_AT_SUCCESS();
            break;
        }
        default: {
            CPP_AT_ERROR("Operator %c not supported.", op);
        }
    }
    CPP_AT_ERROR();  // Should never get here.
}

CPP_AT_CALLBACK(CommsManager::ATWiFiSTACallback) {
    switch (op) {
        case '?': {
            char redacted_password[SettingsManager::Settings::kWiFiPasswordMaxLen + 1];
            SettingsManager::RedactPassword(wifi_sta_password, redacted_password,
                                            SettingsManager::Settings::kWiFiPasswordMaxLen);
            CPP_AT_CMD_PRINTF("=%d,%s,%s\r\n", wifi_sta_enabled, wifi_sta_ssid, redacted_password);
            CPP_AT_SILENT_SUCCESS();
            break;
        }
        case '=': {
            if (CPP_AT_HAS_ARG(0)) {
                CPP_AT_TRY_ARG2NUM(0, wifi_sta_enabled);
                CPP_AT_CMD_PRINTF(": wifi_sta_enabled=%d\r\n", wifi_sta_enabled);
            }
            if (CPP_AT_HAS_ARG(1)) {
                strncpy(wifi_sta_ssid, args[3].data(), SettingsManager::Settings::kWiFiSSIDMaxLen);
                wifi_sta_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen] = '\0';
                CPP_AT_CMD_PRINTF(": sta_ssid=%s\r\n", wifi_sta_ssid);
            }
            if (CPP_AT_HAS_ARG(2)) {
                strncpy(wifi_sta_password, args[4].data(), SettingsManager::Settings::kWiFiPasswordMaxLen);
                wifi_sta_password[SettingsManager::Settings::kWiFiPasswordMaxLen] = '\0';
                char redacted_password[SettingsManager::Settings::kWiFiPasswordMaxLen];
                SettingsManager::RedactPassword(wifi_sta_password, redacted_password,
                                                SettingsManager::Settings::kWiFiPasswordMaxLen);
                CPP_AT_CMD_PRINTF(": sta_password=%s\r\n", redacted_password);
            }

            CPP_AT_SUCCESS();
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
                        "interface.\r\n\tAT_BAUDRATE?\r\n\tQuery the baud rate of all serial interfaces.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATBaudrateCallback, comms_manager)},
    {.command_buf = "+BIAS_TEE_ENABLE",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "AT+BIAS_TEE_ENABLE=<enabled>\r\n\tEnable or disable the bias "
                        "tee.\r\n\tBIAS_TEE_ENABLE?\r\n\tQuery the status of the bias tee.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATBiasTeeEnableCallback, comms_manager)},
    {.command_buf = "+DEVICE_INFO",
     .min_args = 0,
     .max_args = 5,  // TODO: check this value.
     .help_string_buf = "AT+DEVICE_INFO?\r\n\tQuery device information.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATDeviceInfoCallback, comms_manager)},
    {.command_buf = "+ESP32_ENABLE",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "AT+ESP32_ENABLE=<enabled>\r\n\tEnable or disable the ESP32.\r\n\tAT+ESP32_ENABLE?\r\n\tQuery "
                        "the enable status of the ESP32.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATESP32EnableCallback, comms_manager)},
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
    {.command_buf = "+LOG_LEVEL",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf =
         "AT+LOG_LEVEL=<log_level [SILENT ERRORS WARNINGS LOGS]>\r\n\tSet how much stuff gets printed to the "
         "console.\r\n\t",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATLogLevelCallback, comms_manager)},
    {.command_buf = "+PROTOCOL",
     .min_args = 0,
     .max_args = 2,
     .help_callback = CPP_AT_BIND_MEMBER_HELP_CALLBACK(CommsManager::ATProtocolHelpCallback, comms_manager),
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATProtocolCallback, comms_manager)},
    {.command_buf = "+REBOOT",
     .min_args = 0,
     .max_args = 0,
     .help_string_buf = "REBOOT\r\n\tReboots the RP2040.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATRebootCallback, comms_manager)},
    {.command_buf = "+RX_ENABLE",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "RX_ENABLE=<enabled [1,0]>\r\n\tOK\r\n\tEnables or disables the receiver from receiving "
                        "messages.\r\n\tAT+RX_ENABLE?\r\n\t+RX_ENABLE=<enabled [1,0]>\r\n\tQuery whether the "
                        "recevier is enabled.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATRxEnableCallback, comms_manager)

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
     .help_string_buf =
         "Read ADC counts and mV value for the minimum trigger level threshold. Call with no ops nor arguments, "
         "AT+TL_READ.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATTLReadCallback, comms_manager)},
    {.command_buf = "+TL_SET",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "Set minimum trigger level threshold for RF power detector.\r\n\tAT+TLSet=<tl_mv>"
                        "\tQuery trigger level.\r\n\tAT+TL_SET?\r\n\t+TLSet=<tl_mv>.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATTLSetCallback, comms_manager)},
    {.command_buf = "+WIFI_AP",
     .min_args = 0,
     .max_args = 4,
     .help_string_buf =
         "Set WiFi access point params.\r\n\tAT+WIFI_AP=<enabled>,<ap_ssid>,<ap_pwd>,<ap_channel>\r\n\t"
         "Get WiFi access point params.\r\n\tAT+WIFI_AP?\r\n\t+WIFI_AP=<enabled>,<ap_ssid>,<ap_pwd>,<ap_channel>",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATWiFiAPCallback, comms_manager)},
    {.command_buf = "+WIFI_STA",
     .min_args = 0,
     .max_args = 3,
     .help_string_buf = "Set WiFi station params.\r\n\tAT+WIFI_STA=<enabled>,<sta_ssid>,<sta_pwd>\r\n\t"
                        "Get WiFi station params.\r\n\tAT+WIFI_STA?\r\n\t+WIFI_STA=<enabled>,<sta_ssid>,<sta_pwd>",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATWiFiSTACallback, comms_manager)},
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