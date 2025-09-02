#include "settings.hh"

#ifdef ON_PICO
#include "adsbee.hh"
#endif
#include "comms.hh"

// NOTE: This function needs to be updated separately for ESP32.
void SettingsManager::Print() {
    CONSOLE_PRINTF("Settings Struct\r\n");
    CONSOLE_PRINTF("\tReceiver: %s\r\n", settings.r1090_rx_enabled ? "ENABLED" : "DISABLED");
#ifdef ON_PICO
    CONSOLE_PRINTF("\tTrigger Level: %d milliVolts (%d dBm)\r\n", settings.tl_offset_mv,
                   adsbee.AD8313MilliVoltsTodBm(settings.tl_offset_mv));
#elif ON_ESP32
    // ESP32 doesn't have access to mV->dBm conversion via ADSBee class.
    CONSOLE_PRINTF("\tTrigger Offset Level: %d milliVolts\r\n", settings.tl_offset_mv);
#endif
    CONSOLE_PRINTF("\tBias Tee: %s\r\n", settings.bias_tee_enabled ? "ENABLED" : "DISABLED");
    CONSOLE_PRINTF("\tWatchdog Timeout: %lu seconds\r\n", settings.watchdog_timeout_sec);
    CONSOLE_PRINTF("\tLog Level: %s\r\n", kConsoleLogLevelStrs[settings.log_level]);
    CONSOLE_PRINTF("\tReporting Protocols:\r\n");
    for (uint16_t i = 0; i < SerialInterface::kGNSSUART; i++) {
        // Only report protocols for CONSOLE and COMMS_UART.
        CONSOLE_PRINTF("\t\t%s: %s\r\n", kSerialInterfaceStrs[i],
                       kReportingProtocolStrs[settings.reporting_protocols[i]]);
    }
    CONSOLE_PRINTF("\tComms UART Baud Rate: %lu baud\r\n", settings.comms_uart_baud_rate);
    CONSOLE_PRINTF("\tGNSS UART Baud Rate: %lu baud\r\n", settings.gnss_uart_baud_rate);
    CONSOLE_PRINTF("\tESP32: %s\r\n", settings.core_network_settings.esp32_enabled ? "ENABLED" : "DISABLED");
    CONSOLE_PRINTF(
        "\tSub-GHz Radio: %s\r\n",
        settings.subg_enabled == SettingsManager::EnableState::kEnableStateEnabled
            ? "ENABLED"
            : (settings.subg_enabled == SettingsManager::EnableState::kEnableStateExternal ? "EXTERNAL" : "DISABLED"));

    // Print WiFi AP settings.
    CONSOLE_PRINTF("\tWiFi AP: %s\r\n", settings.core_network_settings.wifi_ap_enabled ? "ENABLED" : "DISABLED");
    if (settings.core_network_settings.wifi_ap_enabled) {
        // Access Point settings. Don't censor password.
        CONSOLE_PRINTF("\t\tChannel: %d\r\n", settings.core_network_settings.wifi_ap_channel);
        CONSOLE_PRINTF("\t\tSSID: %s\r\n", settings.core_network_settings.wifi_ap_ssid);
        CONSOLE_PRINTF("\t\tPassword: %s\r\n", settings.core_network_settings.wifi_ap_password);
    }
    // Print WiFi Station settings.
    CONSOLE_PRINTF("\tWiFi STA: %s\r\n", settings.core_network_settings.wifi_sta_enabled ? "ENABLED" : "DISABLED");
    if (settings.core_network_settings.wifi_sta_enabled) {
        // Station settings. Censor password.
        CONSOLE_PRINTF("\t\tSSID: %s\r\n", settings.core_network_settings.wifi_sta_ssid);
        char redacted_wifi_sta_password[Settings::kWiFiPasswordMaxLen];
        RedactPassword(settings.core_network_settings.wifi_sta_password, redacted_wifi_sta_password,
                       strlen(settings.core_network_settings.wifi_sta_password));
        CONSOLE_PRINTF("\t\tPassword: %s\r\n", redacted_wifi_sta_password);
    }
    // Print Ethernet settings.
    CONSOLE_PRINTF("\tEthernet: %s\r\n", settings.core_network_settings.ethernet_enabled ? "ENABLED" : "DISABLED");

    CONSOLE_PRINTF("\tFeed URIs:\r\n");
    for (uint16_t i = 0; i < Settings::kMaxNumFeeds; i++) {
        CONSOLE_PRINTF("\t\t%d URI:%s Port:%d %s Protocol:%s ID:0x", i, settings.feed_uris[i], settings.feed_ports[i],
                       settings.feed_is_active[i] ? "ACTIVE" : "INACTIVE",
                       kReportingProtocolStrs[settings.feed_protocols[i]]);
        for (int16_t feeder_id_byte_index = 0; feeder_id_byte_index < Settings::kFeedReceiverIDNumBytes;
             feeder_id_byte_index++) {
            CONSOLE_PRINTF("%02x", settings.feed_receiver_ids[i][feeder_id_byte_index]);
        }
        CONSOLE_PRINTF("\r\n");
    }
}

void SettingsManager::PrintAT() {
    // AT+BAUD_RATE
    // Note: Baud rate cannot be changed for CONSOLE since it is a virtual COM port. Don't print its baud rate.
    for (uint16_t i = SerialInterface::kCommsUART; i < SerialInterface::kNumSerialInterfaces; i++) {
        CONSOLE_PRINTF("AT+BAUD_RATE=%s,%lu\r\n", kSerialInterfaceStrs[i], settings.comms_uart_baud_rate);
    }

    // AT+BIAS_TEE_ENABLE
    CONSOLE_PRINTF("AT+BIAS_TEE_ENABLE=%d\r\n", settings.bias_tee_enabled);

    // AT+DEVICE_INFO: Don't store this.

    // AT+ESP32_ENABLE
    CONSOLE_PRINTF("AT+ESP32_ENABLE=%d\r\n", settings.core_network_settings.esp32_enabled);

    // AT+ETHERNET
    CONSOLE_PRINTF("AT+ETHERNET=%d\r\n", settings.core_network_settings.ethernet_enabled);

    // AT+FEED
    for (uint16_t i = 0; i < Settings::kMaxNumFeeds; i++) {
        CONSOLE_PRINTF("AT+FEED=%d,%s,%u,%d,%s\r\n", i, settings.feed_uris[i], settings.feed_ports[i],
                       settings.feed_is_active[i], kReportingProtocolStrs[settings.feed_protocols[i]]);
    }

    // AT+LOG_LEVEL
    CONSOLE_PRINTF("AT+LOG_LEVEL=%s\r\n", kConsoleLogLevelStrs[settings.log_level]);

    // AT+PROTOCOL
    for (uint16_t i = 0; i < SerialInterface::kGNSSUART; i++) {
        CONSOLE_PRINTF("AT+PROTOCOL=%s,%s\r\n", kSerialInterfaceStrs[i],
                       kReportingProtocolStrs[settings.reporting_protocols[i]]);
    }

    // AT+RX_ENABLE
    CONSOLE_PRINTF("AT+RX_ENABLE=%d\r\n", settings.r1090_rx_enabled);

    // AT+SUBG_ENABLE
    CONSOLE_PRINTF("AT+SUBG_ENABLE=%s\r\n", SettingsManager::EnableStateToATValueStr(settings.subg_enabled));

    // AT+TL_SET
    CONSOLE_PRINTF("AT+TL_SET=%u\r\n", settings.tl_offset_mv);

    // AT+WATCHDOG
    CONSOLE_PRINTF("AT+WATCHDOG=%lu\r\n", settings.watchdog_timeout_sec);

    // AT+WIFI_AP
    CONSOLE_PRINTF("AT+WIFI_AP=%d,%s,%s,%d\r\n", settings.core_network_settings.wifi_ap_enabled,
                   settings.core_network_settings.wifi_ap_ssid, settings.core_network_settings.wifi_ap_password,
                   settings.core_network_settings.wifi_ap_channel);

    // AT+WIFI_STA
    CONSOLE_PRINTF("AT+WIFI_STA=%d,%s,%s\r\n", settings.core_network_settings.wifi_sta_enabled,
                   settings.core_network_settings.wifi_sta_ssid, settings.core_network_settings.wifi_sta_password);
}