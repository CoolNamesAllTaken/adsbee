#include "settings.hh"

#ifdef ON_PICO
#include "adsbee.hh"
#endif
#include "comms.hh"

// NOTE: This function needs to be updated separately for ESP32.
void SettingsManager::Print() {
    CONSOLE_PRINTF("Settings Struct\r\n");
    CONSOLE_PRINTF("\tReceiver: %s\r\n", settings.receiver_enabled ? "ENABLED" : "DISABLED");
#ifdef ON_PICO
    CONSOLE_PRINTF("\tTrigger Level: %d milliVolts (%d dBm)\r\n", settings.tl_mv,
                   adsbee.AD8313MilliVoltsTodBm(settings.tl_mv));
#elif ON_ESP32
    // ESP32 doesn't have access to mV->dBm conversion via ADSBee class.
    CONSOLE_PRINTF("\tTrigger Level: %d milliVolts\r\n", settings.tl_mv);
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
    CONSOLE_PRINTF("\tESP32: %s\r\n", settings.esp32_enabled ? "ENABLED" : "DISABLED");

    // Print WiFi AP settings.
    CONSOLE_PRINTF("\tWiFi AP: %s\r\n", settings.wifi_ap_enabled ? "ENABLED" : "DISABLED");
    if (settings.wifi_ap_enabled) {
        // Access Point settings. Don't censor password.
        CONSOLE_PRINTF("\t\tChannel: %d\r\n", settings.wifi_ap_channel);
        CONSOLE_PRINTF("\t\tSSID: %s\r\n", settings.wifi_ap_ssid);
        CONSOLE_PRINTF("\t\tPassword: %s\r\n", settings.wifi_ap_password);
    }
    // Print WiFi Station settings.
    CONSOLE_PRINTF("\tWiFi STA: %s\r\n", settings.wifi_sta_enabled ? "ENABLED" : "DISABLED");
    if (settings.wifi_sta_enabled) {
        // Station settings. Censor password.
        CONSOLE_PRINTF("\t\tSSID: %s\r\n", settings.wifi_sta_ssid);
        char redacted_wifi_sta_password[Settings::kWiFiPasswordMaxLen];
        RedactPassword(settings.wifi_sta_password, redacted_wifi_sta_password, strlen(settings.wifi_sta_password));
        CONSOLE_PRINTF("\t\tPassword: %s\r\n", redacted_wifi_sta_password);
    }
    // Print Ethernet settings.
    CONSOLE_PRINTF("\tEthernet: %s\r\n", settings.ethernet_enabled ? "ENABLED" : "DISABLED");

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