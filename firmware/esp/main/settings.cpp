#include "settings.hh"

#include "comms.hh"

bool SettingsManager::Apply() {
    bool ethernet_restart_required = false;
    bool wifi_sta_restart_required = false;
    bool wifi_ap_restart_required = false;

    // Check if the hostname has changed.
    if (strcmp(comms_manager.hostname, settings.hostname) != 0) {
        // Restart all network interfaces if the hostname has changed.
        ethernet_restart_required = true;
        wifi_sta_restart_required = true;
        wifi_ap_restart_required = true;
    }

    // Apply the hostname.
    strncpy(comms_manager.hostname, settings.hostname, Settings::kHostnameMaxLen);
    comms_manager.hostname[Settings::kHostnameMaxLen] = '\0';

    // Check if Ethernet settings have changed.
    if (comms_manager.ethernet_enabled != settings.ethernet_enabled) {
        ethernet_restart_required = true;
    }

    // Apply the Ethernet settings.
    comms_manager.ethernet_enabled = settings.ethernet_enabled;

    // Check if the AP settings have changed.
    if (comms_manager.wifi_ap_enabled != settings.wifi_ap_enabled ||
        (comms_manager.wifi_ap_enabled && (comms_manager.wifi_ap_channel != settings.wifi_ap_channel ||
                                           strcmp(comms_manager.wifi_ap_ssid, settings.wifi_ap_ssid) != 0 ||
                                           strcmp(comms_manager.wifi_ap_password, settings.wifi_ap_password) != 0))) {
        wifi_ap_restart_required = true;
    }
    // Apply the AP settings.
    comms_manager.wifi_ap_enabled = settings.wifi_ap_enabled;
    comms_manager.wifi_ap_channel = settings.wifi_ap_channel;
    strncpy(comms_manager.wifi_ap_ssid, settings.wifi_ap_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
    strncpy(comms_manager.wifi_ap_password, settings.wifi_ap_password,
            SettingsManager::Settings::kWiFiPasswordMaxLen + 1);

    // Check if the Station settings have changed.
    if (comms_manager.wifi_sta_enabled != settings.wifi_sta_enabled ||
        (comms_manager.wifi_sta_enabled &&
         (strcmp(comms_manager.wifi_sta_ssid, settings.wifi_sta_ssid) != 0 ||
          strcmp(comms_manager.wifi_sta_password, settings.wifi_sta_password) != 0))) {
        wifi_sta_restart_required = true;
    }

    // Apply the Station settings.
    comms_manager.wifi_sta_enabled = settings.wifi_sta_enabled;
    strncpy(comms_manager.wifi_sta_ssid, settings.wifi_sta_ssid, SettingsManager::Settings::kWiFiSSIDMaxLen + 1);
    strncpy(comms_manager.wifi_sta_password, settings.wifi_sta_password,
            SettingsManager::Settings::kWiFiPasswordMaxLen + 1);

    // Restart network interfaces if necessary.
    if (ethernet_restart_required) {
        if (!comms_manager.EthernetDeInit()) {
            CONSOLE_ERROR("SettingsManager::Apply", "Failed to deinitialize Ethernet.");
            return false;
        }
        if (settings.ethernet_enabled && !comms_manager.EthernetInit()) {
            CONSOLE_ERROR("SettingsManager::Apply", "Failed to initialize Ethernet.");
            return false;
        }
    }

    if (wifi_ap_restart_required || wifi_sta_restart_required) {
        if (!comms_manager.WiFiDeInit()) {
            CONSOLE_ERROR("SettingsManager::Apply", "Failed to deinitialize WiFi.");
            return false;
        }
        if ((settings.wifi_ap_enabled || settings.wifi_sta_enabled) && !comms_manager.WiFiInit()) {
            CONSOLE_ERROR("SettingsManager::Apply", "Failed to initialize WiFi.");
            return false;
        }
    }
    return true;
}

// void SettingsManager::Print() {
//     CONSOLE_PRINTF("Settings Struct\r\n");
//     CONSOLE_PRINTF("\tReceiver: %s\r\n", settings.receiver_enabled ? "ENABLED" : "DISABLED");
//     CONSOLE_PRINTF("\tTrigger Level: %d milliVolts\r\n", settings.tl_mv);
//     CONSOLE_PRINTF("\tBias Tee: %s\r\n", settings.bias_tee_enabled ? "ENABLED" : "DISABLED");
//     CONSOLE_PRINTF("\tWatchdog Timeout: %lu seconds\r\n", settings.watchdog_timeout_sec);
//     CONSOLE_PRINTF("\tLog Level: %s\r\n", kConsoleLogLevelStrs[settings.log_level]);
//     CONSOLE_PRINTF("\tReporting Protocols:\r\n");
//     for (uint16_t i = 0; i < SerialInterface::kGNSSUART; i++) {
//         // Only report protocols for CONSOLE and COMMS_UART.
//         CONSOLE_PRINTF("\t\t%s: %s\r\n", kSerialInterfaceStrs[i],
//                        kReportingProtocolStrs[settings.reporting_protocols[i]]);
//     }
//     CONSOLE_PRINTF("\tComms UART Baud Rate: %lu baud\r\n", settings.comms_uart_baud_rate);
//     CONSOLE_PRINTF("\tGNSS UART Baud Rate: %lu baud\r\n", settings.gnss_uart_baud_rate);
//     CONSOLE_PRINTF("\tESP32: %s\r\n", settings.esp32_enabled ? "ENABLED" : "DISABLED");

//     // Print WiFi AP settings.
//     CONSOLE_PRINTF("\tWiFi AP: %s\r\n", settings.wifi_ap_enabled ? "ENABLED" : "DISABLED");
//     if (settings.wifi_ap_enabled) {
//         // Access Point settings. Don't censor password.
//         CONSOLE_PRINTF("\t\tChannel: %d\r\n", settings.wifi_ap_channel);
//         CONSOLE_PRINTF("\t\tSSID: %s\r\n", settings.wifi_ap_ssid);
//         CONSOLE_PRINTF("\t\tPassword: %s\r\n", settings.wifi_ap_password);
//     }
//     // Print WiFi Station settings.
//     CONSOLE_PRINTF("\tWiFi STA: %s\r\n", settings.wifi_sta_enabled ? "ENABLED" : "DISABLED");
//     if (settings.wifi_sta_enabled) {
//         // Station settings. Censor password.
//         CONSOLE_PRINTF("\t\tSSID: %s\r\n", settings.wifi_sta_ssid);
//         char redacted_wifi_sta_password[Settings::kWiFiPasswordMaxLen];
//         RedactPassword(settings.wifi_sta_password, redacted_wifi_sta_password, strlen(settings.wifi_sta_password));
//         CONSOLE_PRINTF("\t\tPassword: %s\r\n", redacted_wifi_sta_password);
//     }
//     // Print Ethernet settings.
//     CONSOLE_PRINTF("\tEthernet: %s\r\n", settings.ethernet_enabled ? "ENABLED" : "DISABLED");

//     CONSOLE_PRINTF("\tFeed URIs:\r\n");
//     for (uint16_t i = 0; i < Settings::kMaxNumFeeds; i++) {
//         CONSOLE_PRINTF("\t\t%d URI:%s Port:%d %s Protocol:%s ID:0x", i, settings.feed_uris[i],
//         settings.feed_ports[i],
//                        settings.feed_is_active[i] ? "ACTIVE" : "INACTIVE",
//                        kReportingProtocolStrs[settings.feed_protocols[i]]);
//         for (int16_t feeder_id_byte_index = 0; feeder_id_byte_index < Settings::kFeedReceiverIDNumBytes;
//              feeder_id_byte_index++) {
//             CONSOLE_PRINTF("%02x", settings.feed_receiver_ids[i][feeder_id_byte_index]);
//         }
//         CONSOLE_PRINTF("\r\n");
//     }
// }