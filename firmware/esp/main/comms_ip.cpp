#include "beast/beast_utils.hh"  // For beast reporting.
#include "comms.hh"
#include "esp_event.h"
#include "esp_mac.h"
#include "hal.hh"
#include "lwip/dns.h"
#include "lwip/err.h"
#include "lwip/netdb.h"
#include "lwip/sockets.h"
#include "lwip/sys.h"
#include "task_priorities.hh"

static const uint32_t kWiFiTCPSocketReconnectIntervalMs = 5000;

/** "Pass-Through" functions used to access member functions in callbacks. **/
void ip_event_handler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    comms_manager.IPEventHandler(arg, event_base, event_id, event_data);
}
void ip_wan_task(void* pvParameters) { comms_manager.IPWANTask(pvParameters); }
/** End "Pass-Through" functions. **/

bool IsNotIPAddress(const char* uri) {
    // Check if the URI contains any letters
    for (const char* p = uri; *p != '\0'; p++) {
        if (isalpha(*p)) {
            return true;
        }
    }
    return false;
}

bool ResolveURIToIP(const char* url, char* ip) {
    struct addrinfo hints;
    struct addrinfo* res;
    struct in_addr addr;
    int err;

    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;

    err = getaddrinfo(url, NULL, &hints, &res);
    if (err != 0 || res == NULL) {
        CONSOLE_ERROR("ResolveURLToIP", "DNS lookup failed for %s: %d", url, err);
        return false;
    }

    addr.s_addr = ((struct sockaddr_in*)res->ai_addr)->sin_addr.s_addr;
    inet_ntop(AF_INET, &addr, ip, 16);
    CONSOLE_INFO("ResolveURLToIP", "DNS lookup succeeded. IP=%s", ip);

    freeaddrinfo(res);
    return true;
}

bool CommsManager::IPInit() {
    ESP_ERROR_CHECK(esp_event_handler_register(IP_EVENT, ESP_EVENT_ANY_ID, &ip_event_handler, NULL));
    ip_event_handler_was_initialized_ = true;

    xTaskCreatePinnedToCore(ip_wan_task, "ip_wan_task", 4096, &ip_wan_task_handle, kIPWANTaskPriority, NULL,
                            kIPWANTaskCore);
    return true;
}

void CommsManager::IPEventHandler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    switch (event_id) {
        case IP_EVENT_AP_STAIPASSIGNED: {
            // A new station has connected to the ADSBee's softAP network.
            ip_event_ap_staipassigned_t* event = (ip_event_ap_staipassigned_t*)event_data;

            char client_mac_str[SettingsManager::Settings::kMACAddrStrLen + 1] = {0};
            char client_ip_str[SettingsManager::Settings::kIPAddrStrLen + 1] = {0};
            snprintf(client_mac_str, SettingsManager::Settings::kMACAddrStrLen, MACSTR, MAC2STR(event->mac));
            client_mac_str[SettingsManager::Settings::kMACAddrStrLen] = '\0';
            snprintf(client_ip_str, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&event->ip));
            client_ip_str[SettingsManager::Settings::kIPAddrStrLen] = '\0';

            CONSOLE_INFO("CommsManager::IPEventHandler",
                         "WiFi Access Point assigned IP address to client. IP: %s, MAC: %s", client_ip_str,
                         client_mac_str);

            WiFiAddClient(event->ip, event->mac);
            break;
        }
        case IP_EVENT_STA_GOT_IP: {
            // The ADSBee has connected to an external network as a WiFi station.
            ip_event_got_ip_t* event = (ip_event_got_ip_t*)event_data;
            const esp_netif_ip_info_t* ip_info = &event->ip_info;

            wifi_sta_has_ip_ = true;
            snprintf(wifi_sta_ip, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->ip));
            wifi_sta_ip[SettingsManager::Settings::kIPAddrStrLen] = '\0';
            snprintf(wifi_sta_netmask, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->netmask));
            wifi_sta_netmask[SettingsManager::Settings::kIPAddrStrLen] = '\0';
            snprintf(wifi_sta_gateway, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->gw));
            wifi_sta_gateway[SettingsManager::Settings::kIPAddrStrLen] = '\0';

            CONSOLE_INFO("CommsManager::WiFiIPEventHandler",
                         "WiFi Station got IP Address. IP: %s, Netmask: %s, Gateway: %s", wifi_sta_ip, wifi_sta_netmask,
                         wifi_sta_gateway);
            break;
        }
        case IP_EVENT_ETH_GOT_IP: {
            // The ADSBee's Ethernet interface has connected to an external network.
            ip_event_got_ip_t* event = (ip_event_got_ip_t*)event_data;
            const esp_netif_ip_info_t* ip_info = &event->ip_info;

            ethernet_has_ip_ = true;
            snprintf(ethernet_ip, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->ip));
            ethernet_ip[SettingsManager::Settings::kIPAddrStrLen] = '\0';
            snprintf(ethernet_netmask, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->netmask));
            ethernet_netmask[SettingsManager::Settings::kIPAddrStrLen] = '\0';
            snprintf(ethernet_gateway, SettingsManager::Settings::kIPAddrStrLen, IPSTR, IP2STR(&ip_info->gw));
            ethernet_gateway[SettingsManager::Settings::kIPAddrStrLen] = '\0';

            CONSOLE_INFO("CommsManager::EthernetIPEventHandler",
                         "Ethernet got IP address. IP: %s, Netmask: %s, Gateway: %s", ethernet_ip, ethernet_netmask,
                         ethernet_gateway);
            break;
        }
        case IP_EVENT_ETH_LOST_IP: {
            // The ADSBee's Ethernet interface has disconnected from an external network.
            ethernet_has_ip_ = false;
            CONSOLE_INFO("CommsManager::EthernetIPEventHandler", "Ethernet lost IP address.");
            break;
        }
    }
}

void CommsManager::IPWANTask(void* pvParameters) {
    DecodedTransponderPacket decoded_packet;

    int feed_sock[SettingsManager::Settings::kMaxNumFeeds] = {0};
    bool feed_sock_is_connected[SettingsManager::Settings::kMaxNumFeeds] = {false};
    uint32_t feed_sock_last_connect_timestamp_ms[SettingsManager::Settings::kMaxNumFeeds] = {0};

    CONSOLE_INFO("CommsManager::IPWANTask", "IP WAN Task started.");

    while (true) {
        // Don't try establishing socket connections until the ESP32 has been assigned an IP address.
        while (!wifi_sta_has_ip_ && !ethernet_has_ip_) {
            vTaskDelay(1);  // Delay for 1 tick.
        }

        // Update feed statistics once per second and print them. Put this before the queue receive so that it runs even
        // if no packets are received.
        static const uint16_t kStatsMessageMaxLen = 500;
        uint32_t timestamp_ms = get_time_since_boot_ms();
        if (timestamp_ms - feed_mps_last_update_timestamp_ms_ > kMsPerSec) {
            for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
                feed_mps[i] = feed_mps_counter_[i];
                feed_mps_counter_[i] = 0;
            }
            feed_mps_last_update_timestamp_ms_ = timestamp_ms;

            char feeds_stats_message[kStatsMessageMaxLen] = {'\0'};

            for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
                char single_feed_stats_message[kStatsMessageMaxLen / SettingsManager::Settings::kMaxNumFeeds] = {'\0'};
                snprintf(single_feed_stats_message, kStatsMessageMaxLen / SettingsManager::Settings::kMaxNumFeeds,
                         "%d:[%d] ", i, feed_mps[i]);
                strcat(feeds_stats_message, single_feed_stats_message);
            }
            CONSOLE_INFO("CommsManager::IPWANTask", "Feed msgs/s: %s", feeds_stats_message);
        }

        // Gather packet(s) to send.
        if (xQueueReceive(ip_wan_decoded_transponder_packet_queue_, &decoded_packet,
                          kWiFiSTATaskUpdateIntervalTicks) != pdTRUE) {
            // No packets available to send, wait and try again.
            continue;
        }

        // NOTE: Construct packets that are shared between feeds here!

        for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
            // Iterate through feeds, open/close and send message as required.
            if (!settings_manager.settings.feed_is_active[i]) {
                // Socket should not be fed.
                if (feed_sock_is_connected[i]) {
                    // Need to close the socket connection.
                    close(feed_sock[i]);
                    feed_sock_is_connected[i] = false;
                    CONSOLE_INFO("CommsManager::IPWANTask", "Closed socket for feed %d.", i);
                }
                continue;  // Don't need to do anything else if socket should be closed and is closed.
            }

            // Socket should be open.
            if (!feed_sock_is_connected[i]) {
                // Need to open the socket connection.

                // Meter reconnect attempt interval.
                uint32_t timestamp_ms = get_time_since_boot_ms();
                if (timestamp_ms - feed_sock_last_connect_timestamp_ms[i] <= kWiFiTCPSocketReconnectIntervalMs) {
                    continue;
                }
                feed_sock_last_connect_timestamp_ms[i] = timestamp_ms;

                // Create socket.
                // IPv4, TCP
                feed_sock[i] = socket(AF_INET, SOCK_STREAM, IPPROTO_IP);
                if (feed_sock[i] <= 0) {
                    CONSOLE_ERROR("CommsManager::IPWANTask", "Unable to create socket for feed %d: errno %d", i, errno);
                    continue;
                }
                CONSOLE_INFO("CommsManager::IPWANTask", "Socket for feed %d created, connecting to %s:%d", i,
                             settings_manager.settings.feed_uris[i], settings_manager.settings.feed_ports[i]);

                struct sockaddr_in dest_addr;
                // If the URI contains letters, resolve it to an IP address
                if (IsNotIPAddress(settings_manager.settings.feed_uris[i])) {
                    // Is not an IP address, try DNS resolution.
                    char resolved_ip[16];
                    if (!ResolveURIToIP(settings_manager.settings.feed_uris[i], resolved_ip)) {
                        CONSOLE_ERROR("CommsManager::IPWANTask", "Failed to resolve URL %s for feed %d",
                                      settings_manager.settings.feed_uris[i], i);
                        close(feed_sock[i]);
                        feed_sock_is_connected[i] = false;
                        continue;
                    }
                    inet_pton(AF_INET, resolved_ip, &dest_addr.sin_addr);
                } else {
                    // Is an IP address, use it directly.
                    inet_pton(AF_INET, settings_manager.settings.feed_uris[i], &dest_addr.sin_addr);
                }

                dest_addr.sin_family = AF_INET;
                dest_addr.sin_port = htons(settings_manager.settings.feed_ports[i]);

                int err = connect(feed_sock[i], (struct sockaddr*)&dest_addr, sizeof(dest_addr));
                if (err != 0) {
                    CONSOLE_ERROR(
                        "CommsManager::IPWANTask", "Socket unable to connect to URI %s:%d for feed %d: errno %d",
                        settings_manager.settings.feed_uris[i], settings_manager.settings.feed_ports[i], i, errno);
                    close(feed_sock[i]);
                    feed_sock_is_connected[i] = false;
                    continue;
                }
                CONSOLE_INFO("CommsManager::IPWANTask", "Successfully connected to %s",
                             settings_manager.settings.feed_uris[i]);
                feed_sock_is_connected[i] = true;
            }

            // Send packet!
            // NOTE: Construct packets that are specific to a feed in case statements here!
            switch (settings_manager.settings.feed_protocols[i]) {
                case SettingsManager::ReportingProtocol::kBeast:
                    if (!decoded_packet.IsValid()) {
                        // Packet is invalid, don't send.
                        break;
                    }
                    [[fallthrough]];  // Intentional cascade into BEAST_RAW, since reporting code is shared.
                case SettingsManager::ReportingProtocol::kBeastRaw: {
                    // Send Beast packet.
                    // Double the length as a hack to make room for the escaped UUID.
                    uint8_t beast_message_buf[2 * SettingsManager::Settings::kFeedReceiverIDNumBytes +
                                              kBeastFrameMaxLenBytes];
                    uint16_t beast_message_len_bytes = TransponderPacketToBeastFramePrependReceiverID(
                        decoded_packet, beast_message_buf, settings_manager.settings.feed_receiver_ids[i],
                        SettingsManager::Settings::kFeedReceiverIDNumBytes);

                    int err = send(feed_sock[i], beast_message_buf, beast_message_len_bytes, 0);
                    if (err < 0) {
                        CONSOLE_ERROR("CommsManager::IPWANTask",
                                      "Error occurred during sending %d Byte beast message to feed %d with URI %s "
                                      "on port %d: "
                                      "errno %d.",
                                      beast_message_len_bytes, i, settings_manager.settings.feed_uris[i],
                                      settings_manager.settings.feed_ports[i], errno);
                        // Mark socket as disconnected and try reconnecting in next reporting interval.
                        close(feed_sock[i]);
                        feed_sock_is_connected[i] = false;
                    } else {
                        // CONSOLE_INFO("CommsManager::IPWANTask", "Message sent to feed %d.", i);
                        feed_mps_counter_[i]++;  // Log that a message was sent in statistics.
                    }
                    break;
                }
                // TODO: add other protocols here
                default:
                    // No reporting protocol or unsupported protocol: do nothing.
                    break;
            }
        }
    }

    // Close all sockets while exiting.
    for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
        if (feed_sock_is_connected[i]) {
            // Need to close the socket connection.
            close(feed_sock[i]);
            feed_sock_is_connected[i] = false;  // Not necessary but leaving this here in case of refactor.
        }
    }

    CONSOLE_INFO("CommsManager::IPWANTask", "IP WAN Task exiting.");
}