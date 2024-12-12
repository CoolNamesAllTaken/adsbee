#include "comms.hh"
#include "esp_event.h"
#include "esp_mac.h"

/** "Pass-Through" functions used to access member functions in callbacks. **/
void ip_event_handler(void* arg, esp_event_base_t event_base, int32_t event_id, void* event_data) {
    comms_manager.IPEventHandler(arg, event_base, event_id, event_data);
}
/** End "Pass-Through" functions. **/

bool CommsManager::IPInit() {
    ESP_ERROR_CHECK(esp_event_handler_register(IP_EVENT, ESP_EVENT_ANY_ID, &ip_event_handler, NULL));
    ip_event_handler_was_initialized_ = true;
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