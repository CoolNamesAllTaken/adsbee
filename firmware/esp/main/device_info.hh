#ifndef DEVICE_INFO_HH_
#define DEVICE_INFO_HH_

#include "esp_check.h"
#include "object_dictionary.hh"

inline ObjectDictionary::ESP32DeviceInfo GetESP32DeviceInfo() {
    ObjectDictionary::ESP32DeviceInfo device_info;
    // Get Base MAC address as well as WiFi Station and AP MAC addresses.
    ESP_ERROR_CHECK(esp_efuse_mac_get_default(device_info.base_mac));
    memcpy(device_info.wifi_station_mac, device_info.base_mac, ObjectDictionary::kMACAddrLenBytes);
    memcpy(device_info.wifi_ap_mac, device_info.base_mac, ObjectDictionary::kMACAddrLenBytes);
    device_info.wifi_ap_mac[5] += 1;  // WiFi AP MAC is base MAC + 1 to the last octet.
    // ESP_ERROR_CHECK(esp_wifi_get_mac(WIFI_IF_STA, device_info.wifi_station_mac));  // base mac.
    // ESP_ERROR_CHECK(esp_wifi_get_mac(WIFI_IF_AP, device_info.wifi_ap_mac));        // base+1 to last octet.
    // Calculate the remaining (BT + Ethernet) MAC addresses from base MAC.
    memcpy(device_info.bluetooth_mac, device_info.base_mac, ObjectDictionary::kMACAddrLenBytes);
    device_info.bluetooth_mac[5] += 2;  // Bluetooth MAC is base MAC + 2 to the last octet.
    memcpy(device_info.ethernet_mac, device_info.base_mac, ObjectDictionary::kMACAddrLenBytes);
    device_info.ethernet_mac[5] += 3;  // Ethernet MAC is base MAC + 3 to the last octet.

    // esp_read_mac(device_info.base_mac, ESP_MAC_WIFI_STA);
    // esp_read_mac(device_info.wifi_station_mac, ESP_MAC_WIFI_STA);
    // esp_read_mac(device_info.wifi_ap_mac, ESP_MAC_WIFI_SOFTAP);
    // esp_read_mac(device_info.bluetooth_mac, ESP_MAC_BT);
    // esp_read_mac(device_info.ethernet_mac, ESP_MAC_ETH);
    return device_info;
}

#endif /* DEVICE_INFO_HH_ */
