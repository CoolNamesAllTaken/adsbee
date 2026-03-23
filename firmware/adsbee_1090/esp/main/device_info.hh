#ifndef DEVICE_INFO_HH_
#define DEVICE_INFO_HH_

#include "esp_check.h"
#include "object_dictionary.hh"

inline ObjectDictionary::ESP32DeviceInfo GetESP32DeviceInfo() {
    ObjectDictionary::ESP32DeviceInfo device_info;
    // Get Base MAC address as well as WiFi Station and AP MAC addresses.
    ESP_ERROR_CHECK(esp_efuse_mac_get_default(device_info.base_mac));
    memcpy(device_info.wifi_station_mac, device_info.base_mac, ObjectDictionary::kMACAddrLenBytes);
    // WiFi station MAC is same as base MAC.
    memcpy(device_info.wifi_ap_mac, device_info.base_mac, ObjectDictionary::kMACAddrLenBytes);
    device_info.wifi_ap_mac[5] += 1;  // WiFi AP MAC is base MAC + 1 to the last octet.
    memcpy(device_info.bluetooth_mac, device_info.base_mac, ObjectDictionary::kMACAddrLenBytes);
    device_info.bluetooth_mac[5] += 2;  // Bluetooth MAC is base MAC + 2 to the last octet.
    memcpy(device_info.ethernet_mac, device_info.base_mac, ObjectDictionary::kMACAddrLenBytes);
    device_info.ethernet_mac[5] += 3;  // Ethernet MAC is base MAC + 3 to the last octet.

    // These functions don't work until everything is up and running.
    // esp_read_mac(device_info.base_mac, ESP_MAC_WIFI_STA);
    // esp_read_mac(device_info.wifi_station_mac, ESP_MAC_WIFI_STA);
    // esp_read_mac(device_info.wifi_ap_mac, ESP_MAC_WIFI_SOFTAP);
    // esp_read_mac(device_info.bluetooth_mac, ESP_MAC_BT);
    // esp_read_mac(device_info.ethernet_mac, ESP_MAC_ETH);
    return device_info;
}

#endif /* DEVICE_INFO_HH_ */
