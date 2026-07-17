// WiFi promiscuous sniffer for Broadcast Remote ID (ASTM F3411) over WiFi beacon frames.
//
// Used only on the internal-RAM (non-PSRAM) build when WiFi AP/STA are disabled: the WiFi radio is repurposed as a
// channel-hopping (1/6/11) sniffer while Ethernet carries IP. The driver is brought up in NULL mode with trimmed RX
// buffers and promiscuous mode enabled; beacon frames are scanned for the Open Drone ID vendor-specific IE
// (OUI FA:0B:BC, type 0x0D) and the enclosed message pack is handed to RemoteIDManager::OnRawRemoteIDPacket().
//
// On the PSRAM coexist build the radio is locked to the AP/STA channel; channel-locked best-effort sniffing there is
// left as future work (RemoteIDManager does not start the sniffer while WiFi AP/STA are up).

#include "remote_id_manager.hh"

#include <cstring>

#include "comms.hh"  // Logging.
#include "esp_wifi.h"
#include "hal.hh"  // get_time_since_boot_ms.

namespace {

// Open Drone ID WiFi vendor-specific IE framing.
constexpr uint8_t kElementIdVendorSpecific = 0xDD;
constexpr uint8_t kODIDOui[3] = {0xFA, 0x0B, 0xBC};
constexpr uint8_t kODIDOuiType = 0x0D;
// Within a vendor IE's data: [OUI(3)][OUI type(1)][message counter(1)][ODID message pack ...].
constexpr uint8_t kODIDPayloadOffsetInIE = 5;

// 802.11 management frame beacon layout offsets.
constexpr uint8_t kBeaconSAOffset = 10;         // addr2 (source address) in the MAC header.
constexpr uint8_t kBeaconTaggedParamsOffset = 36;  // 24-byte MAC header + 12-byte fixed beacon params.
constexpr uint16_t kBeaconSubtype = 0x0080;      // Frame control type=mgmt(0), subtype=beacon(8).
constexpr uint16_t kFrameControlTypeSubtypeMask = 0x00FC;

bool s_sniffer_running = false;

void PromiscuousRxCb(void* buf, wifi_promiscuous_pkt_type_t type) {
    if (type != WIFI_PKT_MGMT) return;
    const wifi_promiscuous_pkt_t* pkt = static_cast<const wifi_promiscuous_pkt_t*>(buf);
    const uint8_t* frame = pkt->payload;
    uint16_t frame_len = pkt->rx_ctrl.sig_len;
    if (frame_len < kBeaconTaggedParamsOffset) return;

    uint16_t frame_control = (uint16_t)frame[0] | ((uint16_t)frame[1] << 8);
    if ((frame_control & kFrameControlTypeSubtypeMask) != kBeaconSubtype) return;  // Beacons only.

    const uint8_t* sa = &frame[kBeaconSAOffset];

    // Walk the tagged parameters (Information Elements) looking for the ODID vendor-specific IE.
    uint16_t i = kBeaconTaggedParamsOffset;
    while (i + 2 <= frame_len) {
        uint8_t element_id = frame[i];
        uint8_t ie_len = frame[i + 1];
        const uint8_t* ie_data = &frame[i + 2];
        if (i + 2 + ie_len > frame_len) break;  // Truncated IE.

        if (element_id == kElementIdVendorSpecific && ie_len >= kODIDPayloadOffsetInIE &&
            memcmp(ie_data, kODIDOui, sizeof(kODIDOui)) == 0 && ie_data[3] == kODIDOuiType) {
            uint8_t odid_len = ie_len - kODIDPayloadOffsetInIE;
            if (odid_len > 0 && odid_len <= RawRemoteIDPacket::kMaxPayloadLenBytes) {
                RawRemoteIDPacket packet;
                packet.received_timestamp_ms = get_time_since_boot_ms();
                memcpy(packet.source_mac, sa, 6);
                packet.rssi_dbm = pkt->rx_ctrl.rssi;
                packet.transport = RawRemoteIDPacket::kTransportWiFiBeacon;
                packet.channel = pkt->rx_ctrl.channel;
                packet.payload_len_bytes = odid_len;
                memcpy(packet.payload, &ie_data[kODIDPayloadOffsetInIE], odid_len);
                remote_id_manager.OnRawRemoteIDPacket(packet);
            }
            return;
        }
        i += 2 + ie_len;
    }
}

}  // namespace

bool RemoteIDManager::WiFiSnifferStart() {
    if (wifi_sniffer_running_) return true;

    // Bring up the WiFi driver in NULL mode (no AP/STA association) with trimmed RX buffers to conserve internal RAM.
    wifi_init_config_t cfg = WIFI_INIT_CONFIG_DEFAULT();
    cfg.static_rx_buf_num = 4;
    cfg.dynamic_rx_buf_num = 8;
    cfg.ampdu_rx_enable = 0;

    esp_err_t err = esp_wifi_init(&cfg);
    if (err != ESP_OK) {
        CONSOLE_ERROR("remote_id_wifi", "esp_wifi_init failed: %d.", err);
        return false;
    }
    if ((err = esp_wifi_set_storage(WIFI_STORAGE_RAM)) != ESP_OK ||
        (err = esp_wifi_set_mode(WIFI_MODE_NULL)) != ESP_OK || (err = esp_wifi_start()) != ESP_OK) {
        CONSOLE_ERROR("remote_id_wifi", "WiFi NULL-mode bring-up failed: %d.", err);
        esp_wifi_deinit();
        return false;
    }

    wifi_promiscuous_filter_t filter = {.filter_mask = WIFI_PROMIS_FILTER_MASK_MGMT};
    esp_wifi_set_promiscuous_filter(&filter);
    esp_wifi_set_promiscuous_rx_cb(&PromiscuousRxCb);
    if ((err = esp_wifi_set_promiscuous(true)) != ESP_OK) {
        CONSOLE_ERROR("remote_id_wifi", "esp_wifi_set_promiscuous failed: %d.", err);
        esp_wifi_stop();
        esp_wifi_deinit();
        return false;
    }

    sniffer_channel_index_ = 0;
    esp_wifi_set_channel(kSnifferChannels[0], WIFI_SECOND_CHAN_NONE);
    last_channel_hop_ms_ = get_time_since_boot_ms();
    wifi_sniffer_running_ = true;
    s_sniffer_running = true;
    CONSOLE_INFO("remote_id_wifi", "Remote ID WiFi sniffer started (channels 1/6/11).");
    return true;
}

void RemoteIDManager::WiFiSnifferStop() {
    if (!wifi_sniffer_running_) return;
    esp_wifi_set_promiscuous(false);
    esp_wifi_stop();
    esp_wifi_deinit();
    wifi_sniffer_running_ = false;
    s_sniffer_running = false;
}

void RemoteIDManager::WiFiSnifferServiceHopper() {
    uint32_t now_ms = get_time_since_boot_ms();
    if (now_ms - last_channel_hop_ms_ < kSnifferChannelDwellMs) return;
    sniffer_channel_index_ = (sniffer_channel_index_ + 1) % (sizeof(kSnifferChannels) / sizeof(kSnifferChannels[0]));
    esp_wifi_set_channel(kSnifferChannels[sniffer_channel_index_], WIFI_SECOND_CHAN_NONE);
    last_channel_hop_ms_ = now_ms;
}
