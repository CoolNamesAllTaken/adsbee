// NimBLE observer for Broadcast Remote ID (ASTM F3411) over Bluetooth LE.
//
// Scans (passively) on both the 1M PHY (BT4 legacy advertising) and, when requested and supported, the Coded PHY (BT5
// Long Range) using BLE 5 extended discovery. Advertisements are filtered for the ASTM Remote ID Service Data (16-bit
// UUID 0xFFFA, application code 0x0D); the enclosed Open Drone ID message / message pack bytes are handed to
// RemoteIDManager::OnRawRemoteIDPacket().
//
// The whole file compiles to no-ops when Bluetooth/NimBLE is not built into the firmware (e.g. a WiFi-only image), so
// RemoteIDManager reports kStatusNotInBuild instead of failing to link.

#include "remote_id_manager.hh"
#include "sdkconfig.h"

#if defined(CONFIG_BT_ENABLED) && defined(CONFIG_BT_NIMBLE_ENABLED)

#include <cstring>

#include "comms.hh"  // Logging.
#include "hal.hh"    // get_time_since_boot_ms.
#include "host/ble_gap.h"
#include "host/ble_hs.h"
#include "nimble/nimble_port.h"
#include "nimble/nimble_port_freertos.h"

namespace {

// ASTM Remote ID Bluetooth framing constants.
constexpr uint16_t kRemoteIDServiceUUID16 = 0xFFFA;
constexpr uint8_t kRemoteIDAppCode = 0x0D;  // "ODID" AD application code.
// Within an AD element's data: [UUID lo][UUID hi][app code][message counter][ODID message/pack ...].
constexpr uint8_t kODIDPayloadOffsetInSvcData = 4;

constexpr uint8_t kAdvTypeServiceData16 = 0x16;  // BLE_HS_ADV_TYPE_SVC_DATA_UUID16.

bool s_ble_initialized = false;
bool s_scanning = false;
bool s_want_coded = false;

// Extract the ODID payload from an advertisement's AD structures and hand it to the manager. Returns true if a Remote ID
// service data element was found and forwarded.
bool ParseAndForward(const uint8_t* adv_data, uint8_t adv_len, const uint8_t* mac, int8_t rssi,
                     RawRemoteIDPacket::Transport transport) {
    uint8_t i = 0;
    while (i + 1 < adv_len) {
        uint8_t elem_len = adv_data[i];
        if (elem_len == 0) break;
        if (i + 1 + elem_len > adv_len) break;  // Malformed length.
        uint8_t elem_type = adv_data[i + 1];
        const uint8_t* elem_data = &adv_data[i + 2];
        uint8_t elem_data_len = elem_len - 1;

        if (elem_type == kAdvTypeServiceData16 && elem_data_len >= kODIDPayloadOffsetInSvcData) {
            uint16_t uuid = (uint16_t)elem_data[0] | ((uint16_t)elem_data[1] << 8);
            if (uuid == kRemoteIDServiceUUID16 && elem_data[2] == kRemoteIDAppCode) {
                uint8_t odid_len = elem_data_len - kODIDPayloadOffsetInSvcData;
                if (odid_len > 0 && odid_len <= RawRemoteIDPacket::kMaxPayloadLenBytes) {
                    RawRemoteIDPacket packet;
                    packet.received_timestamp_ms = get_time_since_boot_ms();
                    memcpy(packet.source_mac, mac, 6);
                    packet.rssi_dbm = rssi;
                    packet.transport = transport;
                    packet.payload_len_bytes = odid_len;
                    memcpy(packet.payload, &elem_data[kODIDPayloadOffsetInSvcData], odid_len);
                    remote_id_manager.OnRawRemoteIDPacket(packet);
                    return true;
                }
            }
        }
        i += 1 + elem_len;
    }
    return false;
}

int GapEventHandler(struct ble_gap_event* event, void* arg) {
    switch (event->type) {
        case BLE_GAP_EVENT_EXT_DISC: {
            const struct ble_gap_ext_disc_desc* d = &event->ext_disc;
            // Coded PHY (secondary) indicates a BT5 Long Range advertisement.
            RawRemoteIDPacket::Transport transport = (d->sec_phy == BLE_HCI_LE_PHY_CODED)
                                                         ? RawRemoteIDPacket::kTransportBT5LongRange
                                                         : RawRemoteIDPacket::kTransportBT4Legacy;
            ParseAndForward(d->data, d->length_data, d->addr.val, d->rssi, transport);
            return 0;
        }
        default:
            return 0;
    }
}

void StartExtDiscovery() {
    // Passive scan, no duplicate filtering (Location updates repeat with the same AD structure; the manager de-dups).
    // window < itvl leaves an ~20% idle slice each interval so that, under WiFi/BLE software coexistence, the coex
    // arbiter has BLE-idle time to schedule the WiFi promiscuous sniffer's RX (an unassociated WiFi is otherwise treated
    // as IDLE and starved by BLE). At 80% duty with a 100 ms interval, BLE still catches the ~1 Hz Remote ID adverts
    // easily, so this costs BLE-only capture nothing meaningful. This keeps BLE the priority transport, WiFi best-effort.
    struct ble_gap_ext_disc_params uncoded = {};
    uncoded.itvl = 160;    // 100 ms scan interval (units of 0.625 ms).
    uncoded.window = 128;  // 80 ms scan window -> ~80% duty, ~20% left for the WiFi sniffer under coexistence.
    uncoded.passive = 1;

    struct ble_gap_ext_disc_params coded = uncoded;

    uint8_t own_addr_type = BLE_OWN_ADDR_PUBLIC;
    int rc = ble_gap_ext_disc(own_addr_type, /*duration=*/0, /*period=*/0, /*filter_duplicates=*/0,
                              /*filter_policy=*/BLE_HCI_SCAN_FILT_NO_WL, /*limited=*/0, &uncoded,
                              s_want_coded ? &coded : nullptr, GapEventHandler, nullptr);
    if (rc != 0) {
        CONSOLE_ERROR("remote_id_ble", "ble_gap_ext_disc failed, rc=%d.", rc);
        s_scanning = false;
    } else {
        s_scanning = true;
    }
}

void OnHostSync() {
    // Controller/host are in sync; safe to start scanning.
    StartExtDiscovery();
}

void HostTask(void* param) {
    nimble_port_run();  // Runs until nimble_port_stop().
    nimble_port_freertos_deinit();
}

}  // namespace

bool RemoteIDManager::BLEStart(bool enable_coded_phy) {
    s_want_coded = enable_coded_phy;
    if (ble_running_) {
        // Already running: if the coded-PHY request changed, restart discovery with the new parameters.
        if (s_scanning && ble_coded_running_ != enable_coded_phy) {
            ble_gap_disc_cancel();
            StartExtDiscovery();
        }
        ble_coded_running_ = enable_coded_phy;
        return true;
    }

    if (!s_ble_initialized) {
        esp_err_t err = nimble_port_init();
        if (err != ESP_OK) {
            CONSOLE_ERROR("remote_id_ble", "nimble_port_init failed: %d.", err);
            return false;
        }
        ble_hs_cfg.sync_cb = OnHostSync;
        nimble_port_freertos_init(HostTask);
        s_ble_initialized = true;
    } else {
        // Host already initialized (e.g. toggled off then on): just restart discovery.
        StartExtDiscovery();
    }

    ble_running_ = true;
    ble_coded_running_ = enable_coded_phy;
    return true;
}

void RemoteIDManager::BLEStop() {
    if (!ble_running_) return;
    if (s_scanning) {
        ble_gap_disc_cancel();
        s_scanning = false;
    }
    // We intentionally leave the NimBLE host/controller initialized (tearing it down and back up is expensive and
    // error-prone); scanning is stopped, which is what frees the radio. Full de-init would follow the esp_restart()
    // pattern used elsewhere if a hard teardown were ever required.
    ble_running_ = false;
    ble_coded_running_ = false;
}

#else  // Bluetooth not compiled in: no-op stubs so RemoteIDManager links and reports kStatusNotInBuild.

bool RemoteIDManager::BLEStart(bool) { return false; }
void RemoteIDManager::BLEStop() {}

#endif  // CONFIG_BT_ENABLED && CONFIG_BT_NIMBLE_ENABLED
