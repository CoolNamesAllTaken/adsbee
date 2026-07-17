#include "remote_id_manager.hh"

#include <cstring>

#include "comms.hh"                 // comms_manager (WiFi/Ethernet state) + logging.
#include "data_structures.hh"       // PFBQueue.
#include "esp_heap_caps.h"          // heap_caps_get_free_size.
#include "hal.hh"                   // get_time_since_boot_ms.
#include "object_dictionary.hh"     // object_dictionary.device_status.remote_id_status.
#include "sdkconfig.h"              // CONFIG_SPIRAM / CONFIG_BT_* feature flags.
#include "server/adsbee_server.hh"  // adsbee_server: local dictionary + RP2040 out-queue.

RemoteIDManager remote_id_manager;

// Thread-safe hand-off queue from the BLE host task / WiFi promiscuous callback (producers) to the main task
// (consumer, ServiceIngestQueue). Kept as a file-scope static so the header doesn't need to pull in PFBQueue.
static constexpr uint16_t kIngestQueueDepth = 32;
static RawRemoteIDPacket s_ingest_queue_buffer[kIngestQueueDepth];
static PFBQueue<RawRemoteIDPacket> s_ingest_queue = PFBQueue<RawRemoteIDPacket>({
    .buf_len_num_elements = kIngestQueueDepth,
    .buffer = s_ingest_queue_buffer,
    .overwrite_when_full = true,  // Drop oldest under a burst rather than block the radio callback.
    .is_thread_safe = true,
});

bool RemoteIDManager::CanCoexistWithWiFi() {
#ifdef CONFIG_SPIRAM
    return true;  // PSRAM build: NimBLE host heap + LWIP/WiFi buffers live in PSRAM, so BLE can coexist with WiFi AP/STA.
#else
    return false;  // Internal-RAM-only build: not enough SRAM to run WiFi AP/STA and the BLE stack simultaneously.
#endif
}

void RemoteIDManager::OnRawRemoteIDPacket(const RawRemoteIDPacket& packet) {
    // Runs in the NimBLE host task or the WiFi promiscuous callback. Keep it minimal: just enqueue.
    s_ingest_queue.Enqueue(packet);
}

RemoteIDManager::DedupEntry* RemoteIDManager::FindOrAllocDedupEntry(const uint8_t mac[6]) {
    DedupEntry* free_slot = nullptr;
    uint32_t oldest_ms = UINT32_MAX;
    DedupEntry* oldest_slot = &dedup_table_[0];
    for (auto& entry : dedup_table_) {
        if (entry.in_use && memcmp(entry.mac, mac, 6) == 0) {
            return &entry;
        }
        if (!entry.in_use && free_slot == nullptr) {
            free_slot = &entry;
        }
        uint32_t recent = entry.last_location_forward_ms > entry.last_static_forward_ms
                              ? entry.last_location_forward_ms
                              : entry.last_static_forward_ms;
        if (recent < oldest_ms) {
            oldest_ms = recent;
            oldest_slot = &entry;
        }
    }
    // Not found: reuse a free slot, else evict the least-recently-forwarded transmitter.
    DedupEntry* slot = free_slot ? free_slot : oldest_slot;
    slot->in_use = true;
    memcpy(slot->mac, mac, 6);
    slot->last_location_forward_ms = 0;
    slot->last_static_forward_ms = 0;
    return slot;
}

bool RemoteIDManager::ShouldForwardToRP2040(const RawRemoteIDPacket& packet) {
    // Determine whether this advertisement carries dynamic (Location/Vector) data, which we forward at up to 1 Hz, vs
    // static identity data, which we forward at most every 10 s. We only need a coarse classification here; the RP2040
    // decodes the full content. A message pack always contains a Location, so treat packs as dynamic. For a single
    // message, the message type is the high nibble of the first ODID byte: type 1 == Location/Vector.
    bool is_dynamic = packet.GetIsMessagePack() ||
                      (packet.payload_len_bytes > 0 && (packet.payload[0] >> 4) == 0x1 /* ODID_MESSAGETYPE_LOCATION */);

    uint32_t now_ms = get_time_since_boot_ms();
    DedupEntry* entry = FindOrAllocDedupEntry(packet.source_mac);
    if (is_dynamic) {
        if (now_ms - entry->last_location_forward_ms < kLocationForwardIntervalMs) return false;
        entry->last_location_forward_ms = now_ms;
        return true;
    }
    if (now_ms - entry->last_static_forward_ms < kStaticForwardIntervalMs) return false;
    entry->last_static_forward_ms = now_ms;
    return true;
}

uint16_t RemoteIDManager::ServiceIngestQueue() {
    // Runs on the main task (ADSBeeServer::Update), so it is the only mutator of the aircraft dictionary and the RP2040
    // out-queue from this path.
    uint16_t num_processed = 0;
    RawRemoteIDPacket packet;
    while (s_ingest_queue.Dequeue(packet)) {
        num_processed++;
        // Always ingest locally (cheap) — this drives the ESP32's network/web output.
        adsbee_server.aircraft_dictionary.IngestRawRemoteIDPacket(packet);
        // Forward a rate-limited copy up to the RP2040 for serial reporting.
        if (ShouldForwardToRP2040(packet)) {
            adsbee_server.raw_remote_id_packet_out_queue.Enqueue(packet);
        }
    }
    return num_processed;
}

void RemoteIDManager::Reconcile() {
    status_ = 0;

    if (!settings_manager.settings.remote_id_rx_enabled) {
        BLEStop();
        WiFiSnifferStop();
        return;
    }

    const uint8_t transports = settings_manager.settings.remote_id_transports;
    const bool want_ble = transports & (SettingsManager::kRemoteIDTransportBLE4 | SettingsManager::kRemoteIDTransportBLE5Long);
    const bool want_coded = transports & SettingsManager::kRemoteIDTransportBLE5Long;
    const bool want_wifi = transports & SettingsManager::kRemoteIDTransportWiFiBeacon;

    const bool wifi_ap_sta_up =
        comms_manager.wifi_ap_enabled || comms_manager.wifi_sta_enabled;

    // On non-PSRAM builds, Remote ID may only run when WiFi AP/STA are off (and Ethernet is carrying IP).
    if (wifi_ap_sta_up && !CanCoexistWithWiFi()) {
        status_ |= kStatusBlockedByWiFi;
        BLEStop();
        WiFiSnifferStop();
        return;
    }

    // Heap guard: don't start the BLE/WiFi stacks if we're already low on internal RAM.
    if (heap_caps_get_free_size(MALLOC_CAP_8BIT) < kMinHeapFreeBytesToStart && !ble_running_ && !wifi_sniffer_running_) {
        status_ |= kStatusBlockedByRAM;
        return;
    }

    // --- BLE ---
    if (want_ble) {
        if (BLEStart(want_coded)) {
            status_ |= kStatusBLEActive;
            if (ble_coded_running_) status_ |= kStatusBLECodedPHYActive;
        } else {
            status_ |= kStatusNotInBuild;  // BLEStart only fails to no-op when Bluetooth isn't compiled in.
        }
    } else {
        BLEStop();
    }

    // --- WiFi beacon sniffer ---
    // The channel-hopping sniffer is only meaningful when WiFi is not otherwise in use (non-coexist path). On the PSRAM
    // coexist path the radio is locked to the AP/STA channel, so we leave beacon sniffing to a future channel-locked
    // best-effort mode and do not hop here.
    if (want_wifi && !wifi_ap_sta_up) {
        if (WiFiSnifferStart()) {
            status_ |= kStatusWiFiSnifferActive;
        }
    } else {
        WiFiSnifferStop();
    }
}

void RemoteIDManager::Apply() {
    Reconcile();
    // Publish the resolved status so the RP2040 can surface it via AT+REMOTE_ID?.
    object_dictionary.device_status.remote_id_status = status_;
}

void RemoteIDManager::Update() {
    if (wifi_sniffer_running_) {
        WiFiSnifferServiceHopper();
    }
    object_dictionary.device_status.remote_id_status = status_;
}
