#pragma once

#include <cstdint>

#include "remote_id_packet.hh"
#include "settings.hh"

/**
 * RemoteIDManager orchestrates Broadcast Remote ID (ASTM F3411) reception on the ESP32-S3.
 *
 * It decides which transports can actually run given (a) the user's settings, (b) the hardware build (PSRAM lets Remote
 * ID coexist with WiFi AP/STA; without PSRAM, RAM only allows Remote ID when WiFi is off and Ethernet carries IP), and
 * (c) live heap headroom. It brings up the BLE (NimBLE) observer and, on capable configurations, the WiFi promiscuous
 * sniffer; both feed a single de-duplication / rate-limiting stage before packets are ingested locally and forwarded to
 * the RP2040.
 *
 * Wiring:
 *   - Received advertisements are parsed to raw ODID bytes and handed to OnRawRemoteIDPacket() (from the NimBLE host
 *     task or the WiFi promiscuous callback).
 *   - OnRawRemoteIDPacket() always ingests into the ESP32's local AircraftDictionary (drives network output) and, after
 *     rate-limiting, enqueues a copy into ADSBeeServer::raw_remote_id_packet_out_queue for the RP2040 to pull.
 *   - Apply() is called from SettingsManager::Apply() (esp/main/settings.cpp) after the WiFi/Ethernet interfaces are
 *     (re)configured, so it sees the resolved network state.
 *   - GetStatus() feeds ObjectDictionary::ESP32DeviceStatus::remote_id_status so the RP2040 can explain the live state.
 */
class RemoteIDManager {
   public:
    // Heap guard: refuse to start (or keep) a transport if free internal 8-bit heap would drop below this. Remote ID is
    // a best-effort add-on and must never starve the network stack (whose back-pressure trips around 20 KB, see
    // comms_ip.cpp::safe_send).
    static constexpr uint32_t kMinHeapFreeBytesToStart = 60 * 1024;

    // Per-source rate limiting for SPI forwarding to the RP2040. Local dictionary ingest is not rate limited.
    static constexpr uint32_t kLocationForwardIntervalMs = 1000;  // Location/Vector: at most 1 Hz per source.
    static constexpr uint32_t kStaticForwardIntervalMs = 10000;   // Static messages: at most every 10 s per source.
    static constexpr uint16_t kDedupTableNumEntries = 24;         // Tracked simultaneous transmitters for rate limiting.

    // WiFi sniffer channel hop set (US: 1/6/11 carry virtually all WiFi Remote ID beacons).
    static constexpr uint8_t kSnifferChannels[3] = {1, 6, 11};
    static constexpr uint32_t kSnifferChannelDwellMs = 450;  // >= 4 beacon intervals per channel.

    // Live status bitfield, mirrored into ObjectDictionary::ESP32DeviceStatus::remote_id_status.
    enum Status : uint8_t {
        kStatusBLEActive = 1 << 0,          // NimBLE observer is scanning.
        kStatusBLECodedPHYActive = 1 << 1,  // Coded PHY (BT5 Long Range) extended scan is active.
        kStatusWiFiSnifferActive = 1 << 2,  // WiFi promiscuous sniffer is running.
        kStatusBlockedByWiFi = 1 << 3,      // Requested but blocked: WiFi AP/STA up on a non-PSRAM build.
        kStatusBlockedByRAM = 1 << 4,       // Requested but blocked: insufficient free heap.
        kStatusNotInBuild = 1 << 5,         // Requested but Bluetooth is not compiled into this firmware.
    };

    RemoteIDManager() = default;

    /**
     * (Re)configures Remote ID reception from the current settings and network state. Idempotent: brings transports up
     * or down to match. Called from SettingsManager::Apply() and safe to call repeatedly.
     */
    void Apply();

    /**
     * Per-iteration work: services the WiFi channel hopper (when the sniffer is active) and any deferred bookkeeping.
     * Called from ADSBeeServer::Update().
     */
    void Update();

    /**
     * Ingests one raw Remote ID advertisement (already stripped to ODID bytes + transport metadata). Called from the
     * NimBLE host task and the WiFi promiscuous callback. Thread-safe with respect to Update()/Apply() via the queue and
     * the fact that dictionary ingest happens on the main task (see below).
     */
    void OnRawRemoteIDPacket(const RawRemoteIDPacket& packet);

    /**
     * Drains queued advertisements on the main task: ingests each into the local AircraftDictionary and forwards
     * rate-limited copies to the RP2040. Called from ADSBeeServer::Update() so all dictionary mutation stays on one
     * task. Returns the number of packets processed.
     */
    uint16_t ServiceIngestQueue();

    uint8_t GetStatus() const { return status_; }

   private:
    // Decides the target transport set from settings + build + network + heap, then reconciles the running transports.
    void Reconcile();

    // Returns true if this build/config allows Remote ID to coexist with active WiFi AP/STA (i.e. has PSRAM).
    static bool CanCoexistWithWiFi();

    // Rate-limit decision for forwarding a packet to the RP2040. Updates the dedup table. Returns true to forward.
    bool ShouldForwardToRP2040(const RawRemoteIDPacket& packet);

    // BLE (NimBLE) control — implemented in remote_id_ble.cpp.
    bool BLEStart(bool enable_coded_phy);
    void BLEStop();

    // WiFi promiscuous sniffer control — implemented in remote_id_wifi_sniffer.cpp.
    bool WiFiSnifferStart();
    void WiFiSnifferStop();
    void WiFiSnifferServiceHopper();

    struct DedupEntry {
        bool in_use = false;
        uint8_t mac[6] = {0};
        uint32_t last_location_forward_ms = 0;
        uint32_t last_static_forward_ms = 0;
    };
    DedupEntry* FindOrAllocDedupEntry(const uint8_t mac[6]);

    uint8_t status_ = 0;
    bool ble_running_ = false;
    bool ble_coded_running_ = false;
    bool wifi_sniffer_running_ = false;

    uint8_t sniffer_channel_index_ = 0;
    uint32_t last_channel_hop_ms_ = 0;

    DedupEntry dedup_table_[kDedupTableNumEntries];
};

// Global instance (defined in remote_id_manager.cpp), analogous to comms_manager / object_dictionary.
extern RemoteIDManager remote_id_manager;
