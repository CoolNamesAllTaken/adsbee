#pragma once

#include <cstdint>

/**
 * Keeps Remote ID from starving the ESP32 of the internal RAM that the web server, settings and OTA need. Shared by the
 * ESP32 (enforcement) and the RP2040 (AT checks and status text).
 */
class RemoteIDGuard {
   public:
    // Live status bitfield, ObjectDictionary::ESP32DeviceStatus::remote_id_status. Low byte receive, high byte transmit.
    enum Status : uint16_t {
        kStatusBLEActive = 1 << 0,          // NimBLE observer is scanning.
        kStatusBLECodedPHYActive = 1 << 1,  // Coded PHY (BT5 Long Range) extended scan is active.
        kStatusWiFiSnifferActive = 1 << 2,  // WiFi promiscuous sniffer is running.
        kStatusBlockedByNetwork = 1 << 3,   // Requested transports blocked: no PSRAM and WiFi or Ethernet on.
        kStatusBlockedByRAM = 1 << 4,       // Requested but blocked: insufficient free heap.
        kStatusNotInBuild = 1 << 5,         // Requested but Bluetooth is not compiled into this firmware.
        kStatusPausedLowHeap = 1 << 6,      // Requested but paused: free heap fell below the reserve.

        kStatusTxBLELegacyActive = 1 << 8,    // Advertising Remote ID on BT4 legacy (1M PHY).
        kStatusTxBLECodedActive = 1 << 9,     // Advertising Remote ID on BT5 Long Range (Coded PHY).
        kStatusTxWiFiBeaconActive = 1 << 10,  // Injecting Remote ID WiFi beacon frames.
        kStatusTxNoPosition = 1 << 11,        // Transmitting, but rx_position is unavailable (Location sent as unknown).
        kStatusTxBlocked = 1 << 12,           // Transmit requested but could not start (RAM, radio refused, or build).
        // Transmitting, but the rx_position source may not be broadcast as our own (aircraft-derived, or none). Always
        // accompanied by kStatusTxNoPosition.
        kStatusTxPositionSourceNotAllowed = 1 << 13,
    };

    // Internal heap kept free for the web server, settings and OTA while Remote ID runs.
    static constexpr uint32_t kReserveFreeBytes = 48 * 1024;
    static constexpr uint32_t kReserveLargestBlockBytes = 16 * 1024;
    // After a pause, Remote ID restarts only after a hold-off that doubles with each pause (capped).
    static constexpr uint32_t kResumeHoldOffMs = 60 * 1000;
    static constexpr uint32_t kResumeHoldOffMaxMs = 64 * 60 * 1000;

    // Transport bits, as in SettingsManager::kRemoteIDTransport*.
    static constexpr uint8_t kTransportsBLE = 0b011;
    static constexpr uint8_t kTransportWiFiBeacon = 0b100;
    static constexpr uint8_t kTransportsAll = kTransportsBLE | kTransportWiFiBeacon;

    /**
     * Transports this hardware can run with the enabled network interfaces. Without PSRAM, nothing fits next to WiFi AP
     * or STA. Next to Ethernet the trimmed Bluetooth stack fits, but not together with the WiFi beacon sniffer, so
     * Bluetooth (the more common Remote ID broadcast) gets the RAM.
     */
    static uint8_t AllowedTransports(bool has_psram, bool wifi_ap_enabled, bool wifi_sta_enabled,
                                     bool ethernet_enabled) {
        if (has_psram) return kTransportsAll;
        if (wifi_ap_enabled || wifi_sta_enabled) return 0;
        if (ethernet_enabled) return kTransportsBLE;
        return kTransportsAll;
    }

    static bool HeapBelowReserve(uint32_t free_bytes, uint32_t largest_block_bytes) {
        return free_bytes < kReserveFreeBytes || largest_block_bytes < kReserveLargestBlockBytes;
    }

    /**
     * Runtime safety net: pauses Remote ID when the heap falls below the reserve, allows a restart after the hold-off.
     * Starting a transport still needs its own start threshold (RemoteIDManager), which sits above the reserve.
     */
    class HeapWatch {
       public:
        /**
         * Call about once a second.
         * @param[in] running True if any Remote ID transport is up.
         * @retval True if Remote ID must stay paused.
         */
        bool Update(uint32_t free_bytes, uint32_t largest_block_bytes, uint32_t now_ms, bool running) {
            if (running && HeapBelowReserve(free_bytes, largest_block_bytes)) {
                if (num_pauses_ < UINT8_MAX) num_pauses_++;
                paused_ = true;
                paused_at_ms_ = now_ms;
            } else if (paused_ && now_ms - paused_at_ms_ >= HoldOffMs()) {
                paused_ = false;
            }
            return paused_;
        }

        // Clears the pause and the back-off, e.g. when the user changes Remote ID settings.
        void Reset() {
            paused_ = false;
            num_pauses_ = 0;
        }

        bool IsPaused() const { return paused_; }
        uint8_t GetNumPauses() const { return num_pauses_; }

        uint32_t HoldOffMs() const {
            uint32_t hold_off_ms = kResumeHoldOffMs;
            for (uint8_t i = 1; i < num_pauses_ && hold_off_ms < kResumeHoldOffMaxMs; i++) hold_off_ms *= 2;
            return hold_off_ms < kResumeHoldOffMaxMs ? hold_off_ms : kResumeHoldOffMaxMs;
        }

       private:
        bool paused_ = false;
        uint8_t num_pauses_ = 0;
        uint32_t paused_at_ms_ = 0;
    };

    /**
     * Reason why requested Remote ID isn't (fully) running, or nullptr if nothing blocks it.
     */
    static const char* BlockedReason(uint16_t status) {
        constexpr uint16_t kActive = kStatusBLEActive | kStatusWiFiSnifferActive | kStatusTxBLELegacyActive |
                                     kStatusTxBLECodedActive | kStatusTxWiFiBeaconActive;
        if (status & kStatusPausedLowHeap) return "paused: ESP32 free memory fell below what the web server needs";
        if (status & kStatusBlockedByNetwork) {
            return (status & kActive)
                       ? "partly paused: this ESP32 has no PSRAM, so with Ethernet on only the Bluetooth transports run"
                       : "paused: this ESP32 has no PSRAM, so with WiFi on Remote ID can't run, and with Ethernet on "
                         "only the Bluetooth transports can";
        }
        if (status & kStatusNotInBuild) return "blocked: Bluetooth is not in this firmware";
        if (status & kStatusBlockedByRAM) return "blocked: not enough free ESP32 memory";
        if (status & kStatusTxBlocked) return "blocked: the radio could not start transmitting";
        return nullptr;
    }
};
