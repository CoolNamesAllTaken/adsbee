#pragma once

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <string_view>

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

    // Names for the AT commands, joined with '+' (e.g. BT4+BT5_LR).
    struct BitName {
        uint16_t bit;
        const char* name;
    };
    static constexpr BitName kTransportNames[] = {{1 << 0, "BT4"}, {1 << 1, "BT5_LR"}, {1 << 2, "WIFI_BEACON"}};
    static constexpr BitName kStatusNames[] = {
        {kStatusBLEActive, "BT_SCANNING"},
        {kStatusBLECodedPHYActive, "BT5_LR_SCANNING"},
        {kStatusWiFiSnifferActive, "WIFI_BEACON_SCANNING"},
        {kStatusBlockedByNetwork, "BLOCKED_NETWORK"},
        {kStatusBlockedByRAM, "BLOCKED_RAM"},
        {kStatusNotInBuild, "NOT_IN_BUILD"},
        {kStatusPausedLowHeap, "PAUSED_LOW_HEAP"},
        {kStatusTxBLELegacyActive, "TX_BT4"},
        {kStatusTxBLECodedActive, "TX_BT5_LR"},
        {kStatusTxWiFiBeaconActive, "TX_WIFI_BEACON"},
        {kStatusTxNoPosition, "TX_NO_POSITION"},
        {kStatusTxBlocked, "TX_BLOCKED"},
        {kStatusTxPositionSourceNotAllowed, "TX_POSITION_SOURCE_NOT_ALLOWED"},
    };
    static constexpr size_t kTransportsStrMaxLen = 32;  // BT4+BT5_LR+WIFI_BEACON
    static constexpr size_t kStatusStrMaxLen = 224;     // Every status name.

    /**
     * Writes the names of the set bits joined with '+', or "NONE". Bits without a name print as hex.
     * @retval buf
     */
    template <size_t N>
    static const char* BitsStr(uint16_t bits, const BitName (&names)[N], char* buf, size_t buf_len) {
        size_t len = 0;
        buf[0] = '\0';
        auto append = [&](const char* text) {
            int n = snprintf(buf + len, buf_len - len, "%s%s", len > 0 ? "+" : "", text);
            if (n > 0) len = (len + n < buf_len) ? len + n : buf_len - 1;
        };
        for (const BitName& bit_name : names) {
            if (!(bits & bit_name.bit)) continue;
            append(bit_name.name);
            bits &= ~bit_name.bit;
        }
        if (bits != 0) {
            char hex[8];
            snprintf(hex, sizeof(hex), "0x%X", bits);
            append(hex);
        }
        if (len == 0) append("NONE");
        return buf;
    }
    static const char* TransportsStr(uint8_t transports, char* buf, size_t buf_len) {
        return BitsStr(transports, kTransportNames, buf, buf_len);
    }
    static const char* StatusStr(uint16_t status, char* buf, size_t buf_len) {
        return BitsStr(status, kStatusNames, buf, buf_len);
    }

    /**
     * Parses transports: names joined with '+' (BT4+BT5_LR), ALL, NONE, or the older numeric mask (decimal or 0x hex).
     * @retval False if the text isn't one of those or has unknown bits.
     */
    static bool ParseTransports(std::string_view text, uint8_t& transports) {
        if (text.empty()) return false;
        uint32_t value = 0;
        if (text == "ALL") {
            value = kTransportsAll;
        } else if (text == "NONE") {
            value = 0;
        } else if (text[0] >= '0' && text[0] <= '9') {
            const bool hex = text.size() > 2 && text[0] == '0' && (text[1] == 'x' || text[1] == 'X');
            for (size_t i = hex ? 2 : 0; i < text.size(); i++) {
                const char c = text[i];
                uint32_t digit;
                if (c >= '0' && c <= '9') {
                    digit = c - '0';
                } else if (hex && c >= 'a' && c <= 'f') {
                    digit = c - 'a' + 10;
                } else if (hex && c >= 'A' && c <= 'F') {
                    digit = c - 'A' + 10;
                } else {
                    return false;
                }
                value = value * (hex ? 16 : 10) + digit;
                if (value > kTransportsAll) return false;
            }
        } else {
            while (!text.empty()) {
                const size_t plus = text.find('+');
                const std::string_view name = text.substr(0, plus);
                bool found = false;
                for (const BitName& bit_name : kTransportNames) {
                    if (name == bit_name.name) {
                        value |= bit_name.bit;
                        found = true;
                    }
                }
                if (!found) return false;
                if (plus == std::string_view::npos) break;
                text.remove_prefix(plus + 1);
                if (text.empty()) return false;  // Trailing '+'.
            }
        }
        transports = static_cast<uint8_t>(value);
        return true;
    }

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
