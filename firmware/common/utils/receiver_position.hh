#pragma once

#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <strings.h>

#include <string_view>

/**
 * Antenna position of this receiver, for feeds that report where the receiver is (MLAT, ground station status).
 * Live GNSS with a valid fix wins, else the fixed position from the settings, else there is no position.
 * Packed: it is part of the stored Settings and of the RP2040 to ESP32 device status.
 */
struct __attribute__((packed)) ReceiverPosition {
    enum Source : uint8_t { kSourceNone = 0, kSourceFixed, kSourceGNSS, kNumSources };

    Source source = kSourceNone;
    double latitude_deg = 0.0;           // WGS84.
    double longitude_deg = 0.0;          // WGS84.
    float height_m = 0.0f;               // Above the WGS84 ellipsoid.
    float horizontal_accuracy_m = 0.0f;  // One sigma, 0 if unknown.
    float vertical_accuracy_m = 0.0f;    // One sigma, 0 if unknown.
    bool moving = false;                 // The receiver may move (vehicle).

    bool IsValid() const { return source != kSourceNone; }

    static const char* SourceToStr(Source source) {
        switch (source) {
            case kSourceFixed:
                return "fixed";
            case kSourceGNSS:
                return "gnss";
            case kSourceNone:
            default:
                return "none";
        }
    }

    /**
     * @retval True if the coordinates are finite and in range. Accuracies must be finite and not negative.
     */
    static bool CoordinatesAreValid(double latitude_deg, double longitude_deg, float height_m) {
        return std::isfinite(latitude_deg) && std::isfinite(longitude_deg) && std::isfinite(height_m) &&
               latitude_deg >= -90.0 && latitude_deg <= 90.0 && longitude_deg >= -180.0 && longitude_deg <= 180.0 &&
               height_m > -1000.0f && height_m < 100000.0f;
    }
    static bool AccuracyIsValid(float accuracy_m) { return std::isfinite(accuracy_m) && accuracy_m >= 0.0f; }

    /**
     * Repairs a stored fixed position read from raw flash: anything but a valid kSourceFixed position becomes
     * kSourceNone, and `moving` becomes 0 or 1.
     * @retval True if anything was changed.
     */
    static bool SanitizeStoredFixed(ReceiverPosition& position) {
        bool changed = false;
        uint8_t raw_moving;
        memcpy(&raw_moving, &position.moving, sizeof(raw_moving));
        if (raw_moving > 1) {
            const uint8_t one = 1;
            memcpy(&position.moving, &one, sizeof(one));
            changed = true;
        }
        bool moving = position.moving;
        if (position.source == kSourceNone) {
            return changed;
        }
        if (position.source != kSourceFixed ||
            !CoordinatesAreValid(position.latitude_deg, position.longitude_deg, position.height_m) ||
            !AccuracyIsValid(position.horizontal_accuracy_m) || !AccuracyIsValid(position.vertical_accuracy_m)) {
            position = ReceiverPosition();
            position.moving = moving;
            changed = true;
        }
        return changed;
    }

    /**
     * Applies AT+ANTENNA_POSITION=<NONE|FIXED>,<lat_deg>,<lon_deg>,<height_m>,<hacc_m>,<vacc_m>,<moving> to a stored
     * fixed position. FIXED needs latitude, longitude and height; empty accuracies mean unknown. An empty `moving`
     * keeps the stored value. NONE ignores the coordinates.
     * @param[in] args Argument strings (NUL-terminated), num_args of them.
     * @param[in,out] position Stored fixed position; changed only on success.
     * @param[out] error Reason for a failure.
     * @retval True if the arguments were valid.
     */
    static bool ApplyATArgs(const char* const* args, uint16_t num_args, ReceiverPosition& position,
                            const char*& error) {
        auto arg = [&](uint16_t i) -> const char* { return i < num_args && args[i] != nullptr ? args[i] : ""; };
        auto parse_number = [](const char* str, double& value) -> bool {
            char* end = nullptr;
            value = strtod(str, &end);
            return end != str && *end == '\0' && std::isfinite(value);
        };
        ReceiverPosition result = position;
        if (strcasecmp(arg(0), "NONE") == 0) {
            bool moving = result.moving;
            result = ReceiverPosition();
            result.moving = moving;
        } else if (strcasecmp(arg(0), "FIXED") == 0) {
            double latitude_deg, longitude_deg, height_m;
            if (!parse_number(arg(1), latitude_deg) || !parse_number(arg(2), longitude_deg) ||
                !parse_number(arg(3), height_m)) {
                error = "FIXED needs a numeric latitude, longitude and height.";
                return false;
            }
            if (!CoordinatesAreValid(latitude_deg, longitude_deg, static_cast<float>(height_m))) {
                error = "Latitude must be -90 to 90, longitude -180 to 180 and height -1000 to 100000 m.";
                return false;
            }
            double accuracies_m[2] = {0.0, 0.0};
            for (uint16_t i = 0; i < 2; i++) {
                if (arg(4 + i)[0] == '\0') continue;
                if (!parse_number(arg(4 + i), accuracies_m[i]) || !AccuracyIsValid(static_cast<float>(accuracies_m[i]))) {
                    error = "Accuracies must be numbers of at least 0 m.";
                    return false;
                }
            }
            result.source = kSourceFixed;
            result.latitude_deg = latitude_deg;
            result.longitude_deg = longitude_deg;
            result.height_m = static_cast<float>(height_m);
            result.horizontal_accuracy_m = static_cast<float>(accuracies_m[0]);
            result.vertical_accuracy_m = static_cast<float>(accuracies_m[1]);
        } else if (arg(0)[0] != '\0') {
            error = "Source must be NONE or FIXED.";
            return false;
        }
        const char* moving = arg(6);
        if (strcmp(moving, "0") == 0 || strcmp(moving, "1") == 0) {
            result.moving = moving[0] == '1';
        } else if (moving[0] != '\0') {
            error = "Moving must be 0 or 1.";
            return false;
        }
        position = result;
        return true;
    }

    /**
     * ApplyATArgs() for AT command arguments as string views (cppAT).
     */
    static bool ApplyATArgs(const std::string_view* args, uint16_t num_args, ReceiverPosition& position,
                            const char*& error) {
        static constexpr uint16_t kNumArgs = 7;
        static constexpr uint16_t kArgMaxLen = 24;
        char arg_bufs[kNumArgs][kArgMaxLen + 1] = {};
        const char* arg_ptrs[kNumArgs];
        for (uint16_t i = 0; i < kNumArgs; i++) {
            if (i < num_args) {
                if (args[i].length() > kArgMaxLen) {
                    error = "Argument too long.";
                    return false;
                }
                memcpy(arg_bufs[i], args[i].data(), args[i].length());
            }
            arg_ptrs[i] = arg_bufs[i];
        }
        return ApplyATArgs(arg_ptrs, kNumArgs, position, error);
    }

    /**
     * Writes a stored fixed position as the AT+ANTENNA_POSITION arguments, without the leading '='.
     * @retval Number of characters written, as snprintf.
     */
    static int PrintATArgs(char* buf, size_t buf_len, const ReceiverPosition& position) {
        return snprintf(buf, buf_len, "%s,%.7f,%.7f,%.2f,%.2f,%.2f,%d",
                        position.source == kSourceFixed ? "FIXED" : "NONE", position.latitude_deg,
                        position.longitude_deg, position.height_m, position.horizontal_accuracy_m,
                        position.vertical_accuracy_m, position.moving);
    }

    /**
     * Picks the position to report.
     * @param[in] fixed Stored fixed position: source kSourceFixed if set, kSourceNone otherwise. Its `moving` flag is
     * the setting for both sources.
     * @param[in] gnss Live GNSS position, or nullptr without a valid fix.
     * @retval Live GNSS if available, else the fixed position, else a position with source kSourceNone.
     */
    static ReceiverPosition Resolve(const ReceiverPosition& fixed, const ReceiverPosition* gnss) {
        ReceiverPosition position;
        if (gnss != nullptr && gnss->source == kSourceGNSS) {
            position = *gnss;
        } else if (fixed.source == kSourceFixed) {
            position = fixed;
        }
        position.moving = fixed.moving;
        return position;
    }
};
static_assert(sizeof(ReceiverPosition) == 30, "ReceiverPosition is stored and sent between processors as raw bytes.");

/**
 * GNSS pulse per second (PPS) reference for the MLAT timestamp counter.
 */
struct __attribute__((packed)) ReceiverPPS {
    bool valid = false;
    uint64_t mlat_48mhz_counts = 0;  // MLAT counter at the latest PPS rising edge.
    uint32_t unix_time_s = 0;        // UTC second that edge marks.
};

/**
 * Current receiver position. Defined per platform (RP2040, ESP32, ADSBee m1421).
 * @param[out] position Filled in; source kSourceNone when there is no position.
 * @retval True if a position is available.
 */
bool GetReceiverPosition(ReceiverPosition& position);
