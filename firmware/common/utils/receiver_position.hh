#pragma once

#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <strings.h>

#include <string_view>

/**
 * Antenna position of this receiver, for feeds that report where the receiver is (MLAT, ground station status). Taken
 * from AT+RX_POSITION: the live GNSS fix for the GNSS source, the fixed position for FIXED, and no position for the
 * other sources. Packed: it is part of the RP2040 to ESP32 device status.
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
};
static_assert(sizeof(ReceiverPosition) == 30, "ReceiverPosition is stored and sent between processors as raw bytes.");

/**
 * Optional AT+RX_POSITION arguments for MLAT, after the arguments of the source:
 * AT+RX_POSITION=<source>,...,<ellipsoid_height_m>,<hacc_m>,<vacc_m>,<moving>. The height and accuracies describe a
 * FIXED position; moving applies to every source. Packed: it is part of the stored Settings.
 */
struct __attribute__((packed)) RxPositionDetails {
    static constexpr uint16_t kFirstATArg = 7;  // Index of ellipsoid_height_m in the AT+RX_POSITION arguments.
    static constexpr uint16_t kNumATArgs = 4;
    static constexpr float kFeetToMeters = 0.3048f;

    bool ellipsoid_height_set = false;
    float ellipsoid_height_m = 0.0f;     // Above the WGS84 ellipsoid.
    float horizontal_accuracy_m = 0.0f;  // One sigma, 0 if unknown.
    float vertical_accuracy_m = 0.0f;    // One sigma, 0 if unknown.
    bool moving = false;                 // The receiver may move (vehicle).

    bool operator==(const RxPositionDetails& other) const {
        return ellipsoid_height_set == other.ellipsoid_height_set && ellipsoid_height_m == other.ellipsoid_height_m &&
               horizontal_accuracy_m == other.horizontal_accuracy_m &&
               vertical_accuracy_m == other.vertical_accuracy_m && moving == other.moving;
    }
    bool operator!=(const RxPositionDetails& other) const { return !(*this == other); }

    /**
     * Repairs details read from raw flash: booleans become 0 or 1, and out of range values are cleared.
     * @retval True if anything was changed.
     */
    bool Sanitize() {
        bool changed = false;
        for (bool* flag : {&ellipsoid_height_set, &moving}) {
            uint8_t raw;
            memcpy(&raw, flag, sizeof(raw));
            if (raw > 1) {
                *flag = true;
                changed = true;
            }
        }
        float height_m = ellipsoid_height_m;
        if (!std::isfinite(height_m) || height_m <= -1000.0f || height_m >= 100000.0f ||
            (!ellipsoid_height_set && height_m != 0.0f)) {
            ellipsoid_height_set = false;
            ellipsoid_height_m = 0.0f;
            changed = true;
        }
        float accuracy_m = horizontal_accuracy_m;
        if (!ReceiverPosition::AccuracyIsValid(accuracy_m)) {
            horizontal_accuracy_m = 0.0f;
            changed = true;
        }
        accuracy_m = vertical_accuracy_m;
        if (!ReceiverPosition::AccuracyIsValid(accuracy_m)) {
            vertical_accuracy_m = 0.0f;
            changed = true;
        }
        return changed;
    }

    /**
     * Applies the optional AT+RX_POSITION arguments. An empty argument keeps its value, and "-" clears the ellipsoid
     * height.
     * @param[in] args The kNumATArgs argument strings (NUL-terminated), from ellipsoid_height_m on.
     * @param[out] error Reason for a failure.
     * @retval True if the arguments were valid. Nothing changes otherwise.
     */
    bool ApplyATArgs(const char* const* args, const char*& error) {
        auto parse_number = [](const char* str, float& value) -> bool {
            char* end = nullptr;
            value = strtof(str, &end);
            return end != str && *end == '\0' && std::isfinite(value);
        };
        RxPositionDetails result = *this;
        if (strcmp(args[0], "-") == 0) {
            result.ellipsoid_height_set = false;
            result.ellipsoid_height_m = 0.0f;
        } else if (args[0][0] != '\0') {
            float height_m;
            if (!parse_number(args[0], height_m) || height_m <= -1000.0f || height_m >= 100000.0f) {
                error = "Ellipsoid height must be a number from -1000 to 100000 m.";
                return false;
            }
            result.ellipsoid_height_set = true;
            result.ellipsoid_height_m = height_m;
        }
        float accuracies_m[2] = {result.horizontal_accuracy_m, result.vertical_accuracy_m};
        for (uint16_t i = 0; i < 2; i++) {
            if (args[1 + i][0] == '\0') continue;
            if (!parse_number(args[1 + i], accuracies_m[i]) || !ReceiverPosition::AccuracyIsValid(accuracies_m[i])) {
                error = "Accuracies must be numbers of at least 0 m.";
                return false;
            }
        }
        result.horizontal_accuracy_m = accuracies_m[0];
        result.vertical_accuracy_m = accuracies_m[1];
        if (strcmp(args[3], "0") == 0 || strcmp(args[3], "1") == 0) {
            result.moving = args[3][0] == '1';
        } else if (args[3][0] != '\0') {
            error = "Moving must be 0 or 1.";
            return false;
        }
        *this = result;
        return true;
    }

    /**
     * ApplyATArgs() for the full AT+RX_POSITION argument list as string views (cppAT). Arguments past num_args are
     * empty.
     */
    bool ApplyATArgs(const std::string_view* args, uint16_t num_args, const char*& error) {
        static constexpr uint16_t kArgMaxLen = 24;
        char arg_bufs[kNumATArgs][kArgMaxLen + 1] = {};
        const char* arg_ptrs[kNumATArgs];
        for (uint16_t i = 0; i < kNumATArgs; i++) {
            uint16_t arg = kFirstATArg + i;
            if (arg < num_args) {
                if (args[arg].length() > kArgMaxLen) {
                    error = "Argument too long.";
                    return false;
                }
                memcpy(arg_bufs[i], args[arg].data(), args[arg].length());
            }
            arg_ptrs[i] = arg_bufs[i];
        }
        return ApplyATArgs(arg_ptrs, error);
    }

    /**
     * Writes the optional AT+RX_POSITION arguments, without a leading comma. An unset ellipsoid height is "-".
     * @retval Number of characters written, as snprintf.
     */
    int PrintATArgs(char* buf, size_t buf_len) const {
        char height[16] = "-";
        if (ellipsoid_height_set) {
            snprintf(height, sizeof(height), "%.2f", static_cast<double>(ellipsoid_height_m));
        }
        return snprintf(buf, buf_len, "%s,%.2f,%.2f,%d", height, static_cast<double>(horizontal_accuracy_m),
                        static_cast<double>(vertical_accuracy_m), moving);
    }

    /**
     * The position MLAT reports for an AT+RX_POSITION setting.
     * @param[in] rx_position Receiver position setting (SettingsManager::RxPosition).
     * @param[in] gnss Live GNSS position, or nullptr without a valid fix.
     * @retval The GNSS fix for the GNSS source, the fixed position for FIXED (with the GNSS altitude as its height if
     * no ellipsoid height is set), else a position with source kSourceNone. Its moving flag is this setting's.
     */
    template <typename RxPosition>
    ReceiverPosition ForMLAT(const RxPosition& rx_position, const ReceiverPosition* gnss) const {
        ReceiverPosition position;
        if (rx_position.source == RxPosition::kPositionSourceGNSS) {
            if (gnss != nullptr && gnss->source == ReceiverPosition::kSourceGNSS) {
                position = *gnss;
            }
        } else if (rx_position.source == RxPosition::kPositionSourceFixed) {
            position.source = ReceiverPosition::kSourceFixed;
            position.latitude_deg = rx_position.latitude_deg;
            position.longitude_deg = rx_position.longitude_deg;
            position.height_m = ellipsoid_height_set ? static_cast<float>(ellipsoid_height_m)
                                                     : static_cast<float>(rx_position.gnss_altitude_ft) * kFeetToMeters;
            position.horizontal_accuracy_m = horizontal_accuracy_m;
            position.vertical_accuracy_m = vertical_accuracy_m;
        }
        position.moving = moving;
        return position;
    }
};
static_assert(sizeof(RxPositionDetails) == 14, "RxPositionDetails is stored as raw bytes.");

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
