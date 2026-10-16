#ifndef ALTITUDE_FILTER_HH_
#define ALTITUDE_FILTER_HH_

#include <cstdint>

// Altitude filter on aircraft reports (AT+FILTER_ALTITUDE_FT=<mode>,<a_ft>,<b_ft>). Raw packets are never filtered.
enum AltitudeFilterMode : uint8_t {
    kAltitudeFilterOff = 0,
    kAltitudeFilterAbove = 1,         // Keep aircraft at or above a.
    kAltitudeFilterBelow = 2,         // Keep aircraft at or below a.
    kAltitudeFilterRange = 3,         // Keep aircraft from a to b.
    kAltitudeFilterNearReceiver = 4,  // Keep aircraft within a feet above or below the receiver.
    kNumAltitudeFilterModes
};

// Mode names for settings printouts.
inline const char* AltitudeFilterModeStr(uint8_t mode) {
    static const char* const kStrs[kNumAltitudeFilterModes] = {"OFF", "ABOVE", "BELOW", "RANGE", "NEAR RECEIVER"};
    return mode < kNumAltitudeFilterModes ? kStrs[mode] : "INVALID";
}

static constexpr int32_t kAltitudeFilterMinFt = -2000;
static constexpr int32_t kAltitudeFilterMaxFt = 100000;

/**
 * Whether a mode and its arguments are a valid filter: a and b within kAltitudeFilterMinFt to kAltitudeFilterMaxFt,
 * a <= b for kAltitudeFilterRange and a > 0 for kAltitudeFilterNearReceiver.
 */
inline bool AltitudeFilterIsValid(uint8_t mode, int32_t a_ft, int32_t b_ft) {
    if (mode >= kNumAltitudeFilterModes || a_ft < kAltitudeFilterMinFt || a_ft > kAltitudeFilterMaxFt ||
        b_ft < kAltitudeFilterMinFt || b_ft > kAltitudeFilterMaxFt) {
        return false;
    }
    if (mode == kAltitudeFilterRange) return a_ft <= b_ft;
    if (mode == kAltitudeFilterNearReceiver) return a_ft > 0;
    return true;
}

// Inclusive altitude bounds an aircraft must be within to be reported.
struct AltitudeFilterBounds {
    bool enabled = false;
    int32_t min_ft = INT32_MIN;
    int32_t max_ft = INT32_MAX;

    /**
     * Resolves a filter setting to bounds. Disabled when the mode is off or invalid, or for kAltitudeFilterNearReceiver
     * without a receiver altitude.
     */
    static AltitudeFilterBounds Of(uint8_t mode, int32_t a_ft, int32_t b_ft, bool receiver_altitude_valid,
                                   int32_t receiver_altitude_ft) {
        AltitudeFilterBounds bounds;
        if (!AltitudeFilterIsValid(mode, a_ft, b_ft)) {
            return bounds;
        }
        switch (mode) {
            case kAltitudeFilterAbove:
                bounds.min_ft = a_ft;
                break;
            case kAltitudeFilterBelow:
                bounds.max_ft = a_ft;
                break;
            case kAltitudeFilterRange:
                bounds.min_ft = a_ft;
                bounds.max_ft = b_ft;
                break;
            case kAltitudeFilterNearReceiver:
                if (!receiver_altitude_valid) return bounds;
                bounds.min_ft = receiver_altitude_ft - a_ft;  // No overflow: both are within about +/-100000 ft.
                bounds.max_ft = receiver_altitude_ft + a_ft;
                break;
            default:
                return bounds;
        }
        bounds.enabled = true;
        return bounds;
    }

    // Whether an aircraft at altitude_ft is left out. Aircraft with no known altitude are kept.
    inline bool Excludes(bool altitude_known, int32_t altitude_ft) const {
        return enabled && altitude_known && (altitude_ft < min_ft || altitude_ft > max_ft);
    }
};

#endif /* ALTITUDE_FILTER_HH_ */
