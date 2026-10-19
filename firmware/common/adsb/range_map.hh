#pragma once

#include <cmath>
#include <cstdint>
#include <cstring>

/**
 * Range per direction and altitude band for swarm reports (AT+SWARM), as the swarm protocol v1 defines it: 36 sectors
 * of 10 degrees (0 = north) by 12 altitude bands, each holding the largest distance seen, in units of kUnitMeters.
 */
class RangeMap {
   public:
    static constexpr uint16_t kNumSectors = 36;
    static constexpr uint16_t kNumBands = 12;
    static constexpr uint16_t kNumBins = kNumSectors * kNumBands;
    static constexpr uint16_t kBitmapLenBytes = kNumBins / 8;
    static constexpr uint32_t kUnitMeters = 2000;

    // Band per thousand feet below 40,000 ft. Bands: [0,1k) [1k,2k) [2k,4k) [4k,6k) [6k,10k) [10k,15k) [15k,20k)
    // [20k,25k) [25k,30k) [30k,35k) [35k,40k) [40k,inf).
    static constexpr uint8_t kBandByKft[40] = {0, 1, 2, 2, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6,
                                               7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10};

    static inline uint8_t AltitudeBand(int32_t altitude_ft) {
        if (altitude_ft < 0) return 0;
        if (altitude_ft >= 40000) return kNumBands - 1;
        return kBandByKft[altitude_ft / 1000];
    }

    // Bearing in 1/65536 turns to a 10 degree sector.
    static inline uint8_t Sector(uint16_t bearing_bam16) {
        return static_cast<uint8_t>((static_cast<uint32_t>(bearing_bam16) * kNumSectors) >> 16);
    }

    // Distance in meters to a bin value: ceil(distance / unit), clamped to 1..255.
    static inline uint8_t DistanceValue(uint32_t distance_m) {
        uint32_t units = distance_m / kUnitMeters + (distance_m % kUnitMeters != 0);
        return units < 1 ? 1 : units > 255 ? 255 : static_cast<uint8_t>(units);
    }

    inline void Record(uint32_t distance_m, uint16_t bearing_bam16, int32_t altitude_ft) {
        uint8_t& bin = bins[AltitudeBand(altitude_ft) * kNumSectors + Sector(bearing_bam16)];
        uint8_t value = DistanceValue(distance_m);
        if (value > bin) bin = value;
    }

    void Merge(const RangeMap& other) {
        for (uint16_t i = 0; i < kNumBins; i++) {
            if (other.bins[i] > bins[i]) bins[i] = other.bins[i];
        }
    }

    void Clear() { memset(bins, 0, sizeof(bins)); }

    /**
     * Writes the protocol's two arrays: a bitmap with bit i (byte i / 8, bit i % 8, LSB first) set for each bin with
     * data, and one value byte per set bit in bin order.
     * @param[out] bitmap kBitmapLenBytes Bytes.
     * @param[out] values kNumBins Bytes at most.
     * @retval Number of value Bytes written.
     */
    uint16_t Encode(uint8_t* bitmap, uint8_t* values) const {
        memset(bitmap, 0, kBitmapLenBytes);
        uint16_t num_values = 0;
        for (uint16_t i = 0; i < kNumBins; i++) {
            if (bins[i] == 0) continue;
            bitmap[i / 8] |= 1 << (i % 8);
            values[num_values++] = bins[i];
        }
        return num_values;
    }

    uint8_t bins[kNumBins] = {0};  // index = band * kNumSectors + sector; 0 = no data.
};

/**
 * What a swarm report covers: the range map plus message and aircraft counts. The aircraft dictionary feeds it.
 */
class SwarmRecorder {
   public:
    static constexpr uint16_t kUniqueBits = 2048;  // Linear counting: a few % error up to ~3000 aircraft.
    // A period's range map is withheld when at least this share of positions, from this many aircraft, were dropped.
    static constexpr uint32_t kWithholdDroppedPercent = 10;
    static constexpr uint8_t kWithholdDroppedAircraft = 5;

    struct Guard {
        uint32_t num_positions = 0;  // Positions offered to the range map.
        uint32_t num_dropped = 0;    // Of those, beyond the horizon.
        uint8_t num_dropped_aircraft = 0;  // Distinct aircraft dropped, counted up to kWithholdDroppedAircraft.
        uint32_t dropped_uids[kWithholdDroppedAircraft] = {0};

        void NoteDroppedAircraft(uint32_t uid) {
            for (uint8_t i = 0; i < num_dropped_aircraft; i++) {
                if (dropped_uids[i] == uid) return;
            }
            if (num_dropped_aircraft < kWithholdDroppedAircraft) dropped_uids[num_dropped_aircraft++] = uid;
        }
    };

    struct Stats {
        uint32_t modes_valid = 0;
        uint32_t es_valid = 0;
        uint32_t uat_adsb = 0;
        uint32_t uat_uplink = 0;
        uint16_t aircraft_max = 0;
    };

    // Band tops for the radio horizon, in feet; the top band counts as 60,000 ft.
    static constexpr int32_t kBandTopFt[RangeMap::kNumBands] = {1000,  2000,  4000,  6000,  10000, 15000,
                                                                20000, 25000, 30000, 35000, 40000, 60000};
    /**
     * Sets the horizon limit per band from the antenna altitude: 1.15 * 4.12 km * (sqrt(h_rx) + sqrt(h_band_top)) + 20
     * km, heights in meters (radio horizon with margin). Call when the receiver altitude changes, not per position.
     */
    void SetReceiverAltitude(int32_t altitude_m) {
        if (altitude_m == receiver_altitude_m_) return;
        receiver_altitude_m_ = altitude_m;
        float rx = sqrtf(altitude_m > 0 ? static_cast<float>(altitude_m) : 0.0f);
        for (uint16_t b = 0; b < RangeMap::kNumBands; b++) {
            float top = sqrtf(kBandTopFt[b] * 0.3048f);
            horizon_m_[b] = static_cast<uint32_t>((1.15f * 4.12f * (rx + top) + 20.0f) * 1000.0f);
        }
    }

    /**
     * A confirmed position heard directly. Positions beyond the radio horizon (a wrong receiver position, or a bad
     * decode) are counted as dropped instead.
     */
    inline void RecordPosition(uint32_t distance_m, uint16_t bearing_bam16, int32_t altitude_ft, uint32_t uid) {
        if (!record_range) return;
        guard.num_positions++;
        if (distance_m > horizon_m_[RangeMap::AltitudeBand(altitude_ft)]) {
            guard.num_dropped++;
            guard.NoteDroppedAircraft(uid);
            return;
        }
        range.Record(distance_m, bearing_bam16, altitude_ft);
    }

    // Too many positions beyond the horizon: the receiver position is likely wrong, so the map is withheld.
    bool RangeImplausible() const {
        return guard.num_dropped * 100 >= kWithholdDroppedPercent * guard.num_positions &&
               guard.num_dropped_aircraft >= kWithholdDroppedAircraft && guard.num_dropped > 0;
    }

    inline void MarkAircraft(uint32_t uid) {
        // MurmurHash3 finalizer: linear counting needs bits that look random, also for neighboring addresses.
        uid ^= uid >> 16;
        uid *= 0x85EBCA6Bu;
        uid ^= uid >> 13;
        uid *= 0xC2B2AE35u;
        uid ^= uid >> 16;
        uint32_t bit = uid % kUniqueBits;
        unique_bits_[bit / 8] |= 1 << (bit % 8);
    }

    // Valid frame counts as the receiver reports them each second.
    inline void AddFrames(uint32_t modes_valid, uint32_t es_valid, uint32_t uat_adsb, uint32_t uat_uplink) {
        stats.modes_valid += modes_valid;
        stats.es_valid += es_valid;
        stats.uat_adsb += uat_adsb;
        stats.uat_uplink += uat_uplink;
    }

    // Once per dictionary update: the number of aircraft tracked.
    inline void NoteAircraftCount(uint16_t num_aircraft) {
        if (num_aircraft > stats.aircraft_max) stats.aircraft_max = num_aircraft;
    }

    // Estimated number of different aircraft marked.
    uint16_t UniqueAircraft() const {
        uint16_t zeros = 0;
        for (uint16_t i = 0; i < sizeof(unique_bits_); i++) zeros += 8 - __builtin_popcount(unique_bits_[i]);
        if (zeros == 0) zeros = 1;
        return static_cast<uint16_t>(lroundf(-static_cast<float>(kUniqueBits) * logf(zeros / (float)kUniqueBits)));
    }

    // Adds a later period: max for the range and peak aircraft, sums for counts, union for unique aircraft.
    void Merge(const SwarmRecorder& later) {
        range.Merge(later.range);
        stats.modes_valid += later.stats.modes_valid;
        stats.es_valid += later.stats.es_valid;
        stats.uat_adsb += later.stats.uat_adsb;
        stats.uat_uplink += later.stats.uat_uplink;
        if (later.stats.aircraft_max > stats.aircraft_max) stats.aircraft_max = later.stats.aircraft_max;
        for (uint16_t i = 0; i < sizeof(unique_bits_); i++) unique_bits_[i] |= later.unique_bits_[i];
        guard.num_positions += later.guard.num_positions;
        guard.num_dropped += later.guard.num_dropped;
        for (uint8_t i = 0; i < later.guard.num_dropped_aircraft; i++) {
            guard.NoteDroppedAircraft(later.guard.dropped_uids[i]);
        }
    }

    void Clear() {
        range.Clear();
        stats = Stats();
        guard = Guard();
        memset(unique_bits_, 0, sizeof(unique_bits_));
    }

    SwarmRecorder() {
        receiver_altitude_m_ = INT32_MIN;
        SetReceiverAltitude(0);
    }

    RangeMap range;
    Stats stats;
    Guard guard;
    bool record_range = true;  // False while the receiver position isn't fixed or from GNSS.

   private:
    uint8_t unique_bits_[kUniqueBits / 8] = {0};
    int32_t receiver_altitude_m_;
    uint32_t horizon_m_[RangeMap::kNumBands];
};
