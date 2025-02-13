#ifndef AIRCRAFT_DICTIONARY_HH_
#define AIRCRAFT_DICTIONARY_HH_

#include <cstdio>
#include <cstring>
#include <unordered_map>

#include "hal.hh"
#include "json_utils.hh"
#include "macros.hh"
#include "transponder_packet.hh"

#define USE_NASA_CPR

class Aircraft {
   public:
    static constexpr uint16_t kCallSignMaxNumChars = 7;
    static constexpr uint16_t kCallSignMinNumChars = 3;  // Callsigns must be at this long to be valid.
    // These variables define filter bounds for time between CPR packets. If the time between packets is greater than
    // the time delta limit, the old CPR packet is discarded and the CPR packet pair is not used for position decoding.
    static constexpr uint32_t kDefaultCPRIntervalMs = 10e3;  // CPR interval when starting from scratch or stale track.
    static constexpr uint32_t kRefCPRIntervalMs = 19e3;      // Reference interval for rejecting CPR packet pairs.
    static constexpr uint32_t kMaxCPRIntervalMs = 30e3;  // Never accept CPR packet pairs more than 30 seconds apart.
    static constexpr uint32_t kMaxTrackUpdateIntervalMs = 20e3;  // Tracks older than this are considered stale.

    enum Category : uint8_t {
        kCategoryInvalid = 0,
        kCategoryReserved,
        kCategoryNoCategoryInfo,
        kCategorySurfaceEmergencyVehicle,
        kCategorySurfaceServiceVehicle,
        kCategoryGroundObstruction,
        kCategoryGliderSailplane,
        kCategoryLighterThanAir,
        kCategoryParachutistSkydiver,
        kCategoryUltralightHangGliderParaglider,
        kCategoryUnmannedAerialVehicle,
        kCategorySpaceTransatmosphericVehicle,
        kCategoryLight,    // < 7000kg
        kCategoryMedium1,  // 7000kg - 34000kg
        kCategoryMedium2,  // 34000kg - 136000kg
        kCategoryHighVortexAircraft,
        kCategoryHeavy,            // > 136000kg
        kCategoryHighPerformance,  // >5g acceleration and >400kt speed
        kCategoryRotorcraft
    };

    enum AltitudeSource : int16_t {
        kAltitudeNotAvailable = -2,
        kAltitudeSourceNotSet = -1,
        kAltitudeSourceBaro = 0,
        kAltitudeSourceGNSS = 1
    };

    enum VerticalRateSource : int16_t {
        kVerticalRateNotAvailable = -2,
        kVerticalRateSourceNotSet = -1,
        kVerticalRateSourceGNSS = 0,
        kVerticalRateSourceBaro = 1
    };

    enum VelocitySource : int16_t {
        kVelocitySourceNotAvailable = -2,
        kVelocitySourceNotSet = -1,
        kVelocitySourceGroundSpeed = 0,
        kVelocitySourceAirspeedTrue = 1,
        kVelocitySourceAirspeedIndicated = 2
    };

    enum BitFlag : uint32_t {
        kBitFlagIsAirborne = 0,  // Received messages or flags indicating the aircraft is airborne.
        kBitFlagBaroAltitudeValid,
        kBitFlagGNSSAltitudeValid,
        kBitFlagPositionValid,
        kBitFlagDirectionValid,
        kBitFlagHorizontalVelocityValid,
        kBitFlagVerticalVelocityValid,
        kBitFlagIsMilitary,              // Received at least one military ES message from the aircraft.
        kBitFlagIsClassB2GroundVehicle,  // Is a class B2 ground vehicle transmitting at <70W.
        kBitFlagHas1090ESIn,             // Aircraft is equipped with 1090MHz Extended Squitter receive capability.
        kBitFlagHasUATIn,                // Aircraft can receive UAT.
        kBitFlagTCASOperational,         // TCAS system on aircraft is functional.
        kBitFlagSingleAntenna,           // Indicates that the aircraft is using a single antenna. Transmissions may be
                                         // intermittent.
        kBitFlagDirectionIsHeading,      // Direction is aircraft heading and not track angle.
        kBitFlagHeadingUsesMagneticNorth,  // Heading in surface and airborne position messages is magnetic north, not
                                           // true north.
        kBitFlagIdent,                     // IDENT switch is currently active.
        kBitFlagAlert,                     // Aircraft is indicating an alert.
        kBitFlagTCASRA,                    // Indicates a TCAS resolution advisory is active.
        kBitFlagReserved0,
        kBitFlagReserved1,
        kBitFlagReserved2,
        kBitFlagReserved3,
        // Flags after kBitFlagUpdatedBaroAltitude are cleared at the end of every reporting interval.
        kBitFlagUpdatedBaroAltitude,
        kBitFlagUpdatedGNSSAltitude,
        kBitFlagUpdatedPosition,
        kBitFlagUpdatedDirection,
        kBitFlagUpdatedHorizontalVelocity,
        kBitFlagUpdatedVerticalVelocity,
        kBitFlagNumFlagBits
    };

    enum NICBit : uint16_t { kNICBitA = 0, kNICBitB = 1, kNICBitC = 2 };

    enum SystemDesignAssurance : uint8_t {
        kSDASupportedFailureUnknownOrNoSafetyEffect = 0b00,
        kSDASupportedFailureMinor = 0b01,
        kSDASupportedFailureMajor = 0b10,
        kSDASupportedFailureHazardous = 0b11
    };

    enum NICRadiusOfContainment : uint8_t {
        kROCUnknown = 0,
        kROCLessThan20NauticalMiles = 1,
        kROCLessThan8NauticalMiles = 2,
        kROCLessThan4NauticalMiles = 3,
        kROCLessThan2NauticalMiles = 4,
        kROCLessThan1NauticalMile = 5,
        kROCLessThan0p6NauticalMiles = 6,  // Lump together with <0.5NM and <0.3NM since they share a NIC value.
        kROCLessThan0p2NauticalMiles = 7,
        kROCLessThan0p1NauticalMiles = 8,
        kROCLessThan75Meters = 9,
        kROCLessThan25Meters = 10,
        kROCLessThan7p5Meters = 11
    };

    enum NICBarometricAltitudeIntegrity : uint8_t {
        kBAIGillhamInputNotCrossChecked = 0,
        kBAIGillHamInputCrossCheckedOrNonGillhamSource = 1
    };

    enum NACHorizontalVelocityError : uint8_t {
        kHVEUnknownOrGreaterThanOrEqualTo10MetersPerSecond = 0b000,
        kHVELessThan10MetersPerSecond = 0b110,
        kHVELessThan3MetersPerSecond = 0b010,
        kHVELessThan1MeterPerSecond = 0b011,
        kHVELessThan0p3MetersPerSecond = 0b100
    };

    enum NACEstimatedPositionUncertainty : uint8_t {
        kEPUUnknownOrGreaterThanOrEqualTo10NauticalMiles = 0,
        kEPULessThan10NauticalMiles = 1,
        kEPULessThan4NauticalMiles = 2,
        kEPULessThan2NauticalMiles = 3,
        kEPULessThan1NauticalMile = 4,
        kEPULessThan0p5NauticalMiles = 5,
        kEPULessThan0p3NauticalMiles = 6,
        kEPULessThan0p1NauticalMiles = 7,
        kEPULessThan0p05NauticalMiles = 8,
        kEPULessThan30Meters = 9,
        kEPULessThan10Meters = 10,
        kEPULessThan3Meters = 11
    };

    // This composite SIL value is SIL | (SIL_supplement << 2).
    enum SILProbabilityOfExceedingNICRadiusOfContainmnent : uint8_t {
        kPOERCUnknownOrGreaterThan1em3PerFlightHour = 0b000,
        kPOERCLessThanOrEqualTo1em3PerFligthHour = 0b001,
        kPOERCLessThanOrEqualTo1em5PerFlightHour = 0b010,
        kPOERCLessThanOrEqualTo1em7PerFlightHour = 0b011,
        kPOERCUnknownOrGreaterThan1em3PerSample = 0b100,
        kPOERCLessThanOrEqualTo1em3PerSample = 0b101,
        kPOERCLessThanOrEqualTo1em5PerSample = 0b110,
        kPOERCLessThanOrEqualTo1em7PerSample = 0b111,
    };

    enum GVA : uint8_t {
        kGVAUnknownOrGreaterThan150Meters = 0,
        GVALessThanOrEqualTo150Meters = 1,
        GVALessThanOrEqualTo45Meters = 2,
        GVALessThan45Meters = 3
    };

    struct Metrics {
        // We can only confirm that valid frames came from this aircraft. Not sure who invalid frames are from.
        uint16_t valid_squitter_frames = 0;
        uint16_t valid_extended_squitter_frames = 0;
    };

    Aircraft(uint32_t icao_address_in);
    Aircraft();

    /**
     * Checks to see if the aircraft position can be decoded. Requires that both an odd and an even packet have been
     * received, and they aren't separated by too large of a time interval.
     * @retval True if the aircraft position can be decoded, false otherwise.
     */
    bool CanDecodePosition();

    /**
     * Clears the CPR packet cache. Used when too much time has elapsed since the last CPR packet was received, to avoid
     * decoding CPR location with invalid packet pairings.
     */
    inline void ClearCPRPackets() {
        // Clearng received timestamps causes the packet pair to be rejected during the decoding stage, so it's as good
        // as wiping all of the received packet contents.
        last_odd_packet_.received_timestamp_ms = 0;
        last_even_packet_.received_timestamp_ms = 0;
    }

    /**
     * Decodes the aircraft position using last_odd_packet_ and last_even_packet_.
     * @retval True if position was decoded successfully, false otherwise.
     */
    bool DecodePosition();

    /**
     * Returns the maximum time delta between CPR packets that will be accepted for decoding.
     * @retval Maximum allowed time delta between CPR packets.
     */
    uint32_t GetMaxAllowedCPRIntervalMs() const {
        if (velocity_source == kVelocitySourceNotSet || velocity_source == kVelocitySourceNotAvailable ||
            get_time_since_boot_ms() - last_track_update_timestamp_ms > kMaxTrackUpdateIntervalMs) {
            return kDefaultCPRIntervalMs;
        }
        // Scale time delta threshold based on the velocity of the aircraft relative to 500kts, but clamp the result to
        // the max time delta thresholds.
        return MIN(kRefCPRIntervalMs * 500 / velocity_kts, kMaxCPRIntervalMs);
    }

    /**
     * Checks whether a flag bit is set.
     * @param[in] bit Position of bit to check.
     * @retval True if bit has been set, false if bit has been cleared.
     */
    inline bool HasBitFlag(BitFlag bit) const { return flags & (0b1 << bit) ? true : false; }

    /**
     * Indicate that a frame has been received by incrementing the corresponding frame counter.
     * @param[in] is_extended_squitter Set to true if the frame received was a Mode S frame.
     */
    inline void IncrementNumFramesReceived(bool is_extended_squitter = false) {
        is_extended_squitter ? metrics_counter_.valid_extended_squitter_frames++
                             : metrics_counter_.valid_squitter_frames++;
    }

    /**
     * Returns whether a NIC supplement bit has been written to. Used to decide when to use NIC supplement bit values to
     * determine NIC value based on received TypeCodes.
     * @param[in] bit NIC supplement bit to check.
     * @retval True if bit has been written to, false otherwise.
     */
    inline bool NICBitIsValid(NICBit bit) { return nic_bits & (0b1 << bit); }

    /**
     * Resets just the flag bits that show that something updated within the last reporting interval.
     */
    inline void ResetUpdatedBitFlags() { flags &= ~(~0b0 << kBitFlagUpdatedBaroAltitude); }

    /**
     * Set an aircraft's position in Compact Position Reporting (CPR) format. Takes either an even or odd set of lat/lon
     * coordinates and uses them to set the aircraft's position.
     * @param[in] n_lat_cpr 17-bit latitude count.
     * @param[in] n_lon_cpr 17-bit longitude count.
     * @param[in] odd Boolean indicating that the position update is relative to an odd grid reference (if true) or an
     * even grid reference.
     * @param[in] received_timestamp_ms Timestamp in milliseconds when the position packet was received. Should be
     * derived from the MLAT counter, but the precision can be pretty lax since it is only used when deciding whether to
     * reject CPR packet pairings due to too much time elapsed between even and odd packets.
     * @retval True if coordinates were parsed successfully, false if not. NOTE: Invalid positions can still be
     * considered a successful parse.
     */
    bool SetCPRLatLon(uint32_t n_lat_cpr, uint32_t n_lon_cpr, bool odd, uint32_t received_timestamp_ms);

    /**
     * Roll the metrics counter over to the public metrics field.
     */
    inline void UpdateMetrics() {
        metrics = metrics_counter_;
        metrics_counter_ = Metrics();
    }

    /**
     * Set or clear a bit on the Aircraft.
     */
    inline void WriteBitFlag(BitFlag bit, bool value) { value ? flags |= (0b1 << bit) : flags &= ~(0b1 << bit); }

    /**
     * Write a value for a NIC supplement bit. Used to piece together a NIC from separate messages, so that the NIC can
     * be determined based on a received TypeCode.
     * @param[in] bit NIC supplement bit to write.
     * @param[in] value Value to write to the bit.
     */
    inline void WriteNICBit(NICBit bit, bool value) {
        value ? nic_bits |= (0b1 << bit) : nic_bits &= ~(0b1 << bit);
        // FIXME: Permanently setting NIC bits valid like this can cause invalid navigation integrity values to be read
        // if a stale NIC supplement bit is being used. Hopefully this isn't a big problem if NIC values don't change
        // frequently.
        nic_bits_valid |= (0b1 << bit);
    }

    uint32_t flags = 0b0;

    uint32_t last_message_timestamp_ms = 0;
    int16_t last_message_signal_strength_dbm = 0;  // Voltage of RSSI signal during message receipt.
    int16_t last_message_signal_quality_db = 0;    // Ratio of RSSI to noise floor during message receipt.
    uint32_t last_track_update_timestamp_ms = 0;   // Timestamp of the last time that the position was updated.
    Metrics metrics;

    uint16_t transponder_capability = 0;
    uint32_t icao_address = 0;
    char callsign[kCallSignMaxNumChars + 1] = "?";  // put extra EOS character at end
    uint16_t squawk = 0;
    Category category = kCategoryNoCategoryInfo;
    uint8_t category_raw = 0;  // Non-enum category in case we want the value without a many to one mapping.

    int32_t baro_altitude_ft = 0;
    int32_t gnss_altitude_ft = 0;
    AltitudeSource altitude_source = kAltitudeSourceNotSet;

    // Airborne Position Message
    float latitude_deg = 0.0f;
    float longitude_deg = 0.0f;

    // Airborne Velocities Message
    float direction_deg = 0.0f;
    float velocity_kts = 0;
    VelocitySource velocity_source = kVelocitySourceNotSet;
    int vertical_rate_fpm = 0.0f;
    VerticalRateSource vertical_rate_source = kVerticalRateSourceNotSet;

    // Aircraft Operation Status Message
    // Navigation Integrity Category (NIC)
    uint8_t nic_bits_valid = 0b000;  // MSb to LSb: nic_c_valid nic_b_valid nic_a_valid.
    uint8_t nic_bits = 0b000;        // MSb to LSb: nic_c nic_b nic_a.
    NICRadiusOfContainment navigation_integrity_category = kROCUnknown;  // 4 bits.
    NICBarometricAltitudeIntegrity navigation_integrity_category_baro =
        kBAIGillhamInputNotCrossChecked;  // 1 bit. Default to worst case.
    // Navigation Accuracy Category (NAC)
    NACHorizontalVelocityError navigation_accuracy_category_velocity =
        kHVEUnknownOrGreaterThanOrEqualTo10MetersPerSecond;  // 3 bits.
    NACEstimatedPositionUncertainty navigation_accuracy_category_position =
        kEPUUnknownOrGreaterThanOrEqualTo10NauticalMiles;  // 4 bits.
    // Geometric Vertical Accuracy (GVA)
    GVA geometric_vertical_accuracy = kGVAUnknownOrGreaterThan150Meters;  // 2 bits.
    SILProbabilityOfExceedingNICRadiusOfContainmnent source_integrity_level =
        kPOERCUnknownOrGreaterThan1em3PerFlightHour;  // 3 bits.
    // System Design Assurance
    SystemDesignAssurance system_design_assurance = kSDASupportedFailureUnknownOrNoSafetyEffect;  // 2 bits.
    // GPS Antenna Offset
    int8_t gnss_antenna_offset_right_of_roll_axis_m =
        INT8_MAX;  // Defaults to INT8_MAX to indicate it hasn't been read yet.
    // Aircraft dimensions (on the ground).
    uint16_t length_m = 0;
    uint16_t width_m = 0;

    int8_t adsb_version = -1;

   private:
    struct CPRPacket {
        // SetCPRLatLon values.
        uint32_t received_timestamp_ms = 0;  // [ms] time since boot when packet was recorded
        uint32_t n_lat = 0;                  // 17-bit latitude count
        uint32_t n_lon = 0;                  // 17-bit longitude count

#ifndef USE_NASA_CPR
        // DecodePosition values.
        float lat_cpr = 0.0f;
        float lon_cpr = 0.0f;
        uint16_t nl_cpr = 0;  // number of longitude cells in latitude band
        float lat =
            0.0f;  // only keep latitude since it's reused in cooperative calculations between odd and even packets
// float lon = 0.0f; // longitude
#endif
    };

    CPRPacket last_odd_packet_;
    CPRPacket last_even_packet_;

    Metrics metrics_counter_;
};

class AircraftDictionary {
   public:
    static const uint16_t kMaxNumAircraft = 400;
    static const uint16_t kMaxNumSources = 3;

    struct AircraftDictionaryConfig_t {
        uint32_t aircraft_prune_interval_ms = 60e3;
    };

    struct Metrics {
        static const uint16_t kMetricsJSONMaxLen = 1000;  // Includes null terminator.

        uint32_t raw_squitter_frames = 0;
        uint32_t valid_squitter_frames = 0;
        uint32_t raw_extended_squitter_frames = 0;
        uint32_t valid_extended_squitter_frames = 0;
        uint32_t demods_1090 = 0;

        uint16_t raw_squitter_frames_by_source[kMaxNumSources] = {0};
        uint16_t valid_squitter_frames_by_source[kMaxNumSources] = {0};
        uint16_t raw_extended_squitter_frames_by_source[kMaxNumSources] = {0};
        uint16_t valid_extended_squitter_frames_by_source[kMaxNumSources] = {0};
        uint16_t demods_1090_by_source[kMaxNumSources] = {0};

        /**
         * Formats the metrics dictionary into a JSON packet with the following structure.
         * {
         *      "raw_squitter_frames": 10,
         *      "valid_squitter_frames": 7,
         *      "raw_extended_squitter_frames": 30,
         *      "valid_extended_squitter_frames": 16,
         *      "demods_1090": 50,
         *      "raw_squitter_frames_by_source": [3, 3, 4],
         *      "valid_squitter_frames_by_source": [2, 2, 3],
         *      "raw_extended_squitter_frames_by_source": [10, 11, 9],
         *      "valid_squitter_frames_by_source": [4, 4, 8],
         *      "demods_1090_by_source": [20, 10, 20]
         * }
         * @param[in] buf Buffer to write the JSON string to.
         * @param[in] buf_len Length of the buffer, including the null terminator.
         */
        inline uint16_t ToJSON(char *buf, size_t buf_len) {
            uint16_t message_max_len = buf_len - 1;  // Leave space for null terminator.
            snprintf(buf, message_max_len - strlen(buf),
                     "{ \"raw_squitter_frames\": %lu, \"valid_squitter_frames\": %lu, "
                     "\"raw_extended_squitter_frames\": %lu, "
                     "\"valid_extended_squitter_frames\": %lu, \"demods_1090\": %lu, ",
                     raw_squitter_frames, valid_squitter_frames, raw_extended_squitter_frames,
                     valid_extended_squitter_frames, demods_1090);
            uint16_t chars_written = strlen(buf);
            chars_written += ArrayToJSON(buf + chars_written, buf_len - chars_written, "raw_squitter_frames_by_source",
                                         raw_squitter_frames_by_source, "%u", true);
            chars_written +=
                ArrayToJSON(buf + chars_written, buf_len - chars_written, "valid_squitter_frames_by_source",
                            valid_squitter_frames_by_source, "%u", true);
            chars_written +=
                ArrayToJSON(buf + chars_written, buf_len - chars_written, "raw_extended_squitter_frames_by_source",
                            raw_extended_squitter_frames_by_source, "%u", true);
            chars_written +=
                ArrayToJSON(buf + chars_written, buf_len - chars_written, "valid_extended_squitter_frames_by_source",
                            valid_extended_squitter_frames_by_source, "%u", true);
            chars_written += ArrayToJSON(buf + strlen(buf), buf_len - strlen(buf), "demods_1090_by_source",
                                         demods_1090_by_source, "%u",
                                         false);  // No trailing comma.
            chars_written += snprintf(buf + chars_written, buf_len - chars_written, "}");
            return chars_written;
        }
    };

    /**
     * Default constructor. Uses default config values.
     */
    AircraftDictionary() {
        // Avoid reallocation of the hash map to prevent fragmentation.
        dict.max_load_factor(1.0);
        dict.reserve(kMaxNumAircraft);
    };

    /**
     * Constructor with config values specified.
     */
    AircraftDictionary(AircraftDictionaryConfig_t config_in) : config_(config_in) {};

    /**
     * Removes all aircraft from the aircraft dictionary.
     */
    void Init();

    /**
     * Prunes stale aircraft from the dictionary.
     * @param[in] timestamp_us Current timestamp, in microseconds, to use for pruning. Aircraft older than timestamp_us
     * minus the pruning interval will be removed.
     */
    void Update(uint32_t timestamp_us);

    /**
     * Log an attempted demodulation on 1090MHz. Used to record performance statistics. Note that the increment won't be
     * visible until the next dictionary update occurs.
     */
    inline void Record1090Demod(int16_t source = -1) {
        metrics_counter_.demods_1090++;
        if (source >= 0 && source < kMaxNumSources) {
            metrics_counter_.demods_1090_by_source[source]++;
        }
    }

    /**
     * Log a received 56-bit squitter frame. Used to record performance statistics. Valid frames are automatically
     * recorded during ingestion, this function is broken out so that raw frames with no ingestion attempted can stil be
     * recorded. Note that the increment won't be visible until the next dictionary update occurs.
     */
    inline void Record1090RawSquitterFrame(int16_t source = -1) {
        metrics_counter_.raw_squitter_frames++;
        if (source > 0) {
            metrics_counter_.raw_squitter_frames_by_source[source]++;
        }
    }

    /**
     * Log a received 112-bit extended squitter frame. Used to record performance statistics. Valid frames are
     * automatically recorded during ingestion, this function is broken out so that raw frames with no ingestion
     * attempted can stil be recorded. Note that the increment won't be visible until the next dictionary update occurs.
     */
    inline void Record1090RawExtendedSquitterFrame(int16_t source = -1) {
        metrics_counter_.raw_extended_squitter_frames++;
        if (source > 0) {
            metrics_counter_.raw_extended_squitter_frames_by_source[source]++;
        }
    }

    /**
     * Ingests a Decoded1090Packet and uses it to insert and update the relevant aircraft.
     * @param[in] packet Decoded1090Packet to ingest. Can be 56-bit (Squitter) or 112-bit (Extended Squitter).
     * Passed as a reference, since packets can be marked as valid by this function.
     * @retval True if successful, false if something broke.
     */
    bool IngestDecoded1090Packet(Decoded1090Packet &packet);

    /**
     * Ingests an Identity Surveillance Reply packet and uses it to update the relevant aircraft. Exposed for
     * testing, but usually called by IngestDecoded1090Packet.
     * Note: this function requires that the packet be marked as valid using the ForceValid() function. If the packet is
     * valid and does not match an ICAO in the aircraft dictionary, a new aircraft will be inserted.
     * @param[in] packet IdentityReplyPacket to ingest.
     * @retval True if successful, false if something broke.
     */
    bool IngestIdentityReplyPacket(IdentityReplyPacket packet);

    /**
     * Ingests an Altitude Surveillance Reply packet and uses it to update the relevant aircraft. Exposed for
     * testing, but usually called by IngestDecoded1090Packet.
     * Note: this function requires that the packet be marked as valid using the ForceValid() function. If the packet is
     * valid and does not match an ICAO in the aircraft dictionary, a new aircraft will be inserted.
     * @param[in] packet AltitudeReplyPacket to ingest.
     * @retval True if successful, false if something broke.
     */
    bool IngestAltitudeReplyPacket(AltitudeReplyPacket packet);

    /**
     * Ingests an All Call Reply packet and uses it to update the relevant aircraft. Exposed for testing, but usually
     * called by IngestDecoded1090Packet.
     *
     * Currently, we only accept all call reply packets with an interrogator ID of 0 (replies to spontaneous acquisition
     * squitters), since we don't have a way to know the interrogator ID of ground based surveillance stations.
     */
    bool IngestAllCallReplyPacket(AllCallReplyPacket packet);

    /**
     * Ingests an ADSBPacket directly. Exposed for testing, but usually this gets called by
     * IngestDecoded1090Packet and should not get touched directly.
     * @param[in] packet ADSBPacket to ingest. Derived from a Decoded1090Packet with DF=17-19.
     * @retval True if successful, false if something broke.
     */
    bool IngestADSBPacket(ADSBPacket packet);

    /**
     * Returns the number of aircraft currently in the dictionary.
     * @retval Number of aircraaft that are currently in the dictionary.
     */
    uint16_t GetNumAircraft();

    /**
     * Adds an Aircraft object to the aircraft dictionary, hashed by ICAO address.
     * @param[in] aircraft Aircraft to insert.
     * @retval True if insertaion succeeded, false if failed.
     */
    bool InsertAircraft(const Aircraft &aircraft);

    /**
     * Remove an aircraft from the dictionary, by ICAO address.
     * @param[in] icao_address ICAO address of the aircraft to remove from the dictionary.
     * @retval True if removal succeeded, false if aircraft was not found.
     */
    bool RemoveAircraft(uint32_t icao_address);

    /**
     * Retrieve an aircraft from the dictionary.
     * @param[in] icao_address Address to use for looking up the aircraft.
     * @param[out] aircraft_out Aircraft reference to put the retrieved aircraft into if successful.
     * @retval True if aircraft was found and retrieved, false if aircraft was not in the dictionary.
     */
    bool GetAircraft(uint32_t icao_address, Aircraft &aircraft_out) const;

    /**
     * Check if an aircraft is contained in the dictionary.
     * @param[in] icao_address Address to use for looking up the aircraft.
     * @retval True if aircraft is in the dictionary, false if not.
     */
    bool ContainsAircraft(uint32_t icao_address) const;

    /**
     * Return a pointer to an aircraft if it's in the aircraft dictionary.
     * @param[in] icao_address ICAO address of the aircraft to find.
     * @retval Pointer to the aircraft if it exists, or NULL if it wasn't in the dictionary.
     */
    Aircraft *GetAircraftPtr(uint32_t icao_address);

    std::unordered_map<uint32_t, Aircraft> dict;  // index Aircraft objects by their ICAO identifier

    Metrics metrics;

   private:
    // Helper functions for ingesting specific ADS-B packet types, called by IngestADSBPacket.

    /**
     * GENERIC COMMENT FOR ALL MESSAGE INGESTION HELPERS
     * Ingests a <Message Type> ADS-B message. Called by IngestADSBPacket, which makes sure that the packet
     * is valid and has the correct Downlink Format.
     * @param[out] aircraft Reference to the Aircraft to populate with info pulled from packet.
     * @param[in] packet ADSBPacket to ingest.
     * @retval True if message was ingested successfully, false otherwise.
     */

    bool ApplyAircraftIDMessage(Aircraft &aircraft, ADSBPacket packet);
    bool ApplySurfacePositionMessage(Aircraft &aircraft, ADSBPacket packet);
    bool ApplyAirbornePositionMessage(Aircraft &aircraft, ADSBPacket packet);
    bool ApplyAirborneVelocitiesMessage(Aircraft &aircraft, ADSBPacket packet);
    bool ApplyAircraftStatusMessage(Aircraft &aircraft, ADSBPacket packet);
    bool ApplyTargetStateAndStatusInfoMessage(Aircraft &aircraft, ADSBPacket packet);
    bool ApplyAircraftOperationStatusMessage(Aircraft &aircraft, ADSBPacket packet);

    AircraftDictionaryConfig_t config_;
    // Counters in metrics_counter_ are incremented, then metrics_counter_ is swapped into metrics during the dictionary
    // update. This ensures that the public metrics struct always has valid data.
    Metrics metrics_counter_;
};

#endif /* AIRCRAFT_DICTIONARY_HH_ */