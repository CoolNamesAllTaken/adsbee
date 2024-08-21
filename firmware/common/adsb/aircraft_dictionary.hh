#ifndef _AIRCRAFT_DICTIONARY_HH_
#define _AIRCRAFT_DICTIONARY_HH_

#include <cstring>
#include <unordered_map>

#include "transponder_packet.hh"

class Aircraft {
   public:
    static const uint16_t kCallSignMaxNumChars = 8;

    enum AirframeType : uint16_t {
        kAirframeTypeInvalid = 0,
        kAirframeTypeReserved,
        kAirframeTypeNoCategoryInfo,
        kAirframeTypeSurfaceEmergencyVehicle,
        kAirframeTypeSurfaceServiceVehicle,
        kAirframeTypeGroundObstruction,
        kAirframeTypeGliderSailplane,
        kAirframeTypeLighterThanAir,
        kAirframeTypeParachutistSkydiver,
        kAirframeTypeUltralightHangGliderParaglider,
        kAirframeTypeUnmannedAerialVehicle,
        kAirframeTypeSpaceTransatmosphericVehicle,
        kAirframeTypeLight,    // < 7000kg
        kAirframeTypeMedium1,  // 7000kg - 34000kg
        kAirframeTypeMedium2,  // 34000kg - 136000kg
        kAirframeTypeHighVortexAircraft,
        kAirframeTypeHeavy,            // > 136000kg
        kAirframeTypeHighPerformance,  // >5g acceleration and >400kt speed
        kAirframeTypeRotorcraft
    };

    enum SurveillanceStatus : int16_t {
        kSurveillanceStatusNotSet = -1,
        kSurveillanceStatusNoCondition = 0,
        kSurveillanceStatusPermanantAlert = 1,
        kSurveillanceStatusTemporaryAlert = 2,
        kSurveillanceStatusSPICondition = 3
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

    enum BitFlag : uint16_t {
        kBitFlagIsAirborne = 0,
        kBitFlagIsMilitary,
        kBitFlagIdent,
        kBitFlagUpdatedBaroAltitude,  // This is the first updated flag bit, used for clearing.
        kBitFlagUpdatedGNSSAltitude,
        kBitFlagUpdatedPosition,
        kBitFlagUpdatedTrack,
        kBitFlagUpdatedHorizontalVelocity,
        kBitFlagUpdatedVerticalVelocity,
        kBitFlagNumFlagBits
    };

    uint32_t flags = 0b0;

    uint32_t last_seen_timestamp_ms = 0;

    uint16_t transponder_capability = 0;
    uint32_t icao_address = 0;
    char callsign[kCallSignMaxNumChars + 1] = "?";  // put extra EOS character at end
    uint16_t squawk = 0;
    AirframeType airframe_type = kAirframeTypeInvalid;

    SurveillanceStatus surveillance_status = kSurveillanceStatusNotSet;
    bool single_antenna_flag = false;
    int32_t baro_altitude_ft = 0;
    int32_t gnss_altitude_ft = 0;
    AltitudeSource altitude_source = kAltitudeSourceNotSet;

    // Airborne Position Message
    float latitude_deg = 0.0f;
    float longitude_deg = 0.0f;
    bool position_valid = false;

    // Airborne Velocities Message
    float heading_deg = 0.0f;
    float velocity_kts = 0;
    VelocitySource velocity_source = kVelocitySourceNotSet;
    int vertical_rate_fpm = 0.0f;
    VerticalRateSource vertical_rate_source = kVerticalRateSourceNotSet;
    int altitude_difference_gnss_above_baro_ft = 0;

    Aircraft(uint32_t icao_address_in);
    Aircraft();

    /**
     * Set an aircraft's position in Compact Position Reporting (CPR) format. Takes either an even or odd set of lat/lon
     * coordinates and uses them to set the aircraft's position.
     * @param[in] n_lat_cpr 17-bit latitude count.
     * @param[in] n_lon_cpr 17-bit longitude count.
     * @param[in] odd Boolean indicating that the position update is relative to an odd grid reference (if true) or an
     * even grid reference.
     * @param[in] redigesting Boolean flag used if SetCPRLatLon is being used to re-digest a packet. Assures that it
     * won't call itself again if set.
     * @retval True if coordinates were parsed successfully, false if not. NOTE: invalid positions can still be
     * considered a successful parse.
     */
    bool SetCPRLatLon(uint32_t n_lat_cpr, uint32_t n_lon_cpr, bool odd, bool redigesting = false);

    /**
     * Simple helper that checks to see whether a packet decode can be attempted (does not guarantee it will succeed,
     * for instance an odd and even packet may have been received, but from different CPR zones).
     * @retval True if decode can be attempted, false otherwise.
     */
    bool CanDecodePosition() {
        return last_odd_packet_.received_timestamp_ms > 0 && last_even_packet_.received_timestamp_ms > 0;
    }

    /**
     * Decodes the aircraft position using last_odd_packet_ and last_even_packet_.
     * @retval True if position was decoded successfully, false otherwise.
     */
    bool DecodePosition();

    /**
     * Set a flag bit on the Aircraft.
     * @param[in] Bit position to set.
     */
    inline void SetBitFlag(BitFlag bit) { flags |= (0b1 << bit); }

    /**
     * Clear a flag bit on the Aircraft.
     * @param[in] bit Bit position to clear.
     */
    inline void ClearBitFlag(BitFlag bit) { flags &= ~(0b1 << bit); }

    /**
     * Checks whether a flag bit is set.
     * @param[in] bit Position of bit to check.
     * @retval True if bit has been set, false if bit has been cleared.
     */
    inline bool HasBitFlag(BitFlag bit) { return flags & (0b1 << bit) ? true : false; }

    /**
     * Resets just the flag bits that show that something updated within the last reporting interval.
     */
    inline void ResetUpdatedBitFlags() { flags &= ~(~0b0 << kBitFlagUpdatedBaroAltitude); }

   private:
    struct CPRPacket {
        // SetCPRLatLon values.
        uint32_t received_timestamp_ms = 0;  // [ms] time since boot when packet was recorded
        uint32_t n_lat = 0;                  // 17-bit latitude count
        uint32_t n_lon = 0;                  // 17-bit longitude count

        // DecodePosition values.
        uint32_t calculated_timestamp_ms = 0;  // [ms] time since boot when packet was calculated
        float lat_cpr = 0.0f;
        float lon_cpr = 0.0f;
        uint16_t nl_cpr = 0;  // number of longitude cells in latitude band
        float lat =
            0.0f;  // only keep latitude since it's reused in cooperative calculations between odd and even packets
        // float lon = 0.0f; // longitude
    };

    CPRPacket last_odd_packet_;
    CPRPacket last_even_packet_;
};

class AircraftDictionary {
   public:
    struct AircraftDictionaryConfig_t {
        uint32_t aircraft_prune_interval_ms = 60e3;
    };
    static const uint16_t kMaxNumAircraft = 100;

    /**
     * Default constructor. Uses default config values.
     */
    AircraftDictionary() {};

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
     * Ingest a DecodedTransponderPacket and use it to insert and update the relevant aircraft.
     * @param[in] packet DecodedTransponderPacket to ingest. Can be 56-bit (Squitter) or 112-bit (Extended Squitter).
     * Passed as a reference, since packets can be marked as valid by this function.
     * @retval True if successful, false if something broke.
     */
    bool IngestDecodedTransponderPacket(DecodedTransponderPacket &packet);

    /**
     * Ingest an ADSBPacket directly. Exposed for testing, but usually this gets called by
     * IngestDecodedTransponderPacket and should not get touched directly.
     * @param[in] packet ADSBPacket to ingest. Derived from a DecodedTransponderPacket with DF=17-19.
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
};

#endif /* _AIRCRAFT_DICTIONARY_HH_ */