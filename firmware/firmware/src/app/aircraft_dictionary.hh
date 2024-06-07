#ifndef _AIRCRAFT_DICTIONARY_HH_
#define _AIRCRAFT_DICTIONARY_HH_

#include <cstring>
#include <unordered_map>

#include "ads_b_packet.hh"

class Aircraft {
   public:
    static const uint16_t kCallSignMaxNumChars = 8;

    enum WakeVortex : uint16_t {
        kWakeVortexInvalid = 0,
        kWakeVortexReserved,
        kWakeVortexNoCategoryInfo,
        kWakeVortexSurfaceEmergencyVehicle,
        kWakeVortexSurfaceServiceVehicle,
        kWakeVortexGroundObstruction,
        kWakeVortexGliderSailplane,
        kWakeVortexLighterThanAir,
        kWakeVortexParachutistSkydiver,
        kWakeVortexUltralightHangGliderParaglider,
        kWakeVortexUnmannedAerialVehicle,
        kWakeVortexSpaceTransatmosphericVehicle,
        kWakeVortexLight,    // < 7000kg
        kWakeVortexMedium1,  // 7000kg - 34000kg
        kWakeVortexMedium2,  // 34000kg - 136000kg
        kWakeVortexHighVortexAircraft,
        kWakeVortexHeavy,            // > 136000kg
        kWakeVortexHighPerformance,  // >5g acceleration and >400kt speed
        kWakeVortexRotorcraft
    };

    enum SurveillanceStatus : uint16_t {
        kSurveillanceStatusNoCondition = 0,
        kSurveillanceStatusPermanantAlert = 1,
        kSurveillanceStatusTemporaryAlert = 2,
        kSurveillanceStatusSPICondition = 3
    };

    uint32_t last_seen_timestamp_ms = 0;

    uint16_t transponder_capability = 0;
    uint32_t icao_address = 0;
    char callsign[kCallSignMaxNumChars + 1];  // put extra EOS character at end
    WakeVortex wake_vortex = kWakeVortexInvalid;

    SurveillanceStatus surveillance_status = kSurveillanceStatusNoCondition;
    bool single_antenna_flag = false;
    uint16_t barometric_altitude_m = 0;
    uint16_t gnss_altitude_m = 0;

    float latitude_deg = 0.0f;
    float longitude_deg = 0.0f;
    bool position_valid = false;
    bool is_airborne =
        true;  // assume that most aircraft encountered will be airborne, so put them there until proven otherwise

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
    AircraftDictionary(){};

    /**
     * Constructor with config values specified.
     */
    AircraftDictionary(AircraftDictionaryConfig_t config_in) : config_(config_in){};

    void Init();
    void Update(uint32_t timestamp_us);

    bool IngestADSBPacket(ADSBPacket packet);
    uint16_t GetNumAircraft();

    bool InsertAircraft(const Aircraft &aircraft);
    bool RemoveAircraft(uint32_t icao_address);
    bool GetAircraft(uint32_t icao_address, Aircraft &aircraft_out) const;
    bool ContainsAircraft(uint32_t icao_address) const;
    Aircraft *GetAircraftPtr(uint32_t icao_address);

    std::unordered_map<uint32_t, Aircraft> dict;  // index Aircraft objects by their ICAO identifier

   private:
    // Helper functions for ingesting specific ADS-B packet types, called by IngestADSBPacket.
    bool IngestAircraftIDMessage(Aircraft &aircraft, ADSBPacket packet);
    bool IngestSurfacePositionMessage(Aircraft &aircraft, ADSBPacket packet);
    // bool IngestAirbornePositionBaroAltMessage(ADSBPacket packet);
    // bool IngestAirbornePositionGNSSAltMessage(ADSBPacket packet);
    bool IngestAirbornePositionMessage(Aircraft &aircraft, ADSBPacket packet);
    bool IngestAirborneVelocitiesMessage(Aircraft &aircraft, ADSBPacket packet);
    bool IngestAircraftStatusMessage(Aircraft &aircraft, ADSBPacket packet);
    bool IngestTargetStateAndStatusInfoMessage(Aircraft &aircraft, ADSBPacket packet);
    bool IngestAircraftOperationStatusMessage(Aircraft &aircraft, ADSBPacket packet);

    AircraftDictionaryConfig_t config_;
};

#endif /* _AIRCRAFT_DICTIONARY_HH_ */