#pragma once

#include <cstdint>

#include "receiver_position.hh"

/**
 * Generic, receiver-agnostic NMEA 0183 parser.
 *
 * Designed to be tolerant of NMEA protocol version differences (2.x through 4.11) so the same
 * parsing core works across a wide range of GNSS receivers:
 *   - Matches on the 3-character sentence type (e.g. "GGA", "RMC"), ignoring the 2-character
 *     talker ID, so multi-constellation talkers ($GPGGA, $GNGGA, $GLGGA, $GAGGA, ...) all parse.
 *   - Indexes fields positionally from the front and tolerates extra trailing fields appended by
 *     newer versions (e.g. RMC navigational status in v2.3+, system/signal IDs in v4.11).
 *   - Treats empty fields as "not present" rather than faulting.
 *   - Validates the XOR checksum when present.
 *
 * The parser has no platform dependencies (no pico-sdk) so it can be unit tested on the host.
 *
 * Usage: feed received UART bytes one at a time to IngestByte(). When a complete, valid sentence
 * is decoded the internally held GNSSFix is updated; query it via fix().
 */
class NMEAParser {
   public:
    // Maximum NMEA sentence length is 82 chars per spec; allow some slack for non-conforming
    // receivers. Includes the leading '$' but not a null terminator.
    static constexpr uint16_t kLineBufMaxLen = 120;
    static constexpr uint16_t kMaxNumFields = 32;

    // Result of ingesting a byte / completing a sentence.
    enum SentenceType : uint8_t {
        kSentenceNone = 0,      // No complete sentence yet (still accumulating).
        kSentenceGGA,           // GGA parsed and applied.
        kSentenceRMC,           // RMC parsed and applied.
        kSentenceGST,           // GST (position error statistics) parsed and applied.
        kSentenceUnknown,       // Complete sentence with a type we don't decode.
        kSentenceChecksumFail,  // Complete sentence but checksum did not match.
        kSentenceMalformed,     // Complete sentence but could not be parsed.
    };

    // Decoded GNSS fix, merged across GGA (altitude / satellites / fix quality) and RMC
    // (position / speed / course / validity).
    struct GNSSFix {
        bool valid = false;             // True if the last position-bearing sentence reported a fix.
        double latitude_deg = 0.0;      // WGS84 degrees, north positive.
        double longitude_deg = 0.0;     // WGS84 degrees, east positive.
        int32_t altitude_ft = 0;        // MSL altitude, feet (converted from meters).
        float altitude_m = 0.0f;        // MSL altitude, meters.
        bool geoid_separation_valid = false;
        float geoid_separation_m = 0.0f;  // Height of the geoid (MSL) above the WGS84 ellipsoid, meters.
        bool accuracy_valid = false;      // From GST: one sigma errors below, updated with the fix.
        float latitude_error_m = 0.0f;
        float longitude_error_m = 0.0f;
        float altitude_error_m = 0.0f;
        uint32_t accuracy_timestamp_ms = 0;  // Caller-supplied timestamp of the last GST.
        float heading_deg = 0.0f;       // Course over ground, degrees from true north.
        int32_t speed_kts = 0;          // Speed over ground, knots.
        uint8_t num_satellites = 0;     // Satellites used in the GGA fix.
        uint8_t fix_quality = 0;        // GGA fix quality (0 = no fix, 1 = GPS, 2 = DGPS, ...).
        bool utc_time_valid = false;    // True when a valid NMEA UTC time has been parsed.
        uint8_t utc_hour = 0;
        uint8_t utc_minute = 0;
        uint8_t utc_second = 0;
        uint16_t utc_millisecond = 0;
        bool utc_date_valid = false;  // True when RMC carried a date.
        uint16_t utc_year = 0;        // Four digits.
        uint8_t utc_month = 0;
        uint8_t utc_day = 0;
        uint32_t utc_time_timestamp_ms = 0;  // Caller-supplied timestamp of the last sentence with a UTC time.
        uint32_t last_update_timestamp_ms = 0;  // Caller-supplied timestamp of last applied fix.
    };

    NMEAParser() = default;

    /**
     * Feed a single received byte into the parser.
     * @param[in] c Received character.
     * @retval SentenceType describing what (if anything) completed on this byte.
     */
    SentenceType IngestByte(char c);

    /**
     * @retval Const reference to the most recently merged fix.
     */
    const GNSSFix& fix() const { return fix_; }

    /**
     * Set the timestamp (ms) recorded on the fix when the next sentence is applied. The parser is
     * platform-agnostic, so the owning driver supplies the clock.
     */
    void SetTimestampMs(uint32_t timestamp_ms) { timestamp_ms_ = timestamp_ms; }

    /**
     * Seconds since 1970-01-01 UTC for a UTC date and time (no leap seconds).
     */
    static uint32_t UnixTime(uint16_t year, uint8_t month, uint8_t day, uint8_t hour, uint8_t minute,
                             uint8_t second);

    /**
     * Finds the UTC second a pulse per second (PPS) edge marks. The receiver sends the time of each whole second
     * after the pulse that marks it, so the edge is labeled with a whole-second time received less than a second
     * after it.
     * @param[in] fix Current fix, with date and time.
     * @param[in] edge_timestamp_ms Time of the PPS edge, on the clock passed to SetTimestampMs().
     * @param[out] unix_time_s UTC second of the edge.
     * @retval True if the fix's time labels this edge.
     */
    static bool PPSEdgeUnixTime(const GNSSFix& fix, uint32_t edge_timestamp_ms, uint32_t& unix_time_s);

    /**
     * Converts a fix to an antenna position: height above the ellipsoid from MSL altitude plus geoid separation, and
     * accuracies from GST when one arrived with the fix.
     * @param[in] fix Current fix.
     * @param[out] position Filled in with source ReceiverPosition::kSourceGNSS.
     * @retval False if the fix has no valid position or no geoid separation.
     */
    static bool FixToReceiverPosition(const GNSSFix& fix, ReceiverPosition& position);

   private:
    // Parse the currently buffered line (line_buf_ / line_len_, '$' stripped, checksum validated)
    // by splitting on ',' and dispatching on the 3-char sentence type.
    SentenceType ParseLine();
    SentenceType ParseGGA(const char* const* fields, uint8_t num_fields);
    SentenceType ParseRMC(const char* const* fields, uint8_t num_fields);
    SentenceType ParseGST(const char* const* fields, uint8_t num_fields);

    char line_buf_[kLineBufMaxLen];  // Accumulated sentence body (between '$' and '*').
    uint16_t line_len_ = 0;
    bool in_sentence_ = false;  // True once '$' seen, until terminator.

    // Checksum tracking: XOR of all chars between '$' and '*'.
    uint8_t running_checksum_ = 0;
    bool reading_checksum_ = false;  // True once '*' seen; next two chars are the checksum hex.
    char checksum_chars_[2];
    uint8_t checksum_char_count_ = 0;

    GNSSFix fix_;
    uint32_t timestamp_ms_ = 0;
};
