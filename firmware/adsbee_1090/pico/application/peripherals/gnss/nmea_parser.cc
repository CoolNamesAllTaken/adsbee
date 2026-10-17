#include "nmea_parser.hh"

#include <cmath>    // For sqrtf.
#include <cstdlib>  // For strtol, strtof, atoi.
#include <cstring>  // For strlen, strncmp.

namespace {

// Convert a single hex character to its nibble value, or -1 if not a hex digit.
int8_t HexCharToNibble(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

// Parse an NMEA latitude/longitude field in ddmm.mmmm / dddmm.mmmm format plus a hemisphere
// character ('N'/'S'/'E'/'W') into signed decimal degrees. Returns false if either field is empty.
bool ParseLatLon(const char* coord, const char* hemi, double& out_deg) {
    if (coord == nullptr || coord[0] == '\0' || hemi == nullptr || hemi[0] == '\0') {
        return false;
    }
    // Degrees are all digits before the decimal point except the last two (which are minutes).
    const char* dot = strchr(coord, '.');
    uint16_t int_digits = dot ? static_cast<uint16_t>(dot - coord) : static_cast<uint16_t>(strlen(coord));
    if (int_digits < 3) return false;  // Need at least dd + mm.
    uint16_t deg_digits = int_digits - 2;

    char deg_str[4] = {0};
    if (deg_digits >= sizeof(deg_str)) return false;
    memcpy(deg_str, coord, deg_digits);

    double degrees = static_cast<double>(atoi(deg_str));
    double minutes = strtod(coord + deg_digits, nullptr);
    double value = degrees + minutes / 60.0;

    if (hemi[0] == 'S' || hemi[0] == 'W') value = -value;
    out_deg = value;
    return true;
}

constexpr float kMetersToFeet = 3.28084f;

bool ParseUTCTime(const char* field, NMEAParser::GNSSFix& fix, uint32_t timestamp_ms) {
    if (field == nullptr || strlen(field) < 6) return false;
    for (uint8_t i = 0; i < 6; i++) {
        if (field[i] < '0' || field[i] > '9') return false;
    }

    uint8_t hour = static_cast<uint8_t>((field[0] - '0') * 10 + field[1] - '0');
    uint8_t minute = static_cast<uint8_t>((field[2] - '0') * 10 + field[3] - '0');
    uint8_t second = static_cast<uint8_t>((field[4] - '0') * 10 + field[5] - '0');
    if (hour > 23 || minute > 59 || second > 60) return false;

    uint16_t millisecond = 0;
    if (field[6] == '.') {
        uint16_t scale = 100;
        for (uint8_t i = 7; field[i] != '\0' && scale > 0; i++, scale /= 10) {
            if (field[i] < '0' || field[i] > '9') break;
            millisecond += static_cast<uint16_t>(field[i] - '0') * scale;
        }
    }

    fix.utc_hour = hour;
    fix.utc_minute = minute;
    fix.utc_second = second;
    fix.utc_millisecond = millisecond;
    fix.utc_time_valid = true;
    fix.utc_time_timestamp_ms = timestamp_ms;
    return true;
}

// RMC date field: ddmmyy.
bool ParseUTCDate(const char* field, NMEAParser::GNSSFix& fix) {
    if (field == nullptr || strlen(field) != 6) return false;
    for (uint8_t i = 0; i < 6; i++) {
        if (field[i] < '0' || field[i] > '9') return false;
    }
    uint8_t day = static_cast<uint8_t>((field[0] - '0') * 10 + field[1] - '0');
    uint8_t month = static_cast<uint8_t>((field[2] - '0') * 10 + field[3] - '0');
    uint8_t year = static_cast<uint8_t>((field[4] - '0') * 10 + field[5] - '0');
    if (day < 1 || day > 31 || month < 1 || month > 12) return false;
    fix.utc_day = day;
    fix.utc_month = month;
    fix.utc_year = 2000 + year;  // Two digit NMEA year: 2000 to 2099.
    fix.utc_date_valid = true;
    return true;
}

// Parses a non-empty decimal field. Returns false if the field is empty or not a number.
bool ParseFloatField(const char* field, float& value) {
    if (field == nullptr || field[0] == '\0') return false;
    char* end = nullptr;
    value = strtof(field, &end);
    return end != field;
}

}  // namespace

NMEAParser::SentenceType NMEAParser::IngestByte(char c) {
    if (c == '$') {
        // Start of a new sentence; reset accumulation state.
        in_sentence_ = true;
        line_len_ = 0;
        running_checksum_ = 0;
        reading_checksum_ = false;
        checksum_char_count_ = 0;
        return kSentenceNone;
    }

    if (!in_sentence_) {
        return kSentenceNone;  // Junk before a '$'; ignore.
    }

    if (c == '\r' || c == '\n') {
        // End of sentence. Validate checksum (if one was provided) then parse.
        bool complete = in_sentence_ && line_len_ > 0;
        in_sentence_ = false;
        if (!complete) return kSentenceNone;

        if (reading_checksum_) {
            if (checksum_char_count_ != 2) return kSentenceChecksumFail;
            int8_t hi = HexCharToNibble(checksum_chars_[0]);
            int8_t lo = HexCharToNibble(checksum_chars_[1]);
            if (hi < 0 || lo < 0) return kSentenceChecksumFail;
            uint8_t expected = static_cast<uint8_t>((hi << 4) | lo);
            if (expected != running_checksum_) return kSentenceChecksumFail;
        }
        // No '*' / checksum present: accept (tolerant of receivers that omit it).
        line_buf_[line_len_] = '\0';
        return ParseLine();
    }

    if (c == '*') {
        // Remainder of the line is the two-character checksum; stop XOR accumulation.
        reading_checksum_ = true;
        return kSentenceNone;
    }

    if (reading_checksum_) {
        if (checksum_char_count_ < 2) {
            checksum_chars_[checksum_char_count_++] = c;
        }
        return kSentenceNone;
    }

    // Body character: accumulate into the line buffer and update the running checksum.
    running_checksum_ ^= static_cast<uint8_t>(c);
    if (line_len_ < kLineBufMaxLen - 1) {
        line_buf_[line_len_++] = c;
    } else {
        // Overflow: drop the sentence to avoid a buffer overrun.
        in_sentence_ = false;
        return kSentenceMalformed;
    }
    return kSentenceNone;
}

NMEAParser::SentenceType NMEAParser::ParseLine() {
    // Split line_buf_ on ',' into field pointers (in place). Field 0 is the address field
    // (talker + sentence type), e.g. "GPGGA".
    char* fields[kMaxNumFields];
    uint8_t num_fields = 0;
    fields[num_fields++] = line_buf_;
    for (uint16_t i = 0; i < line_len_ && num_fields < kMaxNumFields; i++) {
        if (line_buf_[i] == ',') {
            line_buf_[i] = '\0';
            fields[num_fields++] = &line_buf_[i + 1];
        }
    }

    const char* addr = fields[0];
    // Address field is the 2-char talker + 3-char sentence type. Match on the sentence type only
    // (last 3 chars) to be talker-agnostic.
    uint16_t addr_len = static_cast<uint16_t>(strlen(addr));
    if (addr_len < 5) return kSentenceUnknown;
    const char* type = addr + (addr_len - 3);

    if (strncmp(type, "GGA", 3) == 0) {
        return ParseGGA(fields, num_fields);
    }
    if (strncmp(type, "RMC", 3) == 0) {
        return ParseRMC(fields, num_fields);
    }
    if (strncmp(type, "GST", 3) == 0) {
        return ParseGST(fields, num_fields);
    }
    return kSentenceUnknown;
}

// GGA field layout (talker-agnostic):
//   0: address  1: UTC time  2: lat  3: N/S  4: lon  5: E/W  6: fix quality
//   7: num satellites  8: HDOP  9: altitude (MSL)  10: altitude units (M)  11: geoid separation
//   12: geoid separation units (M)  ...
NMEAParser::SentenceType NMEAParser::ParseGGA(const char* const* fields, uint8_t num_fields) {
    if (num_fields < 11) return kSentenceMalformed;

    uint8_t fix_quality = static_cast<uint8_t>(atoi(fields[6]));
    fix_.fix_quality = fix_quality;
    fix_.num_satellites = static_cast<uint8_t>(atoi(fields[7]));
    ParseUTCTime(fields[1], fix_, timestamp_ms_);

    if (fields[9][0] != '\0') {
        float altitude_m = strtof(fields[9], nullptr);
        fix_.altitude_m = altitude_m;
        fix_.altitude_ft = static_cast<int32_t>(altitude_m * kMetersToFeet);
    }
    float geoid_separation_m;
    fix_.geoid_separation_valid = num_fields > 11 && ParseFloatField(fields[11], geoid_separation_m);
    if (fix_.geoid_separation_valid) {
        fix_.geoid_separation_m = geoid_separation_m;
    }

    double lat, lon;
    if (fix_quality > 0 && ParseLatLon(fields[2], fields[3], lat) && ParseLatLon(fields[4], fields[5], lon)) {
        fix_.latitude_deg = lat;
        fix_.longitude_deg = lon;
        fix_.valid = true;
        fix_.last_update_timestamp_ms = timestamp_ms_;
    } else if (fix_quality == 0) {
        fix_.valid = false;
    }
    return kSentenceGGA;
}

// RMC field layout (talker-agnostic):
//   0: address  1: UTC time  2: status (A=valid, V=void)  3: lat  4: N/S  5: lon  6: E/W
//   7: speed over ground (knots)  8: course over ground (deg)  9: date  ... (trailing fields vary)
NMEAParser::SentenceType NMEAParser::ParseRMC(const char* const* fields, uint8_t num_fields) {
    if (num_fields < 10) return kSentenceMalformed;

    bool status_valid = (fields[2][0] == 'A');
    ParseUTCTime(fields[1], fix_, timestamp_ms_);

    if (fields[7][0] != '\0') {
        fix_.speed_kts = static_cast<int32_t>(strtof(fields[7], nullptr));
    }
    if (fields[8][0] != '\0') {
        fix_.heading_deg = strtof(fields[8], nullptr);
    }
    fix_.utc_date_valid = ParseUTCDate(fields[9], fix_);

    double lat, lon;
    if (status_valid && ParseLatLon(fields[3], fields[4], lat) && ParseLatLon(fields[5], fields[6], lon)) {
        fix_.latitude_deg = lat;
        fix_.longitude_deg = lon;
        fix_.valid = true;
        fix_.last_update_timestamp_ms = timestamp_ms_;
    } else if (!status_valid) {
        fix_.valid = false;
    }
    return kSentenceRMC;
}

// GST field layout (talker-agnostic):
//   0: address  1: UTC time  2: RMS of pseudorange residuals  3: error ellipse semi-major (m)
//   4: semi-minor (m)  5: orientation (deg)  6: latitude error (m)  7: longitude error (m)  8: altitude error (m)
NMEAParser::SentenceType NMEAParser::ParseGST(const char* const* fields, uint8_t num_fields) {
    if (num_fields < 9) return kSentenceMalformed;
    float latitude_error_m, longitude_error_m, altitude_error_m;
    if (ParseFloatField(fields[6], latitude_error_m) && ParseFloatField(fields[7], longitude_error_m) &&
        ParseFloatField(fields[8], altitude_error_m)) {
        fix_.latitude_error_m = latitude_error_m;
        fix_.longitude_error_m = longitude_error_m;
        fix_.altitude_error_m = altitude_error_m;
        fix_.accuracy_valid = true;
        fix_.accuracy_timestamp_ms = timestamp_ms_;
    } else {
        fix_.accuracy_valid = false;
    }
    return kSentenceGST;
}

uint32_t NMEAParser::UnixTime(uint16_t year, uint8_t month, uint8_t day, uint8_t hour, uint8_t minute,
                              uint8_t second) {
    // Days from civil (Howard Hinnant's algorithm), valid for the Gregorian calendar.
    int32_t y = static_cast<int32_t>(year) - (month <= 2 ? 1 : 0);
    int32_t era = y / 400;
    uint32_t year_of_era = static_cast<uint32_t>(y - era * 400);
    uint32_t day_of_year = (153 * (month > 2 ? month - 3 : month + 9) + 2) / 5 + day - 1;
    uint32_t day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year;
    int32_t days = era * 146097 + static_cast<int32_t>(day_of_era) - 719468;
    return static_cast<uint32_t>(days) * 86400u + hour * 3600u + minute * 60u + second;
}

bool NMEAParser::PPSEdgeUnixTime(const GNSSFix& fix, uint32_t edge_timestamp_ms, uint32_t& unix_time_s) {
    if (!fix.valid || !fix.utc_time_valid || !fix.utc_date_valid || fix.utc_millisecond != 0) return false;
    uint32_t time_after_edge_ms = fix.utc_time_timestamp_ms - edge_timestamp_ms;
    if (time_after_edge_ms >= 1000) return false;  // Received before the edge (wraps to large), or too late.
    unix_time_s =
        UnixTime(fix.utc_year, fix.utc_month, fix.utc_day, fix.utc_hour, fix.utc_minute, fix.utc_second);
    return true;
}

bool NMEAParser::FixToReceiverPosition(const GNSSFix& fix, ReceiverPosition& position) {
    if (!fix.valid || !fix.geoid_separation_valid) return false;
    position = ReceiverPosition();
    position.source = ReceiverPosition::kSourceGNSS;
    position.latitude_deg = fix.latitude_deg;
    position.longitude_deg = fix.longitude_deg;
    position.height_m = fix.altitude_m + fix.geoid_separation_m;
    // Use GST only if it is about as fresh as the fix (it comes in the same once a second burst, before or after).
    int32_t accuracy_age_ms = static_cast<int32_t>(fix.last_update_timestamp_ms - fix.accuracy_timestamp_ms);
    if (fix.accuracy_valid && accuracy_age_ms > -1500 && accuracy_age_ms < 1500) {
        position.horizontal_accuracy_m =
            sqrtf(fix.latitude_error_m * fix.latitude_error_m + fix.longitude_error_m * fix.longitude_error_m);
        position.vertical_accuracy_m = fix.altitude_error_m;
    }
    return ReceiverPosition::CoordinatesAreValid(position.latitude_deg, position.longitude_deg, position.height_m);
}
