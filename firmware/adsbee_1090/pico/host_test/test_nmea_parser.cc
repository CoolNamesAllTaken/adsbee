#include <cstring>

#include "gtest/gtest.h"
#include "nmea_parser.hh"

namespace {

// Feed an entire NMEA sentence (including a trailing CRLF) byte-by-byte into the parser and return
// the SentenceType reported on the terminating byte.
NMEAParser::SentenceType FeedSentence(NMEAParser& parser, const char* sentence) {
    NMEAParser::SentenceType result = NMEAParser::kSentenceNone;
    for (const char* p = sentence; *p != '\0'; p++) {
        NMEAParser::SentenceType r = parser.IngestByte(*p);
        if (r != NMEAParser::kSentenceNone) result = r;
    }
    return result;
}

}  // namespace

TEST(NMEAParser, ParsesGPGGA) {
    NMEAParser parser;
    parser.SetTimestampMs(1000);
    // Standard GPS GGA with a valid fix at ~48.1173N, 11.5167E, 545.4m altitude, 8 satellites.
    auto type = FeedSentence(
        parser, "$GPGGA,123519,4807.038,N,01131.000,E,1,08,0.9,545.4,M,46.9,M,,*47\r\n");
    EXPECT_EQ(type, NMEAParser::kSentenceGGA);

    const NMEAParser::GNSSFix& fix = parser.fix();
    EXPECT_TRUE(fix.valid);
    EXPECT_EQ(fix.num_satellites, 8);
    EXPECT_EQ(fix.fix_quality, 1);
    EXPECT_NEAR(fix.latitude_deg, 48.1173f, 0.001f);
    EXPECT_NEAR(fix.longitude_deg, 11.5167f, 0.001f);
    EXPECT_NEAR(fix.altitude_ft, static_cast<int32_t>(545.4f * 3.28084f), 2);
    EXPECT_EQ(fix.last_update_timestamp_ms, 1000u);
}

TEST(NMEAParser, ParsesGPRMC) {
    NMEAParser parser;
    auto type = FeedSentence(
        parser, "$GPRMC,123519,A,4807.038,N,01131.000,E,022.4,084.4,230394,003.1,W*6A\r\n");
    EXPECT_EQ(type, NMEAParser::kSentenceRMC);

    const NMEAParser::GNSSFix& fix = parser.fix();
    EXPECT_TRUE(fix.valid);
    EXPECT_NEAR(fix.latitude_deg, 48.1173f, 0.001f);
    EXPECT_NEAR(fix.longitude_deg, 11.5167f, 0.001f);
    EXPECT_EQ(fix.speed_kts, 22);          // 022.4 knots truncated to int.
    EXPECT_NEAR(fix.heading_deg, 84.4f, 0.1f);
}

// Multi-constellation talker IDs (GN/GL/GA) must parse the same as GP.
TEST(NMEAParser, TalkerIdAgnostic) {
    NMEAParser parser;
    auto type = FeedSentence(
        parser, "$GNRMC,123519,A,4807.038,N,01131.000,E,010.0,090.0,230394,,,A*66\r\n");
    EXPECT_EQ(type, NMEAParser::kSentenceRMC);
    EXPECT_TRUE(parser.fix().valid);
    EXPECT_NEAR(parser.fix().latitude_deg, 48.1173f, 0.001f);
}

// A NMEA 4.11-style sentence with extra appended trailing fields must still parse the leading
// fields and ignore the extras.
TEST(NMEAParser, ToleratesExtraTrailingFields) {
    NMEAParser parser;
    // GGA with extra trailing fields after the standard layout (checksum recomputed to be ignored
    // by feeding a sentence with no '*' so the tolerant path accepts it).
    auto type = FeedSentence(
        parser, "$GNGGA,123519,4807.038,N,01131.000,E,1,12,0.8,100.0,M,46.9,M,,,EXTRA,FIELDS\r\n");
    EXPECT_EQ(type, NMEAParser::kSentenceGGA);
    EXPECT_TRUE(parser.fix().valid);
    EXPECT_EQ(parser.fix().num_satellites, 12);
}

// A sentence with an incorrect checksum must be rejected (fix unchanged).
TEST(NMEAParser, RejectsBadChecksum) {
    NMEAParser parser;
    // Establish a known-good fix first.
    FeedSentence(parser, "$GPGGA,123519,4807.038,N,01131.000,E,1,08,0.9,545.4,M,46.9,M,,*47\r\n");
    ASSERT_TRUE(parser.fix().valid);
    float good_lat = parser.fix().latitude_deg;

    // Now feed a sentence with a deliberately wrong checksum (*00); it must be rejected.
    auto type = FeedSentence(
        parser, "$GPGGA,123519,0000.000,S,00000.000,W,1,08,0.9,1.0,M,46.9,M,,*00\r\n");
    EXPECT_EQ(type, NMEAParser::kSentenceChecksumFail);
    // Fix must be unchanged by the rejected sentence.
    EXPECT_EQ(parser.fix().latitude_deg, good_lat);
}

// A GGA reporting no fix (quality 0) must mark the fix invalid.
TEST(NMEAParser, NoFixMarksInvalid) {
    NMEAParser parser;
    auto type = FeedSentence(parser, "$GPGGA,123519,,,,,0,00,,,M,,M,,*6B\r\n");
    EXPECT_EQ(type, NMEAParser::kSentenceGGA);
    EXPECT_FALSE(parser.fix().valid);
}

// Unknown sentence types are reported as such without disturbing the fix.
TEST(NMEAParser, UnknownSentenceType) {
    NMEAParser parser;
    auto type = FeedSentence(parser, "$GPVTG,084.4,T,,M,022.4,N,041.5,K*6C\r\n");
    EXPECT_EQ(type, NMEAParser::kSentenceUnknown);
}
