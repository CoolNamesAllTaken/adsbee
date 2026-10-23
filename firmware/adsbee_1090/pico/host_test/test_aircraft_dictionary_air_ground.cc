#include <climits>
#include <cstdio>
#include <cstring>
#include <string>

#include "aircraft_dictionary.hh"
#include "aircraftjson_utils.hh"
#include "asterix_utils.hh"
#include "crc.hh"
#include "decode_utils.hh"
#include "gdl90_utils.hh"
#include "gtest/gtest.h"
#include "hal_god_powers.hh"
#include "mode_s_packet.hh"

// Air/ground: ADS-B position and velocity messages decide; Mode S replies (flight status, vertical status, DF11
// capability) only when no ADS-B has given air/ground for ModeSAircraft::kADSBAirGroundHoldMs.
namespace {

// One aircraft heard live: ICAO 0xACF146, 10,050 ft.
constexpr uint32_t kICAO = 0xACF146;
const char* kEvenPosition = "8DACF1465837A13F501C6AD4EA7A";
const char* kOddPosition = "8DACF1465837A4D3B6CA231EE8BD";
const char* kNextOddPosition = "8DACF1465837A4D43ECA414BE26A";  // 2.2 s after kOddPosition.
const char* kVelocity = "8DACF14699088C26800C045E7AA1";

// 13-bit altitude code (AC) with the Q bit set: 25 ft steps.
uint16_t AltitudeCode(int32_t altitude_ft) {
    uint16_t n = (altitude_ft + 1000) / 25;
    return ((n >> 5) << 7) | (((n >> 4) & 1) << 5) | (1 << 4) | (n & 0xF);
}

// Hex of a frame whose last 24 bits are the CRC of the rest, XORed with `address` (address parity), or the plain CRC
// (address 0, as in DF11 with interrogator code 0).
std::string Frame(const uint8_t* data, uint16_t num_data_bytes, uint32_t address) {
    uint32_t parity = (crc24(data, num_data_bytes) ^ address) & 0xFFFFFF;
    char hex[29] = {0};
    int n = 0;
    for (uint16_t i = 0; i < num_data_bytes; i++) {
        n += snprintf(hex + n, sizeof(hex) - n, "%02X", data[i]);
    }
    snprintf(hex + n, sizeof(hex) - n, "%06X", parity);
    return std::string(hex);
}

// First 32 bits: DF (5 bits), a 3-bit field (FS or CA, or VS in its top bit for DF0/16), then 24 bits.
std::string Reply(uint8_t df, uint8_t field3, uint32_t low24, bool long_frame = false) {
    uint32_t word = (static_cast<uint32_t>(df) << 27) | (static_cast<uint32_t>(field3 & 0b111) << 24) | low24;
    uint8_t data[11] = {static_cast<uint8_t>(word >> 24), static_cast<uint8_t>(word >> 16),
                        static_cast<uint8_t>(word >> 8), static_cast<uint8_t>(word)};
    return Frame(data, long_frame ? 11 : 4, df == 11 ? 0 : kICAO);
}

std::string AltitudeReply(uint8_t flight_status, int32_t altitude_ft, bool comm_b = false) {
    return Reply(comm_b ? 20 : 4, flight_status, AltitudeCode(altitude_ft), comm_b);
}
std::string IdentityReply(uint8_t flight_status, bool comm_b = false) {
    return Reply(comm_b ? 21 : 5, flight_status, 0x0A6A, comm_b);  // Some squawk.
}
// DF0/16: VS is the bit after DF; the 3-bit field holds VS, CC and a spare bit.
std::string AirAirReply(bool on_ground, int32_t altitude_ft, bool long_range = false) {
    return Reply(long_range ? 16 : 0, on_ground ? 0b100 : 0, AltitudeCode(altitude_ft), long_range);
}
std::string AllCallReply(uint8_t capability, uint32_t address = kICAO) { return Reply(11, capability, address); }

// Airborne position with the ME replaced by a surface position (TC 7), parity recomputed.
std::string SurfacePosition() {
    DecodedModeSPacket airborne(kEvenPosition);
    uint8_t data[11];
    for (uint16_t i = 0; i < 11; i++) {
        data[i] = airborne.raw.buffer[i / 4] >> (24 - 8 * (i % 4));
    }
    memset(data + 4, 0, 7);
    data[4] = 7 << 3;  // TC 7, movement and track unknown, CPR left at zero.
    return Frame(data, 11, 0);
}

}  // namespace

class AirGround : public ::testing::Test {
   protected:
    void SetUp() override {
        set_time_since_boot_ms(100e3);
        ASSERT_TRUE(Ingest(kEvenPosition));
        inc_time_since_boot_ms(500);
        ASSERT_TRUE(Ingest(kOddPosition));
        inc_time_since_boot_ms(500);
        ASSERT_TRUE(Ingest(kVelocity));
        ASSERT_NE(Aircraft(), nullptr);
        ASSERT_TRUE(Aircraft()->HasBitFlag(ModeSAircraft::kBitFlagPositionValid));
        ASSERT_TRUE(Airborne());
    }

    bool Ingest(const std::string& hex) {
        DecodedModeSPacket packet(hex.c_str());
        packet.raw.mlat_48mhz_64bit_counts = static_cast<uint64_t>(get_time_since_boot_ms()) * 48000;  // CPR pairing.
        return dictionary.IngestDecodedModeSPacket(packet);
    }
    ModeSAircraft* Aircraft(uint32_t address = kICAO) {
        return dictionary.GetAircraftPtr<ModeSAircraft>(Aircraft::ICAOToUID(address, Aircraft::kAircraftTypeModeS),
                                                        false);
    }
    bool Airborne(uint32_t address = kICAO) { return Aircraft(address)->HasBitFlag(ModeSAircraft::kBitFlagIsAirborne); }
    void PastADSBHold() { inc_time_since_boot_ms(ModeSAircraft::kADSBAirGroundHoldMs + 1); }

    AircraftDictionary dictionary;
};

TEST(AirGroundFrames, BuildersMakeValidReplies) {
    DecodedModeSPacket altitude(AltitudeReply(1, 31375).c_str());
    EXPECT_EQ(altitude.downlink_format, 4);
    EXPECT_EQ(altitude.icao_address, kICAO);
    EXPECT_EQ(ModeSAltitudeReplyPacket(altitude).altitude_ft, 31375);
    EXPECT_FALSE(ModeSAltitudeReplyPacket(altitude).is_airborne);
    DecodedModeSPacket comm_b(AltitudeReply(0, 500, true).c_str());
    EXPECT_EQ(comm_b.downlink_format, 20);
    EXPECT_EQ(comm_b.icao_address, kICAO);
    DecodedModeSPacket air_air(AirAirReply(true, 1000, true).c_str());
    EXPECT_EQ(air_air.downlink_format, 16);
    EXPECT_EQ(air_air.icao_address, kICAO);
    DecodedModeSPacket all_call(AllCallReply(5).c_str());
    EXPECT_TRUE(all_call.is_valid);
    EXPECT_EQ(all_call.icao_address, kICAO);
    DecodedModeSPacket surface(SurfacePosition().c_str());
    EXPECT_TRUE(surface.is_valid);
    EXPECT_EQ(ModeSADSBPacket(surface).type_code, 7);
}

TEST_F(AirGround, ModeSGroundRepliesDontOverrideADSB) {
    for (const std::string& reply :
         {AltitudeReply(1, 10050), AltitudeReply(3, 10050), AltitudeReply(1, 10050, true), IdentityReply(1),
          IdentityReply(1, true), AirAirReply(true, 10050), AirAirReply(true, 10050, true), AllCallReply(4)}) {
        SCOPED_TRACE(reply);
        inc_time_since_boot_ms(100);
        EXPECT_TRUE(Ingest(reply));
        EXPECT_TRUE(Airborne());
    }
}

TEST_F(AirGround, ModeSReplyKeepsTheCPRPair) {
    uint32_t position_ms = Aircraft()->last_position_update_ms;
    inc_time_since_boot_ms(1000);
    ASSERT_TRUE(Ingest(AltitudeReply(1, 10050)));
    inc_time_since_boot_ms(1200);
    ASSERT_TRUE(Ingest(kNextOddPosition));
    EXPECT_GT(Aircraft()->last_position_update_ms, position_ms);  // Even + next odd still decode.
}

TEST_F(AirGround, ModeSDecidesOnceADSBIsQuiet) {
    PastADSBHold();
    ASSERT_TRUE(Ingest(AltitudeReply(1, 500)));
    EXPECT_FALSE(Airborne());
    inc_time_since_boot_ms(100);
    ASSERT_TRUE(Ingest(IdentityReply(0)));
    EXPECT_TRUE(Airborne());
    inc_time_since_boot_ms(100);
    ASSERT_TRUE(Ingest(AirAirReply(true, 500)));
    EXPECT_FALSE(Airborne());
    inc_time_since_boot_ms(100);
    ASSERT_TRUE(Ingest(AllCallReply(5)));
    EXPECT_TRUE(Airborne());
}

TEST_F(AirGround, ModeSGroundAboveMaxGroundAltitudeIsIgnored) {
    PastADSBHold();
    // The reply's own altitude.
    ASSERT_TRUE(Ingest(AltitudeReply(1, 31375, true)));
    EXPECT_TRUE(Airborne());
    ASSERT_TRUE(Ingest(AirAirReply(true, 31375)));
    EXPECT_TRUE(Airborne());
    // No altitude in the reply: the last baro altitude.
    ASSERT_TRUE(Ingest(AltitudeReply(0, 31375)));
    ASSERT_TRUE(Ingest(IdentityReply(1)));
    EXPECT_TRUE(Airborne());
    ASSERT_TRUE(Ingest(AllCallReply(4)));
    EXPECT_TRUE(Airborne());
    // At or below the limit, ground is taken.
    ASSERT_TRUE(Ingest(AltitudeReply(1, ModeSAircraft::kMaxGroundAltitudeFt)));
    EXPECT_FALSE(Airborne());
}

TEST_F(AirGround, ADSBSurfacePositionStillLandsAtOnce) {
    inc_time_since_boot_ms(100);
    ASSERT_TRUE(Ingest(SurfacePosition()));
    EXPECT_FALSE(Airborne());
    // A Mode S "airborne" doesn't override the surface position either.
    inc_time_since_boot_ms(100);
    ASSERT_TRUE(Ingest(AltitudeReply(0, 100)));
    ASSERT_TRUE(Ingest(AllCallReply(5)));
    EXPECT_FALSE(Airborne());
    // Airborne ADS-B takes off at once.
    inc_time_since_boot_ms(100);
    ASSERT_TRUE(Ingest(kVelocity));
    EXPECT_TRUE(Airborne());
}

TEST_F(AirGround, AllCallCapabilityWithoutADSB) {
    constexpr uint32_t kOther = 0xA12345;
    ASSERT_TRUE(Ingest(AllCallReply(5, kOther)));
    EXPECT_TRUE(Airborne(kOther));
    ASSERT_TRUE(Ingest(AllCallReply(6, kOther)));  // Air or ground: no change.
    EXPECT_TRUE(Airborne(kOther));
    ASSERT_TRUE(Ingest(AllCallReply(4, kOther)));
    EXPECT_FALSE(Airborne(kOther));
    ASSERT_TRUE(Ingest(AllCallReply(7, kOther)));
    EXPECT_FALSE(Airborne(kOther));
}

// Every output reads the same state.
// On-ground as each output reports it: JSON on_ground, ASTERIX GBS, GDL90 not-airborne.
struct OutputGround {
    bool json, asterix, gdl90;
};

OutputGround OutputsOnGround(const ModeSAircraft& aircraft) {
    OutputGround out = {};
    char json[1024];
    EXPECT_GT(WriteAircraftJSONModeSAircraftStr(json, aircraft), 0);
    out.json = strstr(json, "\"on_ground\":1") != nullptr;

    ASTERIXReporter::ReportContext ctx;
    ctx.sac = 1;
    ctx.sic = 2;
    ctx.timestamp_ms = get_time_since_boot_ms();
    ASTERIXReporter::CAT021TargetReport report;
    ModeSAircraft positioned = aircraft;  // ASTERIX reports only aircraft with a position.
    positioned.WriteBitFlag(ModeSAircraft::kBitFlagPositionValid, true);
    EXPECT_TRUE(ASTERIXReporter::BuildCAT021Report(report, positioned, ctx));
    out.asterix = report.on_ground;

    GDL90Reporter gdl90;
    uint8_t frame[GDL90Reporter::kGDL90MessageMaxLenBytes];
    uint16_t frame_len = gdl90.WriteGDL90TargetReportMessage(frame, sizeof(frame), aircraft, false);
    EXPECT_GT(frame_len, 0);
    uint8_t msg[GDL90Reporter::kGDL90MessageMaxLenBytes];
    uint16_t msg_len = 0;
    for (uint16_t i = 1; i + 1 < frame_len; i++) {  // Strip flag bytes and escapes.
        msg[msg_len++] = frame[i] == 0x7D ? frame[++i] ^ 0x20 : frame[i];
    }
    EXPECT_GE(msg_len, 13);
    out.gdl90 = msg_len >= 13 && !(msg[12] & 0b1000);  // Misc indicators: airborne bit.
    return out;
}

TEST_F(AirGround, OutputsKeepADSBAirborneAfterAModeSGroundReply) {
    inc_time_since_boot_ms(100);
    ASSERT_TRUE(Ingest(AltitudeReply(1, 10050, true)));
    OutputGround out = OutputsOnGround(*Aircraft());
    EXPECT_FALSE(out.json);
    EXPECT_FALSE(out.asterix);
    EXPECT_FALSE(out.gdl90);
}

TEST_F(AirGround, NewAircraftIsNotOnGroundUntilAMessageSaysSo) {
    // 0.9.1-rc9 showed every new aircraft on the ground until its first airborne ADS-B message, and the web UI kept
    // that on_ground:1 after it.
    constexpr uint32_t kOther = 0xA12345;
    ASSERT_TRUE(Ingest(AllCallReply(6, kOther)));  // CA=6: air or ground.
    const ModeSAircraft* other = Aircraft(kOther);
    ASSERT_NE(other, nullptr);
    EXPECT_FALSE(other->IsOnGround());
    OutputGround out = OutputsOnGround(*other);
    EXPECT_FALSE(out.json);
    EXPECT_FALSE(out.asterix);
    EXPECT_FALSE(out.gdl90);

    ASSERT_TRUE(Ingest(AllCallReply(4, kOther)));  // CA=4: on the ground.
    EXPECT_TRUE(other->IsOnGround());
    out = OutputsOnGround(*other);
    EXPECT_TRUE(out.json);
    EXPECT_TRUE(out.asterix);
    EXPECT_TRUE(out.gdl90);
}
