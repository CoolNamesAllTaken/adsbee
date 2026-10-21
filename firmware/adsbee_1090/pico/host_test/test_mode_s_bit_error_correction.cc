#include <cstdio>
#include <cstring>
#include <random>
#include <string>

#include "aircraft_dictionary.hh"
#include "crc.hh"
#include "gtest/gtest.h"
#include "hal_god_powers.hh"
#include "mode_s_bit_errors.hh"
#include "mode_s_packet.hh"
#include "mode_s_packet_decoder.hh"

namespace {

// One aircraft heard live: ICAO 0xACF146, callsign SKW4790, 10,050 ft, squawk 4502.
constexpr uint32_t kICAO = 0xACF146;
const char* kEvenPosition = "8DACF1465837A13F501C6AD4EA7A";
const char* kOddPosition = "8DACF1465837A4D3B6CA231EE8BD";
const char* kNextOddPosition = "8DACF1465837A4D43ECA414BE26A";  // 2.2 s after kOddPosition.
const char* kVelocity = "8DACF14699088C26800C045E7AA1";
const char* kNextVelocity = "8DACF14699088C26C00404A4EEF3";
const char* kCallsign = "8DACF146224CB5F4DF9C2091E65D";
const char* kAltitudeReply = "200006BA0EF1C6";  // DF4, 10,050 ft.
const char* kIdentityReply = "280000A68A6AD5";  // DF5, squawk 4502.

RawModeSPacket Raw(const char* hex) { return DecodedModeSPacket(hex).raw; }

RawModeSPacket Flip(RawModeSPacket raw, std::initializer_list<uint16_t> bits) {
    for (uint16_t bit : bits) {
        flip_bit(raw.buffer, bit);
    }
    return raw;
}

bool SameBits(const RawModeSPacket& a, const RawModeSPacket& b) {
    return a.buffer_len_bytes == b.buffer_len_bytes && memcmp(a.buffer, b.buffer, a.buffer_len_bytes) == 0;
}

// An extended squitter with its ME field replaced and a correct parity field.
RawModeSPacket WithME(const char* hex, uint64_t me) {
    RawModeSPacket raw = Raw(hex);
    raw.buffer[1] = static_cast<uint32_t>(me >> 24);
    raw.buffer[2] = static_cast<uint32_t>(me << 8);
    uint8_t bytes[14];
    for (uint16_t i = 0; i < 14; i++) {
        bytes[i] = raw.buffer[i / 4] >> (24 - 8 * (i % 4));
    }
    uint32_t parity = crc24(bytes, 11);
    raw.buffer[2] = (raw.buffer[2] & 0xFFFFFF00) | (parity >> 16);
    raw.buffer[3] = (parity & 0xFFFF) << 16;
    return raw;
}

// A 56 bit reply with a correct address parity field for the address.
RawModeSPacket WithAddressParity(RawModeSPacket raw, uint32_t address) {
    uint8_t bytes[4];
    for (uint16_t i = 0; i < 4; i++) {
        bytes[i] = raw.buffer[0] >> (24 - 8 * i);
    }
    raw.buffer[1] = ((crc24(bytes, 4) ^ address) & 0xFFFFFF) << 8;
    return raw;
}

// Airborne position ME with another barometric altitude (25 ft steps, Q bit set).
uint64_t WithAltitude(uint64_t me, int32_t altitude_ft) {
    uint32_t n = (altitude_ft + 1000) / 25;
    uint64_t code = ((n >> 4) << 5) | (1 << 4) | (n & 0xF);
    return (me & ~(0xFFFull << 36)) | (code << 36);
}

uint64_t ME(const char* hex) {
    RawModeSPacket raw = Raw(hex);
    return (static_cast<uint64_t>(raw.buffer[1]) << 24) | (raw.buffer[2] >> 8);
}

// Packet as the decoder hands it over: run through the decoder's corrections.
DecodedModeSPacket Decode(const RawModeSPacket& raw, bool enable = true) {
    ModeSPacketDecoder decoder({.enable_1090_error_correction = enable});
    decoder.raw_mode_s_packet_in_queue.Enqueue(raw);
    decoder.UpdateDecoderLoop();
    DecodedModeSPacket out;
    if (!decoder.decoded_mode_s_packet_out_queue.Dequeue(out)) {
        out = DecodedModeSPacket();
    }
    return out;
}

class BitErrorCorrection : public ::testing::Test {
   protected:
    void SetUp() override {
        dictionary.SetAddressParityCorrection(true);
        set_time_since_boot_ms(100e3);
        Ingest(Raw(kEvenPosition));
        inc_time_since_boot_ms(500);
        Ingest(Raw(kOddPosition));
        inc_time_since_boot_ms(500);
        Ingest(Raw(kVelocity));
        Ingest(Raw(kCallsign));
        Ingest(Raw(kIdentityReply));
        inc_time_since_boot_ms(1000);
        ASSERT_EQ(dictionary.GetNumAircraft(), 1);
        ModeSAircraft* aircraft = Aircraft();
        ASSERT_NE(aircraft, nullptr);
        ASSERT_TRUE(aircraft->HasBitFlag(ModeSAircraft::kBitFlagPositionValid));
        ASSERT_EQ(aircraft->baro_altitude_ft, 10050);
        ASSERT_STREQ(aircraft->callsign, "SKW4790 ");
        ASSERT_EQ(aircraft->squawk, 4502);
    }

    bool Ingest(const RawModeSPacket& raw) { return Ingest(Decode(raw)); }
    bool Ingest(DecodedModeSPacket packet) {
        packet.raw.mlat_48mhz_64bit_counts = static_cast<uint64_t>(get_time_since_boot_ms()) * 48000;
        last = packet;
        bool ret = dictionary.IngestDecodedModeSPacket(last);
        return ret;
    }
    ModeSAircraft* Aircraft() {
        uint32_t uid = Aircraft::ICAOToUID(kICAO, Aircraft::kAircraftTypeModeS);
        return dictionary.GetAircraftPtr<ModeSAircraft>(uid, false);
    }
    AircraftDictionary::Metrics Metrics() {
        dictionary.Update(get_time_since_boot_ms());
        return dictionary.metrics;
    }

    AircraftDictionary dictionary;
    DecodedModeSPacket last;
};

}  // namespace

TEST(ModeSBitErrors, FindsEveryOneAndTwoBitError) {
    uint16_t bits[2];
    for (uint16_t len_bits : {56, 112}) {
        EXPECT_EQ(ModeSBitErrors::Find(0, len_bits, 5, 2, bits), 0);
        for (uint16_t a = 0; a < len_bits; a++) {
            uint32_t sa = ModeSBitErrors::BitSyndrome(a, len_bits);
            uint16_t n = ModeSBitErrors::Find(sa, len_bits, 5, 2, bits);
            if (a < 5) {
                EXPECT_EQ(n, 0) << "DF bit " << a;
            } else {
                ASSERT_EQ(n, 1) << len_bits << " " << a;
                EXPECT_EQ(bits[0], a);
            }
            for (uint16_t b = a + 1; b < len_bits; b++) {
                n = ModeSBitErrors::Find(sa ^ ModeSBitErrors::BitSyndrome(b, len_bits), len_bits, 5, 2, bits);
                if (a < 5) {
                    EXPECT_EQ(n, 0) << "DF bit " << a;
                    continue;
                }
                ASSERT_EQ(n, 2) << len_bits << " " << a << " " << b;
                EXPECT_EQ(bits[0], a);
                EXPECT_EQ(bits[1], b);
                uint32_t sab = sa ^ ModeSBitErrors::BitSyndrome(b, len_bits);
                EXPECT_EQ(ModeSBitErrors::Find(sab, len_bits, 5, 1, bits), 0);
            }
        }
    }
}

// The code's minimum distance is 6 at 112 bits: no three bit error looks like a one or two bit error.
TEST(ModeSBitErrors, ThreeBitErrorsAreNotCorrected) {
    uint16_t bits[2];
    for (uint16_t a = 0; a < 112; a++) {
        for (uint16_t b = a + 1; b < 112; b++) {
            uint32_t sab = ModeSBitErrors::BitSyndrome(a, 112) ^ ModeSBitErrors::BitSyndrome(b, 112);
            for (uint16_t c = b + 1; c < 112; c++) {
                ASSERT_EQ(ModeSBitErrors::Find(sab ^ ModeSBitErrors::BitSyndrome(c, 112), 112, 0, 2, bits), 0);
            }
        }
    }
}

TEST(ModeSBitErrorCorrection, DecoderCorrectsTwoBitErrors) {
    RawModeSPacket good = Raw(kNextOddPosition);
    DecodedModeSPacket out = Decode(Flip(good, {40, 99}));
    EXPECT_TRUE(out.is_valid);
    EXPECT_EQ(out.num_corrected_bits, 2);
    EXPECT_TRUE(SameBits(out.raw, good));

    out = Decode(Flip(good, {40}));
    EXPECT_TRUE(out.is_valid);
    EXPECT_EQ(out.num_corrected_bits, 1);

    // DF bits are never flipped, three bit errors are not corrected, and correction can be turned off.
    EXPECT_FALSE(Decode(Flip(good, {3, 60})).is_valid);
    EXPECT_FALSE(Decode(Flip(good, {40, 60, 99})).is_valid);
    EXPECT_FALSE(Decode(Flip(good, {40, 99}), false).is_valid);
}

TEST_F(BitErrorCorrection, CorrectedFramesUpdateTrackedAircraft) {
    EXPECT_TRUE(Ingest(Flip(Raw(kNextOddPosition), {60, 70})));  // CPR latitude bits.
    EXPECT_TRUE(last.is_valid);
    EXPECT_TRUE(Aircraft()->HasBitFlag(ModeSAircraft::kBitFlagUpdatedPosition));
    EXPECT_TRUE(Ingest(Flip(Raw(kNextVelocity), {45, 108})));
    EXPECT_TRUE(Ingest(Flip(Raw(kCallsign), {50, 51})));
    EXPECT_TRUE(Ingest(Flip(Raw(kNextVelocity), {77})));
    AircraftDictionary::Metrics metrics = Metrics();
    EXPECT_EQ(metrics.corrected_frames[AircraftDictionary::kCorrectionExtendedSquitter2Bit], 3);
    EXPECT_EQ(metrics.corrected_frames[AircraftDictionary::kCorrectionExtendedSquitter1Bit], 1);
    EXPECT_EQ(metrics.corrected_frames[AircraftDictionary::kCorrectionRejected], 0);
}

TEST_F(BitErrorCorrection, CorrectedFramesNeverStartATrack) {
    for (uint16_t num_bits : {1, 2}) {
        RawModeSPacket other = Raw("8DA2C5B15835C0E39032B3DDA952");  // Another aircraft.
        ASSERT_TRUE(DecodedModeSPacket(other).is_valid);
        EXPECT_FALSE(Ingest(num_bits == 1 ? Flip(other, {50}) : Flip(other, {50, 90})));
        EXPECT_FALSE(last.is_valid) << "Rejected frames must not be forwarded.";
        EXPECT_EQ(dictionary.GetNumAircraft(), 1);
    }
    EXPECT_EQ(Metrics().corrected_frames[AircraftDictionary::kCorrectionRejected], 2);
}

TEST_F(BitErrorCorrection, ImplausibleTwoBitCorrectionsAreRejected) {
    const uint64_t kCPRLatBit = 1ull << 17;  // Lowest bit of the CPR latitude, ME bits 23-39.
    struct {
        const char* name;
        RawModeSPacket raw;
    } cases[] = {
        {"position 100 km away", WithME(kNextOddPosition, ME(kNextOddPosition) ^ (kCPRLatBit << 14))},
        {"altitude 2,000 ft higher", WithME(kNextOddPosition, WithAltitude(ME(kNextOddPosition), 12050))},
        {"speed 100 kt higher", WithME(kNextVelocity, ME(kNextVelocity) + (100ull << 32))},
        {"other callsign", WithME(kCallsign, ME(kCallsign) ^ (1ull << 20))},
        {"aircraft status", Raw("8DACF146E100A600000000E6056B")},
    };
    for (auto& c : cases) {
        ASSERT_TRUE(DecodedModeSPacket(c.raw).is_valid) << c.name;
        DecodedModeSPacket packet = Decode(c.raw);
        packet.num_corrected_bits = 2;  // As if a wrong two bit correction had produced it.
        EXPECT_FALSE(Ingest(packet)) << c.name;
        EXPECT_FALSE(last.is_valid) << c.name;
    }
    EXPECT_EQ(Aircraft()->baro_altitude_ft, 10050);
    EXPECT_STREQ(Aircraft()->callsign, "SKW4790 ");
    EXPECT_EQ(Metrics().corrected_frames[AircraftDictionary::kCorrectionRejected], 5);
}

TEST_F(BitErrorCorrection, StalePositionsCantCheckTwoBitFixes) {
    inc_time_since_boot_ms(11e3);  // Position and velocity older than 10 s.
    EXPECT_FALSE(Ingest(Flip(Raw(kNextOddPosition), {60, 70})));
    EXPECT_FALSE(Ingest(Flip(Raw(kNextVelocity), {45, 108})));
    EXPECT_TRUE(Ingest(Flip(Raw(kNextOddPosition), {60})));  // One bit fixes are only turned down by a disagreement.
}

TEST_F(BitErrorCorrection, OneBitFixesThatDisagreeWithTheTrackAreRejected) {
    RawModeSPacket far = WithME(kNextOddPosition, WithAltitude(ME(kNextOddPosition), 15050));
    EXPECT_FALSE(Ingest(Flip(far, {60})));
    EXPECT_EQ(Aircraft()->baro_altitude_ft, 10050);
}

TEST_F(BitErrorCorrection, AddressParityRepliesKeepTheAirGroundState) {
    // Flight status 1: on the ground.
    RawModeSPacket on_ground = WithAddressParity(Flip(Raw(kAltitudeReply), {7}), kICAO);
    EXPECT_FALSE(Ingest(Flip(on_ground, {45})));
    EXPECT_TRUE(Aircraft()->HasBitFlag(ModeSAircraft::kBitFlagIsAirborne));
}

TEST_F(BitErrorCorrection, AddressParityRepliesAreCorrected) {
    RawModeSPacket altitude = Raw(kAltitudeReply);
    EXPECT_TRUE(Ingest(Flip(altitude, {9})));  // Downlink request.
    EXPECT_TRUE(last.is_valid);
    EXPECT_EQ(last.icao_address, kICAO);
    EXPECT_TRUE(SameBits(last.raw, altitude));
    EXPECT_TRUE(Ingest(Flip(altitude, {30, 40})));  // Altitude code and parity.
    EXPECT_TRUE(Ingest(Flip(Raw(kIdentityReply), {22, 50})));
    AircraftDictionary::Metrics metrics = Metrics();
    EXPECT_EQ(metrics.corrected_frames[AircraftDictionary::kCorrectionAddressParity1Bit], 1);
    EXPECT_EQ(metrics.corrected_frames[AircraftDictionary::kCorrectionAddressParity2Bit], 2);
}

TEST_F(BitErrorCorrection, AddressParityNeedsAPlausibleAltitudeAndTheSameSquawk) {
    // Bit 20 is in the altitude code: the corrected altitude is far from the track.
    RawModeSPacket altitude = WithAddressParity(Flip(Raw(kAltitudeReply), {20}), kICAO);
    ASSERT_EQ(DecodedModeSPacket(altitude).icao_address, kICAO);
    EXPECT_FALSE(Ingest(Flip(altitude, {45})));

    RawModeSPacket identity = WithAddressParity(Flip(Raw(kIdentityReply), {22}), kICAO);  // Another squawk.
    EXPECT_FALSE(Ingest(Flip(identity, {45})));
    EXPECT_FALSE(last.is_valid);
    EXPECT_EQ(Aircraft()->squawk, 4502);
}

// An untracked aircraft whose address is one bit from a tracked one looks like a one bit error in the parity field.
TEST_F(BitErrorCorrection, RepeatedNearbyAddressesAreNotCorrected) {
    RawModeSPacket neighbor = WithAddressParity(Raw(kAltitudeReply), kICAO ^ 0x000100);
    EXPECT_TRUE(Ingest(neighbor));
    for (uint16_t i = 0; i < 5; i++) {
        inc_time_since_boot_ms(1000);
        EXPECT_FALSE(Ingest(neighbor));
    }
    EXPECT_TRUE(Ingest(Flip(Raw(kAltitudeReply), {9})));  // Errors outside the parity field are still corrected.
}

TEST_F(BitErrorCorrection, AddressParitySearchesAreLimited) {
    RawModeSPacket reply = Flip(Raw(kAltitudeReply), {9});
    dictionary.Update(get_time_since_boot_ms());
    for (uint16_t i = 0; i < AircraftDictionary::kMaxAddressParityCorrectionAttemptsPerUpdate; i++) {
        EXPECT_TRUE(Ingest(reply));
    }
    EXPECT_FALSE(Ingest(reply));
    AircraftDictionary::Metrics metrics = Metrics();
    EXPECT_EQ(metrics.corrected_frames[AircraftDictionary::kCorrectionSkipped], 1);
    EXPECT_TRUE(Ingest(reply));  // The update reset the limit.
}

TEST_F(BitErrorCorrection, AddressParityCorrectionCanBeTurnedOff) {
    dictionary.SetAddressParityCorrection(false);
    EXPECT_FALSE(Ingest(Flip(Raw(kAltitudeReply), {9})));
    EXPECT_FALSE(last.is_valid);
}

// Random replies must not be turned into frames from tracked aircraft.
TEST_F(BitErrorCorrection, RandomAddressParityRepliesAreRejected) {
    std::mt19937 rng(718);
    for (uint32_t i = 1; i < 50; i++) {
        ModeSAircraft* a = dictionary.GetAircraftPtr<ModeSAircraft>(
            Aircraft::ICAOToUID(kICAO ^ (i * 0x10101), Aircraft::kAircraftTypeModeS), true);
        a->baro_altitude_ft = 1000 * static_cast<int32_t>(i);
        a->WriteBitFlag(ModeSAircraft::kBitFlagBaroAltitudeValid, true);
        a->last_message_timestamp_ms = get_time_since_boot_ms();
    }
    uint16_t accepted = 0;
    for (uint16_t i = 0; i < 20000; i++) {
        if (i % 200 == 0) {
            dictionary.Update(get_time_since_boot_ms());  // Resets the search limit.
        }
        RawModeSPacket raw = Raw(kAltitudeReply);
        raw.buffer[0] = (raw.buffer[0] & 0xF8000000) | (rng() & 0x07FFFFFF);
        raw.buffer[1] = rng() & 0xFFFFFF00;
        accepted += Ingest(raw);
    }
    // About 1,326 * 50 / 2^24 = 0.4 % of random replies are within two bits of an aircraft; the altitude check passes
    // about 1 % of those.
    EXPECT_LE(accepted, 3);
    EXPECT_EQ(dictionary.GetNumAircraft(), 50);
}

TEST_F(BitErrorCorrection, RandomExtendedSquittersAreRejected) {
    std::mt19937 rng(1090);
    uint16_t corrected = 0;
    uint16_t accepted = 0;
    for (uint32_t i = 0; i < 100000; i++) {
        RawModeSPacket raw = Raw(kNextOddPosition);  // Tracked address, random content and parity.
        raw.buffer[1] = rng();
        raw.buffer[2] = rng();
        raw.buffer[3] = rng() & 0xFFFF0000;
        DecodedModeSPacket packet = Decode(raw);
        if (packet.num_corrected_bits == 0 || !packet.is_valid) {
            continue;
        }
        corrected++;
        if (((packet.raw.buffer[0]) & 0xFFFFFF) != kICAO) {
            continue;  // The correction moved the address: unknown aircraft, covered elsewhere.
        }
        accepted += Ingest(packet);
    }
    EXPECT_GT(corrected, 10);  // About 5,800 * 100,000 / 2^24 = 34.
    EXPECT_EQ(accepted, 0);
}
