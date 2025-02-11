#include "awb_utils.h"
#include "gtest/gtest.h"
#include "nasa_cpr.hh"

// Convenience struct for copy and pasting from the benchmarking tables.
struct GlobalDecodeTest {
    uint32_t awb_evn_lat, awb_evn_lon, enc_evn_lat, enc_evn_lon, awb_odd_lat, awb_odd_lon, enc_odd_lat, enc_odd_lon,
        rpos0_valid, rpos0_lat_awb, rpos0_lon_awb, rpos1_lat_awb, rpos1_lon_awb;
};

TEST(NASACPR, LatLonToAWBAndBack) {
    // Exercise Alternative Weighted Binary conversion utilities.
    float lat_deg = -50.8591f;
    float lon_deg = 179.9999f;

    EXPECT_NEAR(awb2lat(lat2awb(lat_deg)), lat_deg, 1e-4);
    EXPECT_NEAR(awb2lon(lon2awb(lon_deg)), lon_deg, 1e-4);
}

TEST(NASACPR, GlobalDecode) {
    // Could take a lot more lines from this table if we want to:
    // https://github.com/nasa/cpr/blob/master/C/fixed-point/airborne/benchmarks/global-decoding/airborne_globally_decoded_gd_random_positions.csv
    GlobalDecodeTest tests[] = {{0xD31CF9A3, 0x15780D81, 0xF595, 0x8753, 0xD31DA2EF, 0x157B0D92, 0x14FA9, 0x5CFF, 1,
                                 0xD31CF99A, 0x15780E39, 0xD31DA2B6, 0x157B0EC5},
                                {0x3491D63F, 0x8DAB03C9, 0xA45C, 0x1B560, 0x349879F4, 0x8DBE2B2F, 0x3E48, 0x9C49, 1,
                                 0x3491D555, 0x8DAB0000, 0x3498797E, 0x8DBE2AAB}};

    for (GlobalDecodeTest& test : tests) {
        NASACPRDecoder::CPRMessage message0 = {.odd = false, .lat_cpr = test.enc_evn_lat, .lon_cpr = test.enc_evn_lon};
        NASACPRDecoder::CPRMessage message1 = {.odd = true, .lat_cpr = test.enc_odd_lat, .lon_cpr = test.enc_odd_lon};
        NASACPRDecoder::DecodedPosition result;
        bool result_valid = NASACPRDecoder::DecodeAirborneGlobalCPR(message0, message1, result);
        EXPECT_EQ(result_valid, test.rpos0_valid);

        // rpos0 reflects sending msg0 to global decode as even. This matches what we do here.
        if (result_valid) {
            EXPECT_EQ(result.lat_deg, awb2lat(test.rpos0_lat_awb));
            EXPECT_EQ(result.lon_deg, awb2lon(test.rpos0_lon_awb));
        }

        // Test the other way around.
        message0.odd = true;
        message1.odd = false;
        result_valid = NASACPRDecoder::DecodeAirborneGlobalCPR(message0, message1, result);
        // Only rpos0_valid is given in the table. We assume that if rpos0 decode was valid, rpos1 decode will also be
        // valid.
        EXPECT_EQ(result_valid, test.rpos0_valid);

        if (result_valid) {
            EXPECT_EQ(result.lat_deg, awb2lat(test.rpos1_lat_awb));
            EXPECT_EQ(result.lon_deg, awb2lon(test.rpos1_lon_awb));
        }
    }
}