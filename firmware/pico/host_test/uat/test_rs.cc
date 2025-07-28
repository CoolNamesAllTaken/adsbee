#include "gtest/gtest.h"
#include "rs.hpp"

TEST(ReedSolomon, EncodeDecode) {
    constexpr uint8_t msg_length = 10;
    constexpr uint8_t ecc_length = 4;
    RS::ReedSolomon<msg_length, ecc_length> rs;

    uint8_t message[msg_length] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
    uint8_t encoded[msg_length + ecc_length];
    uint8_t decoded[msg_length];

    rs.Encode(message, encoded);
    ASSERT_EQ(rs.Decode(encoded, decoded), 0);

    for (uint8_t i = 0; i < msg_length; i++) {
        ASSERT_EQ(message[i], decoded[i]);
    }
}