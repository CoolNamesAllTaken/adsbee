#include "../application/comms/at/feed_receiver_id.hh"
#include "gtest/gtest.h"

TEST(FeedReceiverID, ParsesHex) {
    uint8_t id[8] = {0};
    EXPECT_EQ(FeedReceiverID::Parse("BEE00123456789aB", id), FeedReceiverID::kHex);
    const uint8_t want[8] = {0xBE, 0xE0, 0x01, 0x23, 0x45, 0x67, 0x89, 0xAB};
    for (int i = 0; i < 8; i++) EXPECT_EQ(id[i], want[i]) << i;
}

TEST(FeedReceiverID, ParsesDefault) {
    uint8_t id[8] = {1, 2, 3, 4, 5, 6, 7, 8};
    EXPECT_EQ(FeedReceiverID::Parse("DEFAULT", id), FeedReceiverID::kDefault);
    EXPECT_EQ(FeedReceiverID::Parse("default", id), FeedReceiverID::kDefault);
    EXPECT_EQ(id[0], 1);
    EXPECT_EQ(id[7], 8);
}

TEST(FeedReceiverID, RejectsBadValuesWithoutWriting) {
    uint8_t id[8] = {1, 2, 3, 4, 5, 6, 7, 8};
    for (const char* bad : {"", "BEE0012345678", "BEE00123456789ABC", "BEE00123456789AG", "BEE0-0123456789A",
                            "DEFAULTS", "DEFAUL", " BEE00123456789A"}) {
        EXPECT_EQ(FeedReceiverID::Parse(bad, id), FeedReceiverID::kInvalid) << bad;
    }
    for (int i = 0; i < 8; i++) EXPECT_EQ(id[i], i + 1);
}
