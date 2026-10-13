#include <cstring>

#include "esp32_firmware_check.hh"
#include "gtest/gtest.h"

static constexpr uint32_t kVersion = 0x00090108;
static constexpr uint16_t kHashLen = ESP32FirmwareCheck::kHashLenBytes;

// First 208 Bytes of an ESP-IDF v5.4 application image built by CI.
static const uint8_t kImageStart[] = {
    0xe9, 0x06, 0x02, 0x2f, 0x18, 0x56, 0x37, 0x40, 0xee, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x00, 0x00, 0x63,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x20, 0x00, 0x0e, 0x3c, 0x98, 0x42, 0x0c, 0x00, 0x32, 0x54, 0xcd, 0xab,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x62, 0x65, 0x34, 0x62, 0x30, 0x31,
    0x39, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x61, 0x64, 0x73, 0x62, 0x65, 0x65, 0x5f, 0x65, 0x73, 0x70,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x30, 0x34, 0x3a, 0x33, 0x30, 0x3a, 0x32, 0x36, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x4f, 0x63, 0x74, 0x20, 0x31, 0x32, 0x20, 0x32, 0x30, 0x32, 0x36, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x76, 0x35, 0x2e, 0x34, 0x2e, 0x34, 0x2d, 0x31, 0x33, 0x38, 0x39, 0x2d, 0x67, 0x34, 0x38, 0x39, 0x35, 0x31,
    0x61, 0x38, 0x38, 0x32, 0x38, 0x66, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x61, 0x54, 0xd9, 0xf6,
    0x60, 0x4a, 0xbe, 0x43, 0x19, 0x3b, 0xe6, 0x68, 0x63, 0x51, 0x60, 0x79, 0xc0, 0x0f, 0xfd, 0xd1, 0xbc, 0x67,
    0x99, 0x69, 0x31, 0xe9, 0x1c, 0xe3, 0x07, 0x5d, 0x2c, 0x84};
static const uint8_t kImageStartHash[kHashLen] = {0x61, 0x54, 0xd9, 0xf6, 0x60, 0x4a, 0xbe, 0x43, 0x19, 0x3b, 0xe6,
                                                  0x68, 0x63, 0x51, 0x60, 0x79, 0xc0, 0x0f, 0xfd, 0xd1, 0xbc, 0x67,
                                                  0x99, 0x69, 0x31, 0xe9, 0x1c, 0xe3, 0x07, 0x5d, 0x2c, 0x84};

// The application description is 256 Bytes long; the Bytes after the hash are reserved zeros.
static constexpr uint32_t kImageLen = 32 + 256;

struct Image {
    uint8_t bytes[kImageLen] = {0};
    Image() { memcpy(bytes, kImageStart, sizeof(kImageStart)); }
};

TEST(ESP32FirmwareCheck, ReadsHashFromImage) {
    Image image;
    uint8_t hash[kHashLen] = {0};
    ASSERT_TRUE(ESP32FirmwareCheck::GetImageHash(image.bytes, kImageLen, hash));
    EXPECT_EQ(memcmp(hash, kImageStartHash, kHashLen), 0);
}

TEST(ESP32FirmwareCheck, RejectsImageWithoutHash) {
    uint8_t hash[kHashLen];
    Image image;
    EXPECT_FALSE(ESP32FirmwareCheck::GetImageHash(nullptr, kImageLen, hash));
    EXPECT_FALSE(ESP32FirmwareCheck::GetImageHash(image.bytes, kImageLen - 1, hash));
    EXPECT_FALSE(ESP32FirmwareCheck::GetImageHash(image.bytes, 0, hash));

    Image bad_image_magic;
    bad_image_magic.bytes[0] = 0xFF;  // Erased flash.
    EXPECT_FALSE(ESP32FirmwareCheck::GetImageHash(bad_image_magic.bytes, kImageLen, hash));

    Image bad_description_magic;
    bad_description_magic.bytes[32] ^= 0x01;
    EXPECT_FALSE(ESP32FirmwareCheck::GetImageHash(bad_description_magic.bytes, kImageLen, hash));

    Image blank_hash;
    memset(blank_hash.bytes + 176, 0, kHashLen);
    EXPECT_FALSE(ESP32FirmwareCheck::GetImageHash(blank_hash.bytes, kImageLen, hash));
}

TEST(ESP32FirmwareCheck, NoVersionMeansNoResponse) {
    // Stale values from a failed read must not count.
    EXPECT_EQ(ESP32FirmwareCheck::Evaluate(false, kVersion, kVersion, kImageStartHash, kImageStartHash),
              ESP32FirmwareCheck::kNoResponse);
    EXPECT_EQ(ESP32FirmwareCheck::Evaluate(false, 0, kVersion, nullptr, nullptr), ESP32FirmwareCheck::kNoResponse);
}

TEST(ESP32FirmwareCheck, OtherVersionIsAMismatchWhateverTheHash) {
    EXPECT_EQ(ESP32FirmwareCheck::Evaluate(true, kVersion - 1, kVersion, kImageStartHash, kImageStartHash),
              ESP32FirmwareCheck::kVersionMismatch);
    EXPECT_EQ(ESP32FirmwareCheck::Evaluate(true, kVersion + 1, kVersion, kImageStartHash, nullptr),
              ESP32FirmwareCheck::kVersionMismatch);
    EXPECT_EQ(ESP32FirmwareCheck::Evaluate(true, 0, kVersion, nullptr, nullptr),
              ESP32FirmwareCheck::kVersionMismatch);
}

TEST(ESP32FirmwareCheck, SameVersionSameHashIsUpToDate) {
    uint8_t esp32_hash[kHashLen];
    memcpy(esp32_hash, kImageStartHash, kHashLen);
    EXPECT_EQ(ESP32FirmwareCheck::Evaluate(true, kVersion, kVersion, kImageStartHash, esp32_hash),
              ESP32FirmwareCheck::kUpToDate);
}

TEST(ESP32FirmwareCheck, SameVersionOtherHashIsAMismatch) {
    // Every single-bit difference counts.
    for (uint16_t bit = 0; bit < kHashLen * 8; bit++) {
        uint8_t esp32_hash[kHashLen];
        memcpy(esp32_hash, kImageStartHash, kHashLen);
        esp32_hash[bit / 8] ^= 1 << (bit % 8);
        EXPECT_EQ(ESP32FirmwareCheck::Evaluate(true, kVersion, kVersion, kImageStartHash, esp32_hash),
                  ESP32FirmwareCheck::kHashMismatch);
    }
}

TEST(ESP32FirmwareCheck, SameVersionWithoutReportedHashIsNotUpToDate) {
    // Firmware of this version from before the hash was reported.
    EXPECT_EQ(ESP32FirmwareCheck::Evaluate(true, kVersion, kVersion, kImageStartHash, nullptr),
              ESP32FirmwareCheck::kHashNotReported);
}

TEST(ESP32FirmwareCheck, ImageWithoutHashFallsBackToVersion) {
    EXPECT_EQ(ESP32FirmwareCheck::Evaluate(true, kVersion, kVersion, nullptr, nullptr),
              ESP32FirmwareCheck::kUpToDate);
    EXPECT_EQ(ESP32FirmwareCheck::Evaluate(true, kVersion, kVersion, nullptr, kImageStartHash),
              ESP32FirmwareCheck::kUpToDate);
    EXPECT_EQ(ESP32FirmwareCheck::Evaluate(true, kVersion - 1, kVersion, nullptr, nullptr),
              ESP32FirmwareCheck::kVersionMismatch);
}

TEST(ESP32FirmwareCheck, OnlyUpToDateSkipsTheUpdate) {
    // The caller updates the ESP32 for every verdict except kUpToDate, which must be the zero value.
    EXPECT_EQ(ESP32FirmwareCheck::kUpToDate, 0);
    for (ESP32FirmwareCheck::Verdict verdict :
         {ESP32FirmwareCheck::kUpToDate, ESP32FirmwareCheck::kNoResponse, ESP32FirmwareCheck::kVersionMismatch,
          ESP32FirmwareCheck::kHashNotReported, ESP32FirmwareCheck::kHashMismatch}) {
        EXPECT_STRNE(ESP32FirmwareCheck::VerdictToString(verdict), "unknown");
    }
}

TEST(ESP32FirmwareCheck, UsableAsIsOnlyWithThisVersionAndUntouchedFlash) {
    EXPECT_TRUE(ESP32FirmwareCheck::UsableAsIs(ESP32FirmwareCheck::kHashNotReported, 0));
    EXPECT_TRUE(ESP32FirmwareCheck::UsableAsIs(ESP32FirmwareCheck::kHashMismatch, 0));
    // An interrupted write may have left part of an image.
    EXPECT_FALSE(ESP32FirmwareCheck::UsableAsIs(ESP32FirmwareCheck::kHashNotReported, 1));
    EXPECT_FALSE(ESP32FirmwareCheck::UsableAsIs(ESP32FirmwareCheck::kHashMismatch, 3));
    // Other firmware, or none that answers.
    EXPECT_FALSE(ESP32FirmwareCheck::UsableAsIs(ESP32FirmwareCheck::kVersionMismatch, 0));
    EXPECT_FALSE(ESP32FirmwareCheck::UsableAsIs(ESP32FirmwareCheck::kNoResponse, 0));
    EXPECT_FALSE(ESP32FirmwareCheck::UsableAsIs(ESP32FirmwareCheck::kUpToDate, 1));
}
