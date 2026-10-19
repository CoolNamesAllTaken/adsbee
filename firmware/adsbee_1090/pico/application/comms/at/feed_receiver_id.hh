#pragma once

#include <cstdint>
#include <string_view>

// Value of AT+FEED_RECEIVER_ID: 16 hex digits (8 bytes, MSB first) or DEFAULT. Case-insensitive.
namespace FeedReceiverID {

static constexpr uint16_t kNumBytes = 8;

enum Parsed { kInvalid, kHex, kDefault };

inline int HexDigit(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

// Writes the bytes to out for kHex; leaves out unchanged otherwise.
inline Parsed Parse(std::string_view arg, uint8_t out[kNumBytes]) {
    static constexpr std::string_view kDefaultStr = "DEFAULT";
    if (arg.length() == kDefaultStr.length()) {
        bool is_default = true;
        for (uint16_t i = 0; i < kDefaultStr.length(); i++) {
            char c = arg[i];
            if (c >= 'a' && c <= 'z') c -= 'a' - 'A';
            is_default &= c == kDefaultStr[i];
        }
        if (is_default) return kDefault;
    }
    if (arg.length() != 2 * kNumBytes) return kInvalid;
    uint8_t bytes[kNumBytes];
    for (uint16_t i = 0; i < kNumBytes; i++) {
        int hi = HexDigit(arg[2 * i]), lo = HexDigit(arg[2 * i + 1]);
        if (hi < 0 || lo < 0) return kInvalid;
        bytes[i] = static_cast<uint8_t>(hi << 4 | lo);
    }
    for (uint16_t i = 0; i < kNumBytes; i++) out[i] = bytes[i];
    return kHex;
}

}  // namespace FeedReceiverID
