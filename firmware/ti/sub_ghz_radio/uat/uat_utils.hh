#pragma once

#include <stdint.h>

// Full sync words, MSb is first received bit, LSb is last received bit.
// First 12 bits are used as an "any transitions" preamble, followed by a 4 Byte sync word.
static const uint64_t kUATADSBSyncWord = 0b1110'10101100'11011101'10100100'11100010; // 0xEACDDA4E2
static const uint64_t kUATGroundUplinkSyncWord = 0b0001'01010011'00100010'01011011'00011101;
static const uint16_t kUATSyncWordLenBits = 36;