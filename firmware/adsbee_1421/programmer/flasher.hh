#pragma once

#include "cc13x4_bootloader.hh"

enum class FlashResult { kOk, kEraseFailed, kProgramFailed, kVerifyFailed };

// Both assume the ROM bootloader is entered and baud-synced.
bool BakedImageMatches(Cc13x4Bootloader& bl);       // Bootloader CRC32 vs. baked per-segment CRCs.
FlashResult FlashBakedImage(Cc13x4Bootloader& bl);  // Erase + program + CRC verify.
