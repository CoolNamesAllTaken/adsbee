#pragma once

#include "mode_s_packet.hh"
#include "stdint.h"

static const uint16_t kRaw1090FrameMaxNumChars = 100;

uint16_t BuildRaw1090Frame(const RawModeSPacket& packet, char* raw_frame_buf);