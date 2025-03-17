#pragma once

#include "stdint.h"
#include "transponder_packet.hh"

static const uint16_t kRaw1090FrameMaxNumChars = 100;

uint16_t BuildRaw1090Frame(const Raw1090Packet& packet, char* raw_frame_buf);