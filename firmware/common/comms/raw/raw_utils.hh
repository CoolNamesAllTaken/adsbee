#pragma once

#include "stdint.h"
#include "transponder_packet.hh"

static const uint16_t kRawFrameMaxNumChars = 100;

uint16_t BuildRawFrame(const Raw1090Packet& packet, char* raw_frame_buf);