#pragma once

// Times the rising edges of LR2021 DIO5 (CC1314 DIO_13) with GPT0A: 24 bits at 48 MHz. uDMA moves every capture
// to a ring, so no interrupt runs per edge. Used for MLAT timestamps (mlat_pairing.hh).

#include <cstdint>

namespace mlat_capture {

// Powers the timer and starts capturing. Keeps the 48 MHz crystal on and blocks STANDBY until Stop().
void Start();
void Stop();
bool Running();

// False while the system clock is not the 48 MHz crystal: captures are then not usable as timestamps.
bool ClockIsCrystal();

// Timer value now. Only valid while running.
uint32_t Counter();

// DIO5 level: high while the LR2021's SyncwordValid latch is set.
bool PinHigh();

static constexpr uint16_t kRingLen = 128;

// Copies captures not yet read to out (room for kRingLen), oldest first, and returns how many. *overrun: the ring
// overflowed and captures were lost; capturing has restarted.
uint16_t Read(uint32_t* out, bool* overrun);

}  // namespace mlat_capture
