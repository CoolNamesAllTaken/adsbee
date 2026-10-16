#pragma once

// MLAT: ClearIrq(SyncwordValid) after every sync edge, sent by uDMA with no CPU in the per-packet path.
//
// The SyncwordValid edge on LR2021 DIO5 (CC1314 DIO_13) is captured twice: GPT0A stores its time (mlat_capture),
// and GPT0B, fed from the same port event, requests uDMA channel 10. Channel 10 runs a memory scatter-gather list:
// NSS low, the 6-byte ClearIrq into the SPI0 TX FIFO, then re-arm channel 11 and request it. Channel 11's list raises
// NSS, pops the 6 received bytes from the SPI0 RX FIFO and re-arms channel 10. With the latch cleared after every
// edge, the n-th edge belongs to the n-th packet (mlat_pairing.hh).
//
// Bus sharing: the chain only runs while armed. Everything else that uses the SPI (drain sweep, IRQ-paced chain,
// synchronous commands) calls Disarm() first, which masks channel 10's request and waits for a chain in progress
// to end. Arm() is called with the bus free and BUSY low; when DIO5 is already latched (an edge came while
// disarmed), it starts the chain by software request, so no clear is lost.

#include <cstdint>

namespace mlat_clear_dma {

// mlat_capture must be running. clear_cmd: the 6-byte ClearIrq frame, kept valid until Stop().
void Start(const uint8_t* clear_cmd);
void Stop();
bool Running();

// Starts the chain on the next edge. Call with the bus free and BUSY low.
void Arm();
// Masks the trigger and waits for a chain in progress to end. False: it did not end in time.
bool Disarm();
bool Armed();
// Disarmed, between two frames of another SPI user, with BUSY low: when DIO5 is latched (an edge came while
// disarmed), runs the clear now and waits for it to end. True: a clear ran (BUSY is high).
bool ClearPending();

struct Counters {
    uint32_t kicks = 0;            // Clears started by Arm() for an edge that came while disarmed.
    uint32_t pending_clears = 0;   // Clears run by ClearPending().
    uint32_t wait_timeouts = 0;    // A chain did not end in time (Disarm or ClearPending).
};
const Counters& counters();
void ResetCounters();

}  // namespace mlat_clear_dma
