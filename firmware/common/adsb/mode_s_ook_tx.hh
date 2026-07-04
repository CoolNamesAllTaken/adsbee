#pragma once

#include <cstdint>

/**
 * Mode S "ADS-B out" waveform assembly. These helpers build the on-air On-Off-Keyed (OOK) chip
 * stream for a Mode S downlink packet so it can be loaded straight into the LR2021 TX FIFO with
 * OOK encoding = None (the LR2021's packet engine emits the payload bytes literally at the chip
 * rate, with no added preamble / sync / CRC).
 *
 * HARDWARE NOTE: on the m1421 this chip stream cannot actually be transmitted as Mode S — the
 * LR2021 OOK *transmitter* is capped at 32.768 kbps (datasheet spec BROOK) while Mode S needs
 * 1 Mbit (2 Mchip/s). The builder is still exercised by host unit tests and would feed an external
 * RF-gating path (a fast CC1314 GPIO gating the 1090 carrier) if that rework is ever done. See
 * LR2021::SendModeSChipStream for details.
 *
 * The stream is a 2 Mchip/s (0.5 us/chip) sequence:
 *   - An 8 us Mode S preamble: pulses at 0 / 1.0 / 3.5 / 4.5 us (chip indices 0, 2, 7, 9), i.e.
 *     the 16-chip pattern 1010'0001'0100'0000 = {0xA1, 0x40}. The first 10 chips (1010000101)
 *     match the LR2021 receiver's preamble detector pattern in LR2021::SetOokADSB.
 *   - PPM-encoded message bits, MSB first: each 1 us data bit becomes two chips — a '1' puts the
 *     pulse in the first half ("10"), a '0' in the second half ("01"), which is the standard Mode
 *     S pulse-position convention emitted by a real transponder.
 *
 * These are pure bit-manipulation functions with no hardware dependencies, so they are covered by
 * host unit tests.
 */

/// Mode S preamble length in OOK chips (8 us at 0.5 us/chip).
static constexpr uint16_t kModeSOokPreambleLenChips = 16;

/// Two OOK chips are emitted per Mode S message bit (PPM).
static constexpr uint16_t kModeSOokChipsPerBit = 2;

/**
 * Returns the packed chip-stream length in bytes for a Mode S message of the given bit length.
 * @param[in] msg_len_bits Message length in bits: 56 (squitter) or 112 (extended squitter).
 * @retval Number of bytes the chip stream occupies, or 0 if msg_len_bits is not 56 or 112.
 */
uint16_t ModeSOokChipStreamLenBytes(uint16_t msg_len_bits);

/**
 * Builds the OOK chip stream for a Mode S downlink packet.
 * @param[in] msg_bytes      Message bytes including the trailing 24-bit CRC/parity: 7 bytes for a
 *                           56-bit squitter, 14 bytes for a 112-bit extended squitter.
 * @param[in] msg_len_bits   Message length in bits (56 or 112).
 * @param[out] chips_out     Destination buffer for the packed chip stream, MSB first. Must hold at
 *                           least ModeSOokChipStreamLenBytes(msg_len_bits) bytes; it is zeroed
 *                           internally before pulses are set.
 * @param[in] chips_out_size Size of chips_out in bytes.
 * @retval Number of chip-stream bytes written, or 0 on error (bad length, null pointer, or buffer
 *         too small).
 */
uint16_t BuildModeSOokChipStream(const uint8_t* msg_bytes, uint16_t msg_len_bits, uint8_t* chips_out,
                                 uint16_t chips_out_size);
