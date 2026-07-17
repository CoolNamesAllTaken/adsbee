#pragma once

#include <cstdint>

// Encoded pin handle for the FXL6408 GPIO expander.
// Encodes expander index (derived from I2C address) and pin number (0-7)
// into a single byte: bits [7:3] = expander index, bits [2:0] = pin number.
//
// kI2cAddressAddrLow  (0x43) → expander index 0
// kI2cAddressAddrHigh (0x44) → expander index 1
//
// Use FXL6408_PIN(expander_idx, pin) to construct a handle.
// Use FXL6408_PIN_EXPANDER(handle) and FXL6408_PIN_NUMBER(handle) to decode.

typedef uint8_t fxl6408_pin_t;

#define FXL6408_PIN(expander_idx, pin)   ((fxl6408_pin_t)(((expander_idx) << 3) | ((pin) & 0x7)))
#define FXL6408_PIN_EXPANDER(handle)     ((handle) >> 3)
#define FXL6408_PIN_NUMBER(handle)       ((handle) & 0x7)

// Convenience index constants matching the two I2C addresses.
#define FXL6408_EXPANDER_A  0  // ADDR pin low  → 0x43
#define FXL6408_EXPANDER_B  1  // ADDR pin high → 0x44
