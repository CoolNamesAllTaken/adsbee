#pragma once
#include "bsp.hh"
#include "comms.hh"
#include "hal.hh"
#include "hardware/gpio.h"

/**
 * Enables an easy flash pattern on an LED during operations like firmware updates.
 * NOTE: The pin must be initialized before this class is used.
 */
class LEDFlasher {
   public:
    struct LEDFlasherConfig {
        uint16_t led_pin = bsp.r1090_led_pin;
    };

    LEDFlasher(LEDFlasherConfig config_in) : config_(config_in) {}

    inline void SetFlashPattern(uint32_t flash_pattern, uint8_t flash_pattern_len_bits,
                                uint16_t flash_tick_period_ms = 10) {
        if (flash_pattern_len_bits == 0 || flash_pattern_len_bits > 32) {
            CONSOLE_ERROR("LEDFlasher::SetFlashPattern", "Invalid flash pattern length %d bits.",
                          flash_pattern_len_bits);
            return;
        }
        flash_pattern_ = flash_pattern;
        flash_pattern_len_bits_ = flash_pattern_len_bits;
        flash_tick_period_ms_ = flash_tick_period_ms;
        last_flash_tick_timestamp_ms_ = get_time_since_boot_ms();
        current_flash_bit_idx_ = 0;
    }

    inline void Update() {
        if (flash_pattern_len_bits_ == 0) {
            return;  // Nothing to do.
        }
        uint32_t timestamp_ms = get_time_since_boot_ms();
        if (timestamp_ms - last_flash_tick_timestamp_ms_ > flash_tick_period_ms_) {
            last_flash_tick_timestamp_ms_ = timestamp_ms;
            // Update LED state based on current bit in pattern.
            if (flash_pattern_ & (1 << (flash_pattern_len_bits_ - 1 - current_flash_bit_idx_))) {
                // Current bit is 1, turn LED on.
                gpio_put(config_.led_pin, 1);
            } else {
                // Current bit is 0, turn LED off.
                gpio_put(config_.led_pin, 0);
            }
            current_flash_bit_idx_++;
            if (current_flash_bit_idx_ >= flash_pattern_len_bits_) {
                current_flash_bit_idx_ = 0;  // Loop back to start of pattern.
            }
        }
    }

   private:
    LEDFlasherConfig config_;
    bool enabled_ = false;
    uint32_t flash_pattern_ = 0b10101010;
    uint8_t flash_pattern_len_bits_ = 8;
    uint16_t flash_tick_period_ms_ = 10;
    uint32_t last_flash_tick_timestamp_ms_ = 0;
    uint8_t current_flash_bit_idx_ = 0;
};