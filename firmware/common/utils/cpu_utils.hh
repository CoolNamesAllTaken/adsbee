#pragma once

#include <cstdint>

#include "hal.hh"
#include "macros.hh"
#include "unit_conversions.hh"

class CPUMonitor {
   public:
    struct CPUMonitorConfig {
        uint16_t min_loop_frequency_hz = 100;  // Minimum expected loop frequency.
        uint32_t update_interval_ms = 1000;    // Interval at which to update CPU usage percentage.
    };

    CPUMonitor(const CPUMonitorConfig& config) : config_(config) {
        max_loop_interval_ms_ = kMsPerSec / MAX(config_.min_loop_frequency_hz, 1);  // No division by zero.
    }

    inline void Tick() { ticks_since_last_update_++; }
    inline void Update() {
        uint32_t current_timestamp_ms = get_time_since_boot_ms();

        // Use local copies of last_update_timeestamp_ms_ and ticks_since_last_update_ to avoid issues if
        // Update() is called from a different core than the core calling Tick().
        uint32_t delta_time_ms = current_timestamp_ms - last_update_timeestamp_ms_;
        uint32_t ticks_since_last_update = ticks_since_last_update_;

        if (delta_time_ms < config_.update_interval_ms) {
            return;  // Not enough time has passed since the last update.
        }

        // Number of ticks that would correspond to 100% CPU usage.
        uint32_t expected_ticks = MAX(delta_time_ms / max_loop_interval_ms_, 1);  // No division by zero.
        cpu_usage_percent_ = 100 - (ticks_since_last_update * 100 / expected_ticks);

        // Reset the counters.
        ticks_since_last_update_ = 0;
        last_update_timeestamp_ms_ = current_timestamp_ms;
    }

    inline uint8_t GetUsagePercent() const { return cpu_usage_percent_; }

   private:
    CPUMonitorConfig config_;
    uint32_t max_loop_interval_ms_;

    uint32_t last_update_timeestamp_ms_ = 0;
    uint32_t ticks_since_last_update_ = 0;

    uint8_t cpu_usage_percent_ = 0;
};