#pragma once

#include <cstdint>

#include "hal.hh"
#include "macros.hh"
#include "unit_conversions.hh"

#ifdef ON_PICO
#include "hardware/adc.h"
#include "pico/stdlib.h"
#elif ON_TI
extern "C" {
#include "ti/drivers/temperature/TemperatureCC26X2.h"
}
#endif

class CPUMonitor {
   public:
#ifdef ON_PICO
    static constexpr uint16_t kTempSensorADCChannel = 4;  // ADC channel for internal temperature sensor.
#endif

    struct CPUMonitorConfig {
        uint32_t idle_ticks_per_update_interval = 100e3;  // Loop ticks per interval during idle activity.
        uint32_t full_usage_update_frequency_hz =
            100;                             // If the loop slows down to this frequency or lower, CPU usage is 100%.
        uint32_t update_interval_ms = 1000;  // Interval at which to update CPU usage percentage.
    };

    CPUMonitor(const CPUMonitorConfig& config) : config_(config) {
        full_usage_ticks_per_update_interval_ =
            config_.update_interval_ms * config_.full_usage_update_frequency_hz / kMsPerSec;
    };

#ifdef ON_TI
    static void Init() { Temperature_init(); }
#endif

    /**
     * Records an idle tick. Call once per main loop iteration.
     */
    inline void Tick() { ticks_since_last_update_++; }

    /**
     * Updates the CPU usage percentage. Self-regulates to run only at the configured CPU usage update interval. Call
     * frequently (at least once per CPU usage update interval).
     */
    inline void Update() {
        uint32_t current_timestamp_ms = get_time_since_boot_ms();

        // Use local copies of last_update_timestamp_ms_ and ticks_since_last_update_ to avoid issues if
        // Update() is called from a different core than the core calling Tick().
        uint32_t delta_time_ms = current_timestamp_ms - last_update_timestamp_ms_;
        uint32_t ticks_since_last_update = ticks_since_last_update_;

        if (delta_time_ms < config_.update_interval_ms) {
            return;  // Not enough time has passed since the last update.
        }

        // Number of ticks that would correspond to 100% CPU usage.
        uint32_t idle_expected_ticks =
            MAX(delta_time_ms * config_.idle_ticks_per_update_interval / config_.update_interval_ms,
                1);  // No division by zero.
        uint32_t full_usage_expected_ticks =
            MAX(delta_time_ms * full_usage_ticks_per_update_interval_ / config_.update_interval_ms,
                1);  // No division by zero.
        cpu_usage_percent_ =
            100 - MIN((ticks_since_last_update - full_usage_expected_ticks) * 100 / idle_expected_ticks, 100);
        // cpu_usage_percent_ = 100 - MIN(ticks_since_last_update * 100 / idle_expected_ticks, 100);  // Avoid
        // underflow.

        // Reset the counters.
        ticks_since_last_update_ = 0;
        last_update_timestamp_ms_ = current_timestamp_ms;
    }

    /**
     * Returns the CPU usage as a percentage (0-100%). CPU usage is based on the number of idle ticks recorded vs the
     * configured maximum number of idle ticks that could be recorded if the core was doing nothing interesting other
     * than running the main loop. The maximum number of idle ticks is used to represent "0%" utilization. A
     * configurable value for the minimum permisible loop frequency is used to calculate the number of ticks that
     * represents "100%" utilization. Utilization is calculated by finding the proportion of excess idle ticks (over
     * 100% utilization tick count) recorded by the CPU.
     * @retval CPU usage percentage (0-100%).
     */
    inline uint8_t GetUsagePercent() const { return cpu_usage_percent_; }

    inline uint16_t ReadTemperatureMilliC() {
#ifdef ON_PICO
        adc_select_input(kTempSensorADCChannel);  // Internal temperature sensor.
        uint16_t raw = adc_read();
        uint16_t temp_adc_mv = adc_read() * 3300 / (0xFFF);  // Convert 12-bit ADC reading to mV assuming VREF=3.3V.
        // Convert the ADC reading to degrees C using the formula from the RP2040 datasheet.
        // See: https://datasheets.raspberrypi.com/rp2040/rp2040-datasheet.pdf Section 4.9.5
        return 27000 - (temp_adc_mv - 706) * 581;
#elif defined(ON_TI)
        // NOTE: Temperature_init() must be called before using this function.
        return Temperature_getTemperature() * 1000;  // Convert degrees C to milliC.
#else
        return 0;
#endif
    }

   private:
    CPUMonitorConfig config_;
    uint32_t full_usage_ticks_per_update_interval_;

    uint32_t last_update_timestamp_ms_ = 0;
    uint32_t ticks_since_last_update_ = 0;

    uint8_t cpu_usage_percent_ = 0;
};