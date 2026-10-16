#pragma once

#include <cstdint>

#include "comms.hh"
#include "hal.hh"
#include "macros.hh"
#include "unit_conversions.hh"

#ifdef ON_PICO
#include "hardware/adc.h"
#include "hardware/structs/timer.h"
#include "pico/stdlib.h"
#elif defined(ON_TI)
extern "C" {
#include "ti/drivers/temperature/TemperatureCC26X2.h"
}
#elif defined(ON_ESP32)
#include "driver/temperature_sensor.h"
#endif

#ifdef ON_PICO
#define CPU_MONITOR_INLINE __force_inline  // Called from RAM interrupt code, so never left in flash.
#else
#define CPU_MONITOR_INLINE inline
#endif

class CPUMonitor {
   public:
#ifdef ON_PICO
    static constexpr uint16_t kTempSensorADCChannel = 4;  // ADC channel for internal temperature sensor.
#endif

    struct CPUMonitorConfig {
#ifdef ON_ESP32
#else
        uint32_t idle_ticks_per_update_interval = 100e3;  // Loop ticks per interval during idle activity.
        uint32_t full_usage_update_frequency_hz =
            100;                             // If the loop slows down to this frequency or lower, CPU usage is 100%.
        uint32_t update_interval_ms = 1000;  // Interval at which to update CPU usage percentage.
        bool use_busy_time = false;          // Usage from work regions and interrupt time instead of Tick().
#endif
    };

    CPUMonitor(const CPUMonitorConfig &config) : config_(config) {
#ifdef ON_ESP32
#else
        full_usage_ticks_per_update_interval_ =
            config_.update_interval_ms * config_.full_usage_update_frequency_hz / kMsPerSec;
#endif
    };

    static void Init();

    /**
     * Converts idle and total time over one interval into a CPU usage percentage. Arguments are unsigned deltas of
     * free-running counters, so they stay correct across counter wraps.
     * @param[in] idle_delta Time spent in the idle task during the interval.
     * @param[in] total_delta Total time elapsed during the interval, in the same units.
     * @retval CPU usage percentage (0-100%). 0 if no time has elapsed.
     */
    static uint8_t UsagePercentFromIdleDelta(uint32_t idle_delta, uint32_t total_delta) {
        if (total_delta == 0) {
            return 0;
        }
        uint64_t idle_percent = static_cast<uint64_t>(idle_delta) * 100 / total_delta;
        return static_cast<uint8_t>(100 - (idle_percent > 100 ? 100 : idle_percent));
    }

    /**
     * Converts busy time over one interval into a CPU usage percentage.
     * @param[in] busy_delta Time spent working during the interval.
     * @param[in] total_delta Total time elapsed during the interval, in the same units.
     * @retval CPU usage percentage (0-100%). 0 if no time has elapsed.
     */
    static uint8_t UsagePercentFromBusyDelta(uint32_t busy_delta, uint32_t total_delta) {
        if (total_delta == 0) {
            return 0;
        }
        uint64_t busy_percent = static_cast<uint64_t>(busy_delta) * 100 / total_delta;
        return static_cast<uint8_t>(busy_percent > 100 ? 100 : busy_percent);
    }

#ifdef ON_ESP32
    /** Reads each core's CPU usage since the previous call, from FreeRTOS run time stats. */
    void ReadCPUUsage(uint8_t &core_0_usage_percent, uint8_t &core_1_usage_percent);
#else
    /**
     * Records an idle tick. Call once per main loop iteration.
     */
    inline void Tick() { ticks_since_last_update_++; }

    // Busy time mode: usage is (work regions + interrupt handlers) / elapsed time. Call these only on the monitored
    // core; Update() may run on the other core.

    /** Starts a work region. Nested regions count once. */
    inline void BeginWork() {
        if (work_depth_++ == 0) {
            work_start_us_ = NowUs();
            work_start_isr_us_ = isr_us_;
        }
    }

    /** Ends a work region: adds its time, minus interrupts already counted, unless discarded. */
    inline void EndWork(bool counted = true) {
        if (--work_depth_ != 0 || !counted) {
            return;
        }
        uint32_t isr_us = isr_us_ - work_start_isr_us_;
        uint32_t region_us = NowUs() - work_start_us_;
        work_us_ += region_us > isr_us ? region_us - isr_us : 0;
    }

    /** Times its own scope as a work region. Without a monitor, uses the calling core's (see TimeInterrupts()). */
    class WorkScope {
       public:
        explicit WorkScope(CPUMonitor& monitor) : monitor_(&monitor) { monitor_->BeginWork(); }
#ifdef ON_PICO
        WorkScope() : monitor_(ThisCore()) {
            if (monitor_) monitor_->BeginWork();
        }
#endif
        ~WorkScope() {
            if (monitor_) monitor_->EndWork();
        }

       private:
        CPUMonitor* monitor_;
    };

    /** Interrupt entry and exit hooks. Only the outermost of nested interrupts is timed. */
    CPU_MONITOR_INLINE void OnISREnter() {
        if (isr_depth_++ == 0) {
            isr_start_us_ = NowUs();
        }
    }
    CPU_MONITOR_INLINE void OnISRExit() {
        if (isr_depth_ == 1) {
            isr_us_ += NowUs() - isr_start_us_;
        }
        isr_depth_--;
    }

#ifdef ON_PICO
    /**
     * Times the interrupts enabled on the calling core (and its SysTick) through OnISREnter() / OnISRExit(), by
     * pointing their vector table entries at a timing wrapper, and makes this the calling core's monitor. Repeat calls
     * pick up newly enabled interrupts.
     */
    void TimeInterrupts();

    /** The calling core's monitor, nullptr before its TimeInterrupts(). */
    static CPUMonitor* ThisCore();

    /** Restores the vector table entries wrapped by TimeInterrupts(), so their handlers can be set again. */
    void StopTimingInterrupts();
#endif

    /**
     * Updates the CPU usage percentage. Self-regulates to run only at the configured CPU usage update interval.
     * Call frequently (at least once per CPU usage update interval).
     * @retval True if a new interval was computed.
     */
    bool Update();

    /**
     * Returns the CPU usage as a percentage (0-100%) over the last interval. In busy time mode, the share of time spent
     * in work regions and in interrupts. Otherwise estimated from the loop tick rate: the configured idle
     * tick count is 0%, the full usage loop frequency is 100%.
     * @retval CPU usage percentage (0-100%).
     */
    inline uint8_t GetUsagePercent() const { return cpu_usage_percent_; }
#endif

    /**
     * Reads the internal temperature sensor and returns the temperature in degrees Celsius.
     * @retval Temperature in degrees Celsius.
     */
    static int8_t ReadTemperatureDegC();

   private:
    CPUMonitorConfig config_;
    uint32_t full_usage_ticks_per_update_interval_;

    uint32_t last_update_timestamp_ms_ = 0;
    uint32_t ticks_since_last_update_ = 0;

    uint8_t cpu_usage_percent_ = 0;

#ifndef ON_ESP32
    static CPU_MONITOR_INLINE uint32_t NowUs() {
#ifdef ON_PICO
        return timer_hw->timerawl;
#else
        return static_cast<uint32_t>(get_time_since_boot_us());
#endif
    }

    // Free-running counters written by the monitored core only, so Update() takes deltas instead of resetting them.
    volatile uint32_t work_us_ = 0;
    volatile uint32_t isr_us_ = 0;
    uint32_t last_work_us_ = 0;
    uint32_t last_isr_us_ = 0;

    uint32_t work_depth_ = 0;
    uint32_t work_start_us_ = 0;
    uint32_t work_start_isr_us_ = 0;
    uint32_t isr_depth_ = 0;
    uint32_t isr_start_us_ = 0;

#ifdef ON_PICO
    uint64_t timed_exceptions_ = 0;  // Bit n: vector table entry n points at the timing wrapper for this monitor.
#endif
#endif

#ifdef ON_ESP32
    // Run time stats counters at the previous ReadCPUUsage() call.
    uint32_t last_total_run_time_ = 0;
    uint32_t last_idle_run_time_core_0_ = 0;
    uint32_t last_idle_run_time_core_1_ = 0;

    static temperature_sensor_handle_t temp_sensor_handle_;
    static bool temp_sensor_initialized_;
#endif
};