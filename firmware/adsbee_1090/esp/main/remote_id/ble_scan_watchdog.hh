#pragma once

#include <cstdint>

/**
 * Detects a Bluetooth scan that has stopped delivering advertising reports while the controller still reports it as
 * running. The ESP32-S3 Bluetooth controller built to run from flash (CONFIG_BT_CTRL_RUN_IN_FLASH_ONLY) can stop
 * scanning after seconds to minutes when it also advertises or hears nearby Remote ID transmitters; a host reset
 * (HCI Reset and a new sync) brings it back.
 *
 * A stall is a silence of kQuietAfterTrafficMs after at least kMinTrafficReports in the kTrafficWindowMs before it, or
 * any silence of kMaxQuietMs, so a scan with nothing to hear is reset only rarely.
 */
class BLEScanWatchdog {
   public:
    static constexpr uint32_t kQuietAfterTrafficMs = 5 * 1000;
    static constexpr uint32_t kTrafficWindowMs = 30 * 1000;
    static constexpr uint32_t kMinTrafficReports = 10;
    static constexpr uint32_t kMaxQuietMs = 120 * 1000;

    /**
     * Starts watching from now, e.g. after the scan (re)started.
     * @param[in] num_reports Running count of advertising reports.
     */
    void Reset(uint32_t num_reports, uint32_t now_ms) {
        last_num_reports_ = num_reports;
        last_report_ms_ = now_ms;
        num_samples_ = 0;
        next_sample_ = 0;
    }

    /**
     * Call about once a second while scanning.
     * @param[in] num_reports Running count of advertising reports.
     * @retval True if the scan has stalled; call Reset() after resetting the scan.
     */
    bool Update(uint32_t num_reports, uint32_t now_ms) {
        if (num_reports != last_num_reports_) {
            samples_[next_sample_] = {now_ms, last_num_reports_};
            last_num_reports_ = num_reports;
            last_report_ms_ = now_ms;
            next_sample_ = (next_sample_ + 1) % kNumSamples;
            if (num_samples_ < kNumSamples) num_samples_++;
            return false;
        }
        const uint32_t quiet_ms = now_ms - last_report_ms_;
        if (quiet_ms >= kMaxQuietMs) return true;
        return quiet_ms >= kQuietAfterTrafficMs && ReportsBeforeQuiet() >= kMinTrafficReports;
    }

   private:
    // One sample per second with new reports covers kTrafficWindowMs.
    static constexpr uint32_t kNumSamples = kTrafficWindowMs / 1000 + 2;

    // A second with new reports, and the report count before them.
    struct Sample {
        uint32_t timestamp_ms;
        uint32_t num_reports_before;
    };

    // Reports in the kTrafficWindowMs up to the last one.
    uint32_t ReportsBeforeQuiet() const {
        uint32_t num_reports_before_window = last_num_reports_;
        for (uint32_t i = 0; i < num_samples_; i++) {
            const Sample& sample = samples_[(next_sample_ + kNumSamples - 1 - i) % kNumSamples];
            if (last_report_ms_ - sample.timestamp_ms > kTrafficWindowMs) break;
            num_reports_before_window = sample.num_reports_before;
        }
        return last_num_reports_ - num_reports_before_window;
    }

    Sample samples_[kNumSamples] = {};
    uint32_t num_samples_ = 0;
    uint32_t next_sample_ = 0;
    uint32_t last_num_reports_ = 0;
    uint32_t last_report_ms_ = 0;
};
