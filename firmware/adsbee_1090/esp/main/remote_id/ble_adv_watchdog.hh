#pragma once

#include <cstdint>

/**
 * Detects a Bluetooth advertising set that has stopped going out. Each set is started for kEventsPerRun advertising
 * events; the controller then ends it and reports how many it sent (BLE_GAP_EVENT_ADV_COMPLETE), and it is started
 * again. Those events are the controller's own count of what it put on the air. The ESP32-S3 controller built to run
 * from flash (CONFIG_BT_CTRL_RUN_IN_FLASH_ONLY) can stop advertising while still accepting commands; a host reset
 * (HCI Reset and a new sync) brings it back.
 */
class BLEAdvWatchdog {
   public:
    // At a 500 ms advertising interval: a completion about every 10 s.
    static constexpr uint16_t kEventsPerRun = 20;
    // Three runs' time without a single advertising event sent.
    static constexpr uint32_t kMaxQuietMs = 30 * 1000;

    /**
     * Restarts the quiet time from now, e.g. after the set was (re)configured.
     * @param[in] num_events Running count of advertising events the controller reported sent.
     */
    void Restart(uint32_t num_events, uint32_t now_ms) {
        last_num_events_ = num_events;
        last_event_ms_ = now_ms;
    }

    /**
     * Call about once a second while the set should be advertising.
     * @param[in] num_events Running count of advertising events the controller reported sent.
     * @retval True if the set has stalled; call Restart() after resetting the controller.
     */
    bool Update(uint32_t num_events, uint32_t now_ms) {
        if (num_events != last_num_events_) {
            Restart(num_events, now_ms);
            return false;
        }
        return now_ms - last_event_ms_ >= kMaxQuietMs;
    }

   private:
    uint32_t last_num_events_ = 0;
    uint32_t last_event_ms_ = 0;
};
