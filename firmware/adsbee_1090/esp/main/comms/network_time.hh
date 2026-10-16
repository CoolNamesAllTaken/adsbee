#pragma once

#include <cstdint>

#include "settings.hh"

/**
 * Keeps the ESP32 clock on UTC with SNTP (Simple Network Time Protocol) while an output uses ASTERIX, so ASTERIX
 * reports carry UTC when GNSS has no time. Nothing runs while no output uses ASTERIX.
 */
class NetworkTime {
   public:
    // lwIP polls the server every CONFIG_LWIP_SNTP_UPDATE_DELAY (1 h). Time is used for up to three missed polls.
    static constexpr uint32_t kMaxSyncAgeMs = 3 * 3600 * 1000;

    struct Status {
        bool enabled = false;  // SNTP is running.
        bool synced = false;   // UTC is valid.
        uint32_t last_sync_age_s = 0;
        const char* server = "";
    };

    /**
     * Starts, stops or restarts SNTP to match the settings. Call from the main loop.
     */
    void Update();

    /**
     * UTC now, if SNTP has synced recently. Safe to call from any task.
     * @param[out] utc_ms_of_day UTC milliseconds since midnight.
     * @param[out] local_ms Milliseconds since boot at which that UTC time held.
     * @retval True if UTC is valid.
     */
    bool GetUTC(uint32_t& utc_ms_of_day, uint32_t& local_ms);

    void GetStatus(Status& status);

   private:
    static void OnSync(struct timeval* tv);
    void Start();
    void Stop();

    bool running_ = false;
    bool had_ip_ = false;
    char server_[SettingsManager::Settings::kNTPServerMaxLen + 1] = {0};  // lwIP keeps a pointer to this.
    volatile bool synced_ = false;
    volatile uint32_t last_sync_timestamp_ms_ = 0;
};

extern NetworkTime network_time;
