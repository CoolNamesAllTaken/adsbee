#include "ble_adv_watchdog.hh"
#include "gtest/gtest.h"

// Feeds the watchdog once a second, with a completion of kEventsPerRun events every `run_s` seconds (0: none); returns
// the first stall time or 0.
static uint32_t FeedSeconds(BLEAdvWatchdog& watchdog, uint32_t& num_events, uint32_t& t_ms, uint32_t secs,
                            uint32_t run_s) {
    for (uint32_t i = 0; i < secs; i++) {
        t_ms += 1000;
        if (run_s > 0 && (t_ms / 1000) % run_s == 0) num_events += BLEAdvWatchdog::kEventsPerRun;
        if (watchdog.Update(num_events, t_ms)) return t_ms;
    }
    return 0;
}

TEST(BLEAdvWatchdog, AdvertisingSetNeverStalls) {
    BLEAdvWatchdog watchdog;
    uint32_t num_events = 0, t_ms = 0;
    watchdog.Restart(num_events, t_ms);
    EXPECT_EQ(FeedSeconds(watchdog, num_events, t_ms, 3600, 10), 0u);
}

TEST(BLEAdvWatchdog, SlowCompletionsWithinQuietTimeAreFine) {
    BLEAdvWatchdog watchdog;
    uint32_t num_events = 0, t_ms = 0;
    watchdog.Restart(num_events, t_ms);
    EXPECT_EQ(FeedSeconds(watchdog, num_events, t_ms, 600, BLEAdvWatchdog::kMaxQuietMs / 1000 - 1), 0u);
}

TEST(BLEAdvWatchdog, NoCompletionStallsAfterQuietTime) {
    BLEAdvWatchdog watchdog;
    uint32_t num_events = 0, t_ms = 0;
    watchdog.Restart(num_events, t_ms);
    EXPECT_EQ(FeedSeconds(watchdog, num_events, t_ms, 60, 10), 0u);
    const uint32_t last_event_ms = 60 * 1000;
    EXPECT_EQ(FeedSeconds(watchdog, num_events, t_ms, 60, 0), last_event_ms + BLEAdvWatchdog::kMaxQuietMs);
}

TEST(BLEAdvWatchdog, RestartGivesAFreshQuietTime) {
    BLEAdvWatchdog watchdog;
    uint32_t num_events = 0, t_ms = 0;
    watchdog.Restart(num_events, t_ms);
    EXPECT_NE(FeedSeconds(watchdog, num_events, t_ms, 60, 0), 0u);
    watchdog.Restart(num_events, t_ms);
    const uint32_t restart_ms = t_ms;
    EXPECT_EQ(FeedSeconds(watchdog, num_events, t_ms, 60, 0), restart_ms + BLEAdvWatchdog::kMaxQuietMs);
}
