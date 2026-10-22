#include "ble_scan_watchdog.hh"
#include "gtest/gtest.h"

// Feeds the watchdog once a second with reports_per_s new reports; returns the first stall time or 0.
static uint32_t FeedSeconds(BLEScanWatchdog& watchdog, uint32_t& num_reports, uint32_t& t_ms, uint32_t secs,
                    uint32_t reports_per_s) {
    for (uint32_t i = 0; i < secs; i++) {
        t_ms += 1000;
        num_reports += reports_per_s;
        if (watchdog.Update(num_reports, t_ms)) return t_ms;
    }
    return 0;
}

TEST(BLEScanWatchdog, BusyScanNeverStalls) {
    BLEScanWatchdog watchdog;
    uint32_t num_reports = 0, t_ms = 0;
    watchdog.Restart(num_reports, t_ms);
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 3600, 20), 0u);
}

TEST(BLEScanWatchdog, SilenceAfterTrafficStallsAfterQuietTime) {
    BLEScanWatchdog watchdog;
    uint32_t num_reports = 0, t_ms = 0;
    watchdog.Restart(num_reports, t_ms);
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 60, 20), 0u);
    const uint32_t last_report_ms = t_ms;
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 60, 0), last_report_ms + BLEScanWatchdog::kQuietAfterTrafficMs);
}

TEST(BLEScanWatchdog, SparseTrafficWaitsForMaxQuiet) {
    BLEScanWatchdog watchdog;
    uint32_t num_reports = 0, t_ms = 0;
    watchdog.Restart(num_reports, t_ms);
    // A few reports in the window, fewer than kMinTrafficReports: only the long timeout applies.
    for (int i = 0; i < 3; i++) {
        EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 9, 0), 0u);
        EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 1, 1), 0u);
    }
    const uint32_t last_report_ms = t_ms;
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 200, 0), last_report_ms + BLEScanWatchdog::kMaxQuietMs);
}

TEST(BLEScanWatchdog, TrafficOutsideWindowDoesNotCount) {
    BLEScanWatchdog watchdog;
    uint32_t num_reports = 0, t_ms = 0;
    watchdog.Restart(num_reports, t_ms);
    // A burst, then over a window of near silence with one report: the burst is too old to count.
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 5, 20), 0u);
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 4, 0), 0u);
    t_ms += BLEScanWatchdog::kTrafficWindowMs;
    num_reports++;
    EXPECT_FALSE(watchdog.Update(num_reports, t_ms));
    const uint32_t last_report_ms = t_ms;
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 200, 0), last_report_ms + BLEScanWatchdog::kMaxQuietMs);
}

TEST(BLEScanWatchdog, EmptyAirResetsOnlyAtMaxQuiet) {
    BLEScanWatchdog watchdog;
    uint32_t num_reports = 0, t_ms = 5000;
    watchdog.Restart(num_reports, t_ms);
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 200, 0), 5000 + BLEScanWatchdog::kMaxQuietMs);
    // After a reset, the timeout starts again.
    watchdog.Restart(num_reports, t_ms);
    const uint32_t restart_ms = t_ms;
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 200, 0), restart_ms + BLEScanWatchdog::kMaxQuietMs);
}

TEST(BLEScanWatchdog, RestartKeepsRecentTraffic) {
    BLEScanWatchdog watchdog;
    uint32_t num_reports = 0, t_ms = 0;
    watchdog.Restart(num_reports, t_ms);
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 30, 20), 0u);
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 10, 0), 30000 + BLEScanWatchdog::kQuietAfterTrafficMs);
    // The scan is reset and stalls again at once: caught after the short quiet time.
    watchdog.Restart(num_reports, t_ms);
    const uint32_t restart_ms = t_ms;
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 10, 0), restart_ms + BLEScanWatchdog::kQuietAfterTrafficMs);
    // Once that traffic is older than the window, only the long timeout applies.
    t_ms = 30000 + BLEScanWatchdog::kTrafficWindowMs + 1000;
    watchdog.Restart(num_reports, t_ms);
    const uint32_t late_restart_ms = t_ms;
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 200, 0), late_restart_ms + BLEScanWatchdog::kMaxQuietMs);
}

TEST(BLEScanWatchdog, TimestampWrap) {
    BLEScanWatchdog watchdog;
    uint32_t num_reports = 0, t_ms = UINT32_MAX - 20000;
    watchdog.Restart(num_reports, t_ms);
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 40, 20), 0u);
    const uint32_t last_report_ms = t_ms;
    EXPECT_EQ(FeedSeconds(watchdog, num_reports, t_ms, 60, 0), last_report_ms + BLEScanWatchdog::kQuietAfterTrafficMs);
}
