#include <cstring>

#include "gtest/gtest.h"
#include "remote_id_guard.hh"

static constexpr uint32_t kKB = 1024;

TEST(RemoteIDGuard, AllowedTransports) {
    // With PSRAM everything runs next to any network interface.
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(true, true, true, true), RemoteIDGuard::kTransportsAll);
    // Without PSRAM: everything with no network, Bluetooth only next to Ethernet, nothing next to WiFi.
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(false, false, false, false), RemoteIDGuard::kTransportsAll);
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(false, false, false, true), RemoteIDGuard::kTransportsBLE);
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(false, true, false, false), 0);
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(false, false, true, false), 0);
    EXPECT_EQ(RemoteIDGuard::AllowedTransports(false, true, true, true), 0);
}

TEST(RemoteIDGuard, HeapBelowReserve) {
    EXPECT_FALSE(RemoteIDGuard::HeapBelowReserve(RemoteIDGuard::kReserveFreeBytes,
                                                 RemoteIDGuard::kReserveLargestBlockBytes));
    EXPECT_TRUE(RemoteIDGuard::HeapBelowReserve(RemoteIDGuard::kReserveFreeBytes - 1, 100 * kKB));
    EXPECT_TRUE(RemoteIDGuard::HeapBelowReserve(100 * kKB, RemoteIDGuard::kReserveLargestBlockBytes - 1));
}

TEST(RemoteIDGuard, HeapWatchPausesAndBacksOff) {
    RemoteIDGuard::HeapWatch watch;
    uint32_t t = 1000;
    // Healthy heap while running: no pause.
    EXPECT_FALSE(watch.Update(80 * kKB, 30 * kKB, t, true));
    // Low heap while not running: nothing to pause.
    EXPECT_FALSE(watch.Update(20 * kKB, 10 * kKB, t, false));

    // Low heap while running pauses for the hold-off, even once the heap recovers.
    EXPECT_TRUE(watch.Update(30 * kKB, 30 * kKB, t, true));
    EXPECT_EQ(watch.GetNumPauses(), 1);
    EXPECT_TRUE(watch.Update(110 * kKB, 40 * kKB, t + RemoteIDGuard::kResumeHoldOffMs - 1, false));
    EXPECT_FALSE(watch.Update(110 * kKB, 40 * kKB, t + RemoteIDGuard::kResumeHoldOffMs, false));

    // Each further pause doubles the hold-off.
    t += 10 * RemoteIDGuard::kResumeHoldOffMs;
    EXPECT_TRUE(watch.Update(80 * kKB, 8 * kKB, t, true));  // Largest block too small.
    EXPECT_EQ(watch.HoldOffMs(), 2 * RemoteIDGuard::kResumeHoldOffMs);
    EXPECT_TRUE(watch.Update(110 * kKB, 40 * kKB, t + 2 * RemoteIDGuard::kResumeHoldOffMs - 1, false));
    EXPECT_FALSE(watch.Update(110 * kKB, 40 * kKB, t + 2 * RemoteIDGuard::kResumeHoldOffMs, false));

    // The hold-off is capped.
    for (int i = 0; i < 20; i++) {
        t += RemoteIDGuard::kResumeHoldOffMaxMs;
        watch.Update(10 * kKB, 10 * kKB, t, true);
    }
    EXPECT_EQ(watch.HoldOffMs(), RemoteIDGuard::kResumeHoldOffMaxMs);
    EXPECT_FALSE(watch.Update(110 * kKB, 40 * kKB, t + RemoteIDGuard::kResumeHoldOffMaxMs, false));

    // Reset clears the back-off.
    watch.Reset();
    EXPECT_FALSE(watch.IsPaused());
    EXPECT_EQ(watch.HoldOffMs(), RemoteIDGuard::kResumeHoldOffMs);
}

TEST(RemoteIDGuard, HeapWatchHandlesClockWrap) {
    RemoteIDGuard::HeapWatch watch;
    const uint32_t t = UINT32_MAX - 1000;
    EXPECT_TRUE(watch.Update(10 * kKB, 10 * kKB, t, true));
    EXPECT_TRUE(watch.Update(110 * kKB, 40 * kKB, t + 2000, false));
    EXPECT_FALSE(watch.Update(110 * kKB, 40 * kKB, t + RemoteIDGuard::kResumeHoldOffMs, false));
}

TEST(RemoteIDGuard, BlockedReason) {
    EXPECT_EQ(RemoteIDGuard::BlockedReason(0), nullptr);
    EXPECT_EQ(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusBLEActive), nullptr);
    // Ethernet without PSRAM: WiFi beacon paused, Bluetooth running.
    EXPECT_STREQ(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusBlockedByNetwork |
                                              RemoteIDGuard::kStatusBLEActive),
                 "partly paused: this ESP32 has no PSRAM, so with Ethernet on only the Bluetooth transports run");
    EXPECT_NE(strstr(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusBlockedByNetwork), "with WiFi on"), nullptr);
    EXPECT_NE(strstr(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusPausedLowHeap), "web server"), nullptr);
    // A heap pause stops everything, so it explains more than a partial network block.
    EXPECT_NE(strstr(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusPausedLowHeap |
                                                  RemoteIDGuard::kStatusBlockedByNetwork),
                     "web server"),
              nullptr);
    EXPECT_NE(strstr(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusTxBlocked), "could not start"), nullptr);
    EXPECT_NE(strstr(RemoteIDGuard::BlockedReason(RemoteIDGuard::kStatusTxBlocked | RemoteIDGuard::kStatusBlockedByRAM),
                     "memory"),
              nullptr);
}
