#include "gtest/gtest.h"
#include "idle_session_tracker.hh"

static constexpr uint32_t kTimeoutMs = 5000;

TEST(IdleSessionTracker, NothingIdleWhileEmptyOrFresh) {
    IdleSessionTracker<4> tracker;
    EXPECT_EQ(tracker.NextIdle(100000, kTimeoutMs), -1);
    EXPECT_TRUE(tracker.Open(60, 1000));
    EXPECT_EQ(tracker.NextIdle(1000, kTimeoutMs), -1);
    EXPECT_EQ(tracker.NextIdle(1000 + kTimeoutMs - 1, kTimeoutMs), -1);
    EXPECT_EQ(tracker.NextIdle(1000 + kTimeoutMs, kTimeoutMs), 60);
}

TEST(IdleSessionTracker, LongestIdleFirst) {
    IdleSessionTracker<4> tracker;
    tracker.Open(60, 3000);
    tracker.Open(61, 1000);
    tracker.Open(62, 2000);
    EXPECT_EQ(tracker.NextIdle(10000, kTimeoutMs), 61);
    tracker.Close(61);
    EXPECT_EQ(tracker.NextIdle(10000, kTimeoutMs), 62);
    tracker.Close(62);
    EXPECT_EQ(tracker.NextIdle(10000, kTimeoutMs), 60);
    tracker.Close(60);
    EXPECT_EQ(tracker.NextIdle(10000, kTimeoutMs), -1);
    EXPECT_EQ(tracker.NumSessions(), 0);
}

TEST(IdleSessionTracker, TouchRestartsTheTimeout) {
    IdleSessionTracker<4> tracker;
    tracker.Open(60, 0);
    tracker.Touch(60, 4000);
    EXPECT_EQ(tracker.NextIdle(8999, kTimeoutMs), -1);
    EXPECT_EQ(tracker.NextIdle(9000, kTimeoutMs), 60);
    tracker.Touch(99, 9000);  // Unknown sessions are ignored.
    tracker.Close(99);
    EXPECT_EQ(tracker.NumSessions(), 1);
}

TEST(IdleSessionTracker, FullTableRefusesNewSessionsAndReusesClosedSlots) {
    IdleSessionTracker<2> tracker;
    EXPECT_TRUE(tracker.Open(60, 0));
    EXPECT_TRUE(tracker.Open(61, 0));
    EXPECT_FALSE(tracker.Open(62, 0));
    EXPECT_FALSE(tracker.Open(-1, 0));
    tracker.Close(60);
    EXPECT_TRUE(tracker.Open(62, 0));
    EXPECT_EQ(tracker.NumSessions(), 2);
}

TEST(IdleSessionTracker, ReopenedFileDescriptorStartsFresh) {
    // A socket number is reused as soon as its session closes, possibly before Close() is called for it.
    IdleSessionTracker<2> tracker;
    tracker.Open(60, 0);
    EXPECT_TRUE(tracker.Open(60, 9000));
    EXPECT_EQ(tracker.NumSessions(), 1);
    EXPECT_EQ(tracker.NextIdle(10000, kTimeoutMs), -1);
}

TEST(IdleSessionTracker, TimestampWrap) {
    IdleSessionTracker<2> tracker;
    tracker.Open(60, UINT32_MAX - 999);
    EXPECT_EQ(tracker.NextIdle(3999, kTimeoutMs), -1);
    EXPECT_EQ(tracker.NextIdle(4000, kTimeoutMs), 60);
}

TEST(IdleSessionTracker, ExemptSessionsAreNeverReturned) {
    IdleSessionTracker<8> tracker;
    for (int fd = 50; fd < 58; fd++) tracker.Open(fd, fd - 50);  // 50 is the longest unused.
    auto is_websocket = [](int fd) { return fd % 2 == 0; };

    // The server's sweep: ask for a few idle sessions to be closed and restart their timeout. A session leaves the
    // tracker when its close arrives.
    int num_asked = 0;
    for (int i = 0; i < 3; i++) {
        int fd = tracker.NextIdle(10000, kTimeoutMs, is_websocket);
        EXPECT_EQ(fd, 51 + 2 * num_asked);  // Longest unused first, WebSockets skipped.
        tracker.Touch(fd, 10000);
        num_asked++;
    }
    tracker.Close(51);
    tracker.Close(53);  // The close of 55 got lost.
    EXPECT_EQ(tracker.NextIdle(10000, kTimeoutMs, is_websocket), 57);
    tracker.Close(57);
    EXPECT_EQ(tracker.NextIdle(10000, kTimeoutMs, is_websocket), -1);
    EXPECT_EQ(tracker.NextIdle(10000 + kTimeoutMs, kTimeoutMs, is_websocket), 55);  // Asked again one timeout later.
    EXPECT_EQ(tracker.NumSessions(), 5);
    EXPECT_EQ(tracker.NextIdle(10000, 0, [](int) { return true; }), -1);
}

TEST(IdleSessionTracker, MakingRoomTakesTheLongestUnusedSessionAtOnce) {
    // The server closes a session for the next client when the last one is taken: no timeout, the new session and
    // WebSockets exempt.
    IdleSessionTracker<4> tracker;
    tracker.Open(50, 1000);  // WebSocket.
    tracker.Open(51, 2000);
    tracker.Open(52, 3000);
    tracker.Open(53, 3000);  // New session.
    auto is_exempt = [](int fd) { return fd == 50 || fd == 53; };
    EXPECT_EQ(tracker.NextIdle(3000, 0, is_exempt), 51);
    tracker.Close(51);
    EXPECT_EQ(tracker.NextIdle(3000, 0, is_exempt), 52);
    tracker.Close(52);
    EXPECT_EQ(tracker.NextIdle(3000, 0, is_exempt), -1);
}
