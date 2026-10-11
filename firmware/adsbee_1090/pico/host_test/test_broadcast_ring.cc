#include "broadcast_ring.hh"
#include "gtest/gtest.h"

typedef BroadcastRing<4, 4, 2> TestRing;

static void PushValue(TestRing& ring, uint8_t value) {
    uint8_t message[4] = {value, value, value, value};
    ring.Push(message);
}

// Reads every unread message for a client, returning the first byte of each.
static std::vector<uint8_t> ReadAll(TestRing& ring, int client_id) {
    std::vector<uint8_t> values;
    while (const uint8_t* message = ring.Peek(client_id)) {
        values.push_back(message[0]);
        ring.Pop(client_id);
    }
    return values;
}

TEST(BroadcastRing, ClientStartsAtNextMessage) {
    TestRing ring;
    PushValue(ring, 1);
    int clients[] = {7};
    ring.SetClients(clients, 1);
    EXPECT_EQ(ring.Peek(7), nullptr);

    PushValue(ring, 2);
    PushValue(ring, 3);
    EXPECT_EQ(ReadAll(ring, 7), (std::vector<uint8_t>{2, 3}));
    EXPECT_EQ(ring.Peek(7), nullptr);
    EXPECT_EQ(ring.num_dropped, 0u);
}

TEST(BroadcastRing, UnknownClientGetsNothing) {
    TestRing ring;
    PushValue(ring, 1);
    EXPECT_EQ(ring.Peek(3), nullptr);
    ring.Pop(3);  // Must not crash.
}

TEST(BroadcastRing, PeekWithoutPopRepeatsMessage) {
    TestRing ring;
    int clients[] = {7};
    ring.SetClients(clients, 1);
    PushValue(ring, 5);
    ASSERT_NE(ring.Peek(7), nullptr);
    EXPECT_EQ(ring.Peek(7)[0], 5);
    EXPECT_EQ(ring.Peek(7)[0], 5);
}

TEST(BroadcastRing, SlowClientSkipsOldest) {
    TestRing ring;
    int clients[] = {7, 9};
    ring.SetClients(clients, 2);
    for (uint8_t value = 1; value <= 3; value++) PushValue(ring, value);
    EXPECT_EQ(ReadAll(ring, 9), (std::vector<uint8_t>{1, 2, 3}));

    // Client 7 reads nothing while 6 messages pass through a ring of 4.
    for (uint8_t value = 4; value <= 6; value++) PushValue(ring, value);
    EXPECT_EQ(ReadAll(ring, 9), (std::vector<uint8_t>{4, 5, 6}));
    EXPECT_EQ(ring.num_dropped, 0u);
    EXPECT_EQ(ReadAll(ring, 7), (std::vector<uint8_t>{3, 4, 5, 6}));
    EXPECT_EQ(ring.num_dropped, 2u);
}

TEST(BroadcastRing, SetClientsForgetsAndAdds) {
    TestRing ring;
    int clients[] = {7, 9};
    ring.SetClients(clients, 2);
    PushValue(ring, 1);

    // Client 7 leaves, client 11 takes its place and starts fresh. Client 9 keeps its position.
    int new_clients[] = {9, 11};
    ring.SetClients(new_clients, 2);
    EXPECT_EQ(ring.Peek(7), nullptr);
    EXPECT_EQ(ring.Peek(11), nullptr);
    PushValue(ring, 2);
    EXPECT_EQ(ReadAll(ring, 9), (std::vector<uint8_t>{1, 2}));
    EXPECT_EQ(ReadAll(ring, 11), (std::vector<uint8_t>{2}));
}

TEST(BroadcastRing, ExtraClientsAreIgnored) {
    TestRing ring;
    int clients[] = {1, 2, 3};
    ring.SetClients(clients, 3);
    PushValue(ring, 1);
    EXPECT_NE(ring.Peek(1), nullptr);
    EXPECT_NE(ring.Peek(2), nullptr);
    EXPECT_EQ(ring.Peek(3), nullptr);
}
