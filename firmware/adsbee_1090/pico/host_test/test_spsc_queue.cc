#include "../application/spsc_queue.hh"
#include "gtest/gtest.h"

TEST(SPSCQueue, EmptyQueueHasNoFront) {
    SPSCQueue<uint32_t, 4> queue;
    EXPECT_EQ(queue.Front(), nullptr);
    EXPECT_EQ(queue.Length(), 0);
}

TEST(SPSCQueue, HoldsDepthMinusOneElementsInOrder) {
    SPSCQueue<uint32_t, 4> queue;
    for (uint32_t i = 0; i < 3; i++) {
        uint32_t* slot = queue.Back();
        ASSERT_NE(slot, nullptr);
        *slot = 100 + i;
        queue.Push();
    }
    EXPECT_EQ(queue.Length(), 3);
    EXPECT_EQ(queue.Back(), nullptr);  // Full.
    for (uint32_t i = 0; i < 3; i++) {
        const uint32_t* element = queue.Front();
        ASSERT_NE(element, nullptr);
        EXPECT_EQ(*element, 100 + i);
        queue.Pop();
    }
    EXPECT_EQ(queue.Front(), nullptr);
}

TEST(SPSCQueue, UnpushedSlotIsNotVisible) {
    SPSCQueue<uint32_t, 4> queue;
    *queue.Back() = 7;
    EXPECT_EQ(queue.Front(), nullptr);
    queue.Push();
    EXPECT_EQ(*queue.Front(), 7u);
}

TEST(SPSCQueue, WrapsAround) {
    SPSCQueue<uint32_t, 4> queue;
    uint32_t next_in = 0;
    uint32_t next_out = 0;
    for (uint16_t round = 0; round < 50; round++) {
        for (uint16_t i = 0; i < 1 + round % 3; i++) {
            uint32_t* slot = queue.Back();
            if (slot == nullptr) {
                break;
            }
            *slot = next_in++;
            queue.Push();
        }
        for (uint16_t i = 0; i < 1 + round % 2; i++) {
            const uint32_t* element = queue.Front();
            if (element == nullptr) {
                break;
            }
            EXPECT_EQ(*element, next_out++);
            queue.Pop();
        }
        EXPECT_EQ(queue.Length(), next_in - next_out);
    }
    EXPECT_GT(next_out, 50u);
}
