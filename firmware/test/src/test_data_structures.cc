#include "gtest/gtest.h"

#include "data_structures.hh"

template <class T>
void FillAndEmptyQueue(PFBQueue<T> &queue, uint16_t queue_max_length)
{
    ASSERT_EQ(queue.Length(), 0);
    // Fill up the queue.
    for (uint16_t i = 0; i < queue_max_length; i++)
    {
        ASSERT_TRUE(queue.Push(i));
        ASSERT_EQ(queue.Length(), i + 1);
    }
    // Queue is full and can't take any more.
    ASSERT_FALSE(queue.Push(queue_max_length + 1));
    // Pop and push while wrapping around.
    for (uint16_t i = 0; i < queue_max_length; i++)
    {
        uint32_t pop_buffer = UINT32_MAX;
        ASSERT_TRUE(queue.Pop(pop_buffer));
        ASSERT_EQ(pop_buffer, i);
        ASSERT_EQ(queue.Length(), queue_max_length - 1);
        ASSERT_TRUE(queue.Push(queue_max_length + i));
        ASSERT_EQ(queue.Length(), queue_max_length);
    }
    // Pop everything.
    for (uint16_t i = 0; i < queue_max_length; i++)
    {
        uint32_t pop_buffer = UINT32_MAX;
        ASSERT_TRUE(queue.Pop(pop_buffer));
        ASSERT_EQ(pop_buffer, queue_max_length + i);
        ASSERT_EQ(queue.Length(), queue_max_length - i - 1);
    }
}

TEST(PFBQueue, BasicConstruction)
{
    // Dynamically allocate buffer.
    uint16_t queue_max_length = 5;
    PFBQueue<uint32_t> queue = PFBQueue<uint32_t>({.max_num_elements = queue_max_length, .buffer = nullptr});
    FillAndEmptyQueue(queue, queue_max_length);

    // Statically allocate buffer.
    uint32_t buffer[queue_max_length + 1];
    PFBQueue<uint32_t> static_queue = PFBQueue<uint32_t>({.max_num_elements = queue_max_length, .buffer = buffer});
    FillAndEmptyQueue(static_queue, queue_max_length);
}

TEST(PFBQueue, Peek)
{
    uint16_t queue_max_length = 30;
    PFBQueue<uint32_t> queue = PFBQueue<uint32_t>({.max_num_elements = queue_max_length, .buffer = nullptr});
    uint32_t peek_buffer;
    ASSERT_FALSE(queue.Peek(peek_buffer));

    // One push and pop to force a wraparound while testing peek.
    queue.Push(0);
    queue.Pop(peek_buffer);

    for (uint16_t i = 0; i < queue_max_length; i++)
    {
        queue.Push(i);
        ASSERT_TRUE(queue.Peek(peek_buffer));
        ASSERT_EQ(peek_buffer, 0u);
        ASSERT_TRUE(queue.Peek(peek_buffer, i));
        ASSERT_EQ(peek_buffer, i);
    }
}