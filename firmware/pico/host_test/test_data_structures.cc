#include "data_structures.hh"
#include "gtest/gtest.h"

template <class T>
void FillAndEmptyQueue(PFBQueue<T> &queue, uint16_t queue_max_length) {
    ASSERT_EQ(queue.Length(), 0);
    // Fill up the queue.
    for (uint16_t i = 0; i < queue_max_length; i++) {
        ASSERT_TRUE(queue.Push(i));
        ASSERT_EQ(queue.Length(), i + 1);
    }
    // Queue is full and can't take any more.
    ASSERT_FALSE(queue.Push(queue_max_length + 1));
    // Pop and push while wrapping around.
    for (uint16_t i = 0; i < queue_max_length; i++) {
        uint32_t pop_buffer = UINT32_MAX;
        ASSERT_TRUE(queue.Pop(pop_buffer));
        ASSERT_EQ(pop_buffer, i);
        ASSERT_EQ(queue.Length(), queue_max_length - 1);
        ASSERT_TRUE(queue.Push(queue_max_length + i));
        ASSERT_EQ(queue.Length(), queue_max_length);
    }
    // Pop everything.
    for (uint32_t i = 0; i < queue_max_length; i++) {
        uint32_t pop_buffer = UINT32_MAX;
        ASSERT_TRUE(queue.Pop(pop_buffer));
        ASSERT_EQ(pop_buffer, queue_max_length + i);
        ASSERT_EQ(queue.Length(), queue_max_length - i - 1);
    }
}

TEST(PFBQueue, BasicConstruction) {
    // Dynamically allocate buffer.
    uint16_t buf_len_num_elements = 5;
    PFBQueue<uint32_t> queue = PFBQueue<uint32_t>({.buf_len_num_elements = buf_len_num_elements, .buffer = nullptr});
    FillAndEmptyQueue(queue, buf_len_num_elements);

    // Statically allocate buffer.
    uint32_t buffer[buf_len_num_elements];
    PFBQueue<uint32_t> static_queue =
        PFBQueue<uint32_t>({.buf_len_num_elements = buf_len_num_elements, .buffer = buffer});
    FillAndEmptyQueue(static_queue, buf_len_num_elements);
}

TEST(PFBQueue, Peek) {
    uint16_t buf_len_num_elements = 30;
    PFBQueue<uint32_t> queue = PFBQueue<uint32_t>({.buf_len_num_elements = buf_len_num_elements, .buffer = nullptr});
    uint32_t peek_buffer;
    ASSERT_FALSE(queue.Peek(peek_buffer));

    // One push and pop to force a wraparound while testing peek.
    queue.Push(0);
    queue.Pop(peek_buffer);

    for (uint16_t i = 0; i < buf_len_num_elements; i++) {
        queue.Push(i);
        ASSERT_TRUE(queue.Peek(peek_buffer));
        ASSERT_EQ(peek_buffer, 0u);
        ASSERT_TRUE(queue.Peek(peek_buffer, i));
        ASSERT_EQ(peek_buffer, i);
    }
}

TEST(PFBQueue, Clear) {
    uint16_t buf_len_num_elements = 30;
    PFBQueue<uint32_t> queue = PFBQueue<uint32_t>({.buf_len_num_elements = buf_len_num_elements, .buffer = nullptr});

    uint16_t num_pushes_each_time = 10;
    for (uint16_t i = 0; i < buf_len_num_elements; i++) {
        ASSERT_EQ(queue.Length(), 0);
        for (uint16_t j = 0; j < num_pushes_each_time; j++) {
            queue.Push(i);
        }
        ASSERT_EQ(queue.Length(), num_pushes_each_time);
        queue.Clear();
    }
}

TEST(PFBQueue, OverwriteWhenFull) {
    uint16_t buf_len_num_elements = 4;
    PFBQueue<uint32_t> queue = PFBQueue<uint32_t>(
        {.buf_len_num_elements = buf_len_num_elements, .buffer = nullptr, .overwrite_when_full = true});

    // Load the queue with uint32_t's that have their MSB set to 0xF0.
    for (uint16_t i = 0; i < queue.MaxNumElements(); i++) {
        EXPECT_TRUE(queue.Push(0xF0000000 | i));
    }
    // Check that they loaded in ok.
    for (uint16_t i = 0; i < queue.MaxNumElements(); i++) {
        uint32_t out;
        EXPECT_TRUE(queue.Peek(out, i));
        EXPECT_EQ(out, 0xF0000000 | i);
    }
    // Queue should be full.
    EXPECT_EQ(queue.Length(), queue.MaxNumElements());
    // Overwrite all the elements of the queue with uint32_t's with their MSB set to 0x00.
    for (uint16_t i = 0; i < queue.MaxNumElements(); i++) {
        EXPECT_TRUE(queue.Push(i));
        EXPECT_EQ(queue.Length(), queue.MaxNumElements());
    }
    // Make sure all elements were overwritten.
    for (uint16_t i = 0; i < queue.MaxNumElements(); i++) {
        uint32_t out;
        EXPECT_TRUE(queue.Pop(out));
        EXPECT_EQ(out, i);
    }
}

TEST(PFBQueue, Discard) {
    uint16_t buf_len_num_elements = 4;
    PFBQueue<uint32_t> queue = PFBQueue<uint32_t>(
        {.buf_len_num_elements = buf_len_num_elements, .buffer = nullptr, .overwrite_when_full = false});

    EXPECT_EQ(queue.MaxNumElements(), buf_len_num_elements);

    // Load the queue with uint32_t's that have their MSB set to 0xF0.
    for (uint16_t i = 0; i < queue.MaxNumElements(); i++) {
        EXPECT_TRUE(queue.Push(0xF0000000 | i));
    }
    // Not allowed to discard more elements than the queue length.
    EXPECT_FALSE(queue.Discard(5));
    // Discard 0 elements and check that the queue length is unchanged.
    EXPECT_TRUE(queue.Discard(0));
    EXPECT_EQ(queue.Length(), queue.MaxNumElements());
    // Discard 3 elements and check that the queue length is 1 and the remaining element is the last one pushed.
    EXPECT_TRUE(queue.Discard(3));
    EXPECT_EQ(queue.Length(), 1);
    uint32_t out;
    EXPECT_TRUE(queue.Peek(out));
    EXPECT_EQ(out, 0xF0000000 | (queue.MaxNumElements() - 1));
    // Discard the last element and check that the queue is empty.
    EXPECT_TRUE(queue.Discard(1));
    EXPECT_EQ(queue.Length(), 0);

    // Discarding from an empty queue should return false.
    EXPECT_FALSE(queue.Discard(1));
    // Discarding 0 elements from an empty queue should return true.
    EXPECT_TRUE(queue.Discard(0));
}