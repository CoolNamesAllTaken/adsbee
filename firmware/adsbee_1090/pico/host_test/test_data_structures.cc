#include "data_structures.hh"
#include "gtest/gtest.h"

template <class T>
void FillAndEmptyQueue(PFBQueue<T> &queue, uint16_t queue_max_length) {
    ASSERT_EQ(queue.Length(), 0);
    // Fill up the queue.
    for (uint16_t i = 0; i < queue_max_length; i++) {
        ASSERT_TRUE(queue.Enqueue(i));
        ASSERT_EQ(queue.Length(), i + 1);
    }
    // Queue is full and can't take any more.
    ASSERT_FALSE(queue.Enqueue(queue_max_length + 1));
    // Dequeue and push while wrapping around.
    for (uint16_t i = 0; i < queue_max_length; i++) {
        uint32_t pop_buffer = UINT32_MAX;
        ASSERT_TRUE(queue.Dequeue(pop_buffer));
        ASSERT_EQ(pop_buffer, i);
        ASSERT_EQ(queue.Length(), queue_max_length - 1);
        ASSERT_TRUE(queue.Enqueue(queue_max_length + i));
        ASSERT_EQ(queue.Length(), queue_max_length);
    }
    // Dequeue everything.
    for (uint32_t i = 0; i < queue_max_length; i++) {
        uint32_t pop_buffer = UINT32_MAX;
        ASSERT_TRUE(queue.Dequeue(pop_buffer));
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
    queue.Enqueue(0);
    queue.Dequeue(peek_buffer);

    for (uint16_t i = 0; i < buf_len_num_elements; i++) {
        queue.Enqueue(i);
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
            queue.Enqueue(i);
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
        EXPECT_TRUE(queue.Enqueue(0xF0000000 | i));
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
        EXPECT_TRUE(queue.Enqueue(i));
        EXPECT_EQ(queue.Length(), queue.MaxNumElements());
    }
    // Make sure all elements were overwritten.
    for (uint16_t i = 0; i < queue.MaxNumElements(); i++) {
        uint32_t out;
        EXPECT_TRUE(queue.Dequeue(out));
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
        EXPECT_TRUE(queue.Enqueue(0xF0000000 | i));
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
// Usable capacity equals buf_len_num_elements for any length, and positions wrap correctly many times over.
TEST(PFBQueue, CapacityAndWrapAllLengths) {
    for (uint16_t buf_len_num_elements : {1, 2, 3, 5, 16, 255}) {
        PFBQueue<uint32_t> queue = PFBQueue<uint32_t>({.buf_len_num_elements = buf_len_num_elements});
        EXPECT_EQ(queue.MaxNumElements(), buf_len_num_elements);
        EXPECT_TRUE(queue.IsEmpty());
        uint32_t next_in = 0;
        uint32_t next_out = 0;
        for (uint16_t round = 0; round < 10 * buf_len_num_elements + 10; round++) {
            // Fill to the brim, then take out a varying number of elements.
            while (queue.Enqueue(next_in)) next_in++;
            ASSERT_TRUE(queue.IsFull());
            ASSERT_EQ(queue.Length(), buf_len_num_elements);
            ASSERT_EQ(next_in - next_out, buf_len_num_elements);
            uint32_t out;
            ASSERT_TRUE(queue.Peek(out, buf_len_num_elements - 1));
            ASSERT_EQ(out, next_in - 1);
            ASSERT_FALSE(queue.Peek(out, buf_len_num_elements));
            for (uint16_t i = 0; i < 1 + round % buf_len_num_elements; i++) {
                ASSERT_TRUE(queue.Dequeue(out));
                ASSERT_EQ(out, next_out++);
            }
            ASSERT_FALSE(queue.IsFull());
            ASSERT_EQ(queue.Length(), next_in - next_out);
        }
        // Discard and Clear on a wrapped queue.
        while (queue.Enqueue(next_in)) next_in++;
        ASSERT_TRUE(queue.Discard(buf_len_num_elements));
        EXPECT_TRUE(queue.IsEmpty());
        while (queue.Enqueue(next_in)) next_in++;
        queue.Clear();
        EXPECT_TRUE(queue.IsEmpty());
        uint32_t out;
        EXPECT_FALSE(queue.Dequeue(out));
        EXPECT_TRUE(queue.Enqueue(7));
        EXPECT_TRUE(queue.Dequeue(out));
        EXPECT_EQ(out, 7u);
    }
}

TEST(PFBQueue, OverwriteWhenFullWraps) {
    uint16_t buf_len_num_elements = 3;
    PFBQueue<uint32_t> queue =
        PFBQueue<uint32_t>({.buf_len_num_elements = buf_len_num_elements, .overwrite_when_full = true});
    for (uint32_t i = 0; i < 100; i++) {
        EXPECT_TRUE(queue.Enqueue(i));
        EXPECT_EQ(queue.Length(), i < buf_len_num_elements ? i + 1 : buf_len_num_elements);
        uint32_t out;
        EXPECT_TRUE(queue.Peek(out));  // Oldest element that was not overwritten.
        EXPECT_EQ(out, i < buf_len_num_elements ? 0 : i - buf_len_num_elements + 1);
    }
    for (uint32_t i = 97; i < 100; i++) {
        uint32_t out;
        EXPECT_TRUE(queue.Dequeue(out));
        EXPECT_EQ(out, i);
    }
    EXPECT_TRUE(queue.IsEmpty());
}

TEST(PFBQueue, ZeroLength) {
    for (bool overwrite_when_full : {false, true}) {
        PFBQueue<uint32_t> queue =
            PFBQueue<uint32_t>({.buf_len_num_elements = 0, .overwrite_when_full = overwrite_when_full});
        uint32_t out;
        EXPECT_FALSE(queue.Enqueue(1));
        EXPECT_FALSE(queue.Dequeue(out));
        EXPECT_EQ(queue.Length(), 0);
    }
}

TEST(PFBQueue, MoveConstruction) {
    PFBQueue<uint32_t> source = PFBQueue<uint32_t>({.buf_len_num_elements = 3});
    uint32_t out;
    // Wrap the source before it is moved.
    for (uint32_t i = 0; i < 5; i++) {
        EXPECT_TRUE(source.Enqueue(i));
        if (i < 2) EXPECT_TRUE(source.Dequeue(out));
    }
    PFBQueue<uint32_t> queue(std::move(source));
    EXPECT_EQ(source.Length(), 0);
    EXPECT_FALSE(source.Enqueue(9));
    EXPECT_EQ(queue.MaxNumElements(), 3);
    EXPECT_TRUE(queue.IsFull());
    for (uint32_t i = 2; i < 5; i++) {
        EXPECT_TRUE(queue.Dequeue(out));
        EXPECT_EQ(out, i);
    }
    EXPECT_TRUE(queue.IsEmpty());
}

#include <functional>
#include <memory>

// PFBQueue must work with non-trivially-copyable element types (e.g. ObjectDictionary::SCCommandRequestWithCallback
// holds a std::function). Elements must be copied with real copy semantics, and a dequeued slot must release what it
// owned.
TEST(PFBQueue, NonTriviallyCopyableElements) {
    struct Request {
        int id = 0;
        std::function<int()> callback = nullptr;
    };
    PFBQueue<Request> queue = PFBQueue<Request>({.buf_len_num_elements = 4});
    auto tracker = std::make_shared<int>(41);  // Heap object captured by the callbacks to observe ownership.
    ASSERT_EQ(tracker.use_count(), 1);
    {
        Request request = {.id = 7, .callback = [tracker]() { return *tracker + 1; }};
        ASSERT_TRUE(queue.Enqueue(request));
        // Source goes out of scope here; the queue must hold its own copy of the callback.
    }
    EXPECT_EQ(tracker.use_count(), 2);  // Only the queued copy remains.

    Request peeked;
    ASSERT_TRUE(queue.Peek(peeked));
    EXPECT_EQ(peeked.id, 7);
    EXPECT_EQ(peeked.callback(), 42);
    peeked = Request();
    EXPECT_EQ(tracker.use_count(), 2);

    Request popped;
    ASSERT_TRUE(queue.Dequeue(popped));
    EXPECT_EQ(popped.id, 7);
    EXPECT_EQ(popped.callback(), 42);
    EXPECT_EQ(tracker.use_count(), 2);  // Dequeued copy plus the local tracker; the queue slot released its copy.
    popped = Request();
    EXPECT_EQ(tracker.use_count(), 1);
    EXPECT_TRUE(queue.IsEmpty());
}
