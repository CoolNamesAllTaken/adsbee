// Thread safety verification tests for PFBQueue.
//
// The host-test environment does not have pico/mutex.h, so pfb_mutex.hh falls
// back to a no-op stub. To exercise REAL mutual exclusion we inject std::mutex
// via PFB_MUTEX_CUSTOM — this define must appear before the first inclusion of
// data_structures.hh so pfb_mutex.hh's built-in paths are both skipped.
#define PFB_MUTEX_CUSTOM
#include <mutex>
#define PFB_MUTEX_TYPE       std::mutex
#define PFB_MUTEX_INIT(mtx)  ((void)0)    // std::mutex default-constructs; no explicit init call needed.
#define PFB_MUTEX_LOCK(mtx)  (mtx).lock()
#define PFB_MUTEX_UNLOCK(mtx) (mtx).unlock()

#include <atomic>
#include <thread>

#include "data_structures.hh"
#include "gtest/gtest.h"

// A packet-sized struct where every data byte must equal the first byte (fill).
// If a concurrent write tears the 568-byte copy, some bytes will hold the new
// writer's fill and some the old one — IsCoherent() catches that.
// 568 bytes matches sizeof(RawUATUplinkPacket).
struct alignas(4) TornReadPacket {
    static constexpr size_t kLen = 568;
    uint8_t fill;
    uint8_t data[kLen - 1];

    TornReadPacket() : fill(0) { memset(data, 0, sizeof(data)); }
    explicit TornReadPacket(uint8_t v) : fill(v) { memset(data, v, sizeof(data)); }

    bool IsCoherent() const {
        for (size_t i = 0; i < sizeof(data); i++) {
            if (data[i] != fill) return false;
        }
        return true;
    }
};

// ── Thread-safe positive tests ────────────────────────────────────────────────

// Producer enqueues kNumPackets elements while a consumer concurrently dequeues
// them. With is_thread_safe=true every element must survive transfer intact and
// the total counts must balance.
TEST(PFBQueueThreadSafety, ThreadSafe_ProducerConsumerCoherence) {
    static constexpr uint16_t kQueueDepth = 2;
    static constexpr int kNumPackets = 2000;

    TornReadPacket buf[kQueueDepth];
    PFBQueue<TornReadPacket> queue(
        {.buf_len_num_elements = kQueueDepth, .buffer = buf, .is_thread_safe = true});

    std::atomic<int> produced{0};
    std::atomic<int> consumed{0};
    std::atomic<bool> corruption{false};

    std::thread producer([&] {
        for (int i = 0; i < kNumPackets; ++i) {
            TornReadPacket p(static_cast<uint8_t>(i & 0xFF));
            while (!queue.Enqueue(p)) std::this_thread::yield();
            produced.fetch_add(1, std::memory_order_relaxed);
        }
    });

    std::thread consumer([&] {
        TornReadPacket out;
        int n = 0;
        while (n < kNumPackets) {
            if (queue.Dequeue(out)) {
                if (!out.IsCoherent()) corruption.store(true, std::memory_order_relaxed);
                consumed.fetch_add(1, std::memory_order_relaxed);
                ++n;
            } else {
                std::this_thread::yield();
            }
        }
    });

    producer.join();
    consumer.join();

    EXPECT_EQ(produced.load(), kNumPackets);
    EXPECT_EQ(consumed.load(), kNumPackets);
    EXPECT_FALSE(corruption.load()) << "Thread-safe queue produced a torn read — mutex not working!";
}

// Length() must always report a value in [0, capacity] regardless of concurrent
// producer/consumer activity.
TEST(PFBQueueThreadSafety, ThreadSafe_LengthNeverExceedsCapacity) {
    static constexpr uint16_t kQueueDepth = 2;
    static constexpr int kIterations = 10000;

    TornReadPacket buf[kQueueDepth];
    PFBQueue<TornReadPacket> queue(
        {.buf_len_num_elements = kQueueDepth, .buffer = buf, .is_thread_safe = true});

    std::atomic<bool> length_violation{false};
    std::atomic<bool> producer_done{false};

    std::thread producer([&] {
        TornReadPacket p(0xAB);
        for (int i = 0; i < kIterations; ++i) queue.Enqueue(p);
        producer_done.store(true, std::memory_order_release);
    });

    std::thread consumer([&] {
        TornReadPacket out;
        while (!producer_done.load(std::memory_order_acquire) || !queue.IsEmpty()) {
            if (queue.Length() > kQueueDepth) length_violation.store(true, std::memory_order_relaxed);
            queue.Dequeue(out);
        }
    });

    producer.join();
    consumer.join();

    EXPECT_FALSE(length_violation.load());
    EXPECT_TRUE(queue.IsEmpty());
}

// ── Thread-unsafe race demonstration ─────────────────────────────────────────
//
// This test deliberately violates the single-producer assumption by running TWO
// concurrent producers against the same queue without a mutex. It verifies that
// data corruption (torn writes) can occur when is_thread_safe=false, which is
// the condition present in the production firmware.
//
// ── Plausible ESP32 panic sequence ───────────────────────────────────────────
//
// raw_uat_uplink_packet_in_queue (capacity 2, element 568 B) is written by Core
// 1 (SPI receive task, priority 10) and read by Core 0 (main task) via
// PackRawPacketsBuffer, with is_thread_safe=false.
//
// Race window (Core 0 = consumer, Core 1 = producer):
//
//   State: head=0, tail=1, is_full=false  (1 element at slot 0)
//
//   Core 0 — Dequeue:
//     1. Reads head(0)≠tail(1) → not empty → proceeds.
//     2. Begins 568-byte memcpy FROM buffer[0].          ← multi-cycle, NOT atomic
//
//   Core 1 — Enqueue (fires concurrently during step 2):
//     3. Reads is_full=false → proceeds.
//     4. Begins 568-byte memcpy TO buffer[1].            ← different slot, no conflict
//     5. Sets tail=0; tail(0)==head(0) → sets is_full=true.
//
//   Core 0 resumes:
//     6. Finishes memcpy from buffer[0].
//     7. Sets head=1.
//     8. Sets is_full=false.                              ← stomps Core 1's true
//
//   State: head=1, tail=0, is_full=false → 1 valid element (buffer[1]). Correct.
//
// The is_full stomp here is benign in isolation, but under sustained UAT uplink
// load — where the 2-slot queue is near-full on every SPI interrupt — the race
// fires continuously and produces two compounding failure modes:
//
//   A. Spurious is_full=true (reverse stomp):
//      Core 1 sets is_full=true after Core 0 has already cleared it, making a
//      queue with 1 real element appear full. PackRawPacketsBuffer's Dequeue
//      loop exits after only 1 call, leaving one element unprocessed each pass.
//      at_least_one_queue_half_full then fires every Update() iteration, causing
//      PackRawPacketsBuffer to be called far more frequently than the 200 ms
//      nominal interval.
//
//   B. Cascade to heap exhaustion → panic:
//      Each PackRawPacketsBuffer call drains up to 2 uplink packets. For each,
//      ReportGDL90UplinkDataMessage encodes a 600-byte GDL90 message and calls
//      WiFiAccessPointSendMessageToAllStations, which blocks up to 100 ms
//      waiting on the 8-slot WiFi AP queue. If the queue fills, xQueueReset
//      drops all pending frames and the UDP send path (lwip pbuf_alloc) draws
//      DMA heap. When heap drops below 20 KB, safe_send in the WAN task polls
//      every 50 ms for up to 5 000 ms. Blocking Core 0 for 5 s without yielding
//      to the idle task triggers the Task Watchdog Timer → panic + restart.
//
//      Alternative: pbuf_alloc returns NULL; ESP-IDF LwIP calls
//      LWIP_ASSERT("pbuf allocation failed", false) → abort() → panic.
//
// Fix: add .is_thread_safe = true to the three packet queues in adsbee_server.hh.
//      One FreeRTOS mutex lock/unlock per Dequeue call adds negligible overhead
//      relative to the 568-byte memcpy that immediately follows.
// ─────────────────────────────────────────────────────────────────────────────
TEST(PFBQueueThreadSafety, DISABLED_ThreadUnsafe_ConcurrentProducersCorruptData) {
    static constexpr uint16_t kQueueDepth = 4;
    static constexpr int kIterationsPerProducer = 50000;
    static constexpr uint8_t kFillA = 0xAA;
    static constexpr uint8_t kFillB = 0xBB;

    TornReadPacket buf[kQueueDepth];
    // is_thread_safe intentionally false — we want to expose the race.
    PFBQueue<TornReadPacket> queue(
        {.buf_len_num_elements = kQueueDepth, .buffer = buf, .is_thread_safe = false});

    std::atomic<bool> corruption_seen{false};
    std::atomic<bool> stop{false};

    // Two producers write distinguishable fill patterns into the same queue
    // without synchronization. Their concurrent memcpy calls to buffer[tail_]
    // will interleave when the compiler and/or CPU reorder stores, producing
    // elements whose bytes are a mix of kFillA and kFillB.
    auto producer_fn = [&](uint8_t fill) {
        TornReadPacket p(fill);
        for (int i = 0; i < kIterationsPerProducer; ++i) {
            if (stop.load(std::memory_order_relaxed)) break;
            queue.Enqueue(p);
        }
    };

    std::thread prod_a(producer_fn, kFillA);
    std::thread prod_b(producer_fn, kFillB);

    std::thread consumer([&] {
        TornReadPacket out;
        const int kMaxDequeues = kIterationsPerProducer * 2;
        for (int i = 0; i < kMaxDequeues; ++i) {
            if (queue.Dequeue(out)) {
                if (!out.IsCoherent()) {
                    corruption_seen.store(true, std::memory_order_relaxed);
                    stop.store(true, std::memory_order_relaxed);
                    return;
                }
            } else {
                std::this_thread::yield();
            }
        }
    });

    prod_a.join();
    prod_b.join();
    consumer.join();

    // On a preemptively scheduled multi-core host, torn writes appear within
    // a few thousand iterations. If no corruption is detected in a single run
    // the race simply didn't manifest that time — re-run or increase
    // kIterationsPerProducer. The test is EXPECTED to succeed (corruption_seen
    // == true); a failure here means the data race did not fire this execution.
    EXPECT_TRUE(corruption_seen.load())
        << "No torn write detected — race did not manifest this run. "
        << "Increase kIterationsPerProducer or re-run.";
}
