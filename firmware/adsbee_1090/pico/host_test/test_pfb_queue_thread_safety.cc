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

#include <pthread.h>
#include <signal.h>

#include <atomic>
#include <chrono>
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

// Two writers need the lock: an unlocked queue supports exactly one.
TEST(PFBQueueThreadSafety, ThreadSafe_TwoProducers) {
    static constexpr uint16_t kQueueDepth = 4;
    static constexpr int kNumPacketsPerProducer = 20000;

    TornReadPacket buf[kQueueDepth];
    PFBQueue<TornReadPacket> queue({.buf_len_num_elements = kQueueDepth, .buffer = buf, .is_thread_safe = true});

    auto producer_fn = [&](uint8_t fill) {
        TornReadPacket p(fill);
        for (int i = 0; i < kNumPacketsPerProducer; ++i) {
            while (!queue.Enqueue(p)) std::this_thread::yield();
        }
    };
    std::thread producer_a(producer_fn, 0xAA);
    std::thread producer_b(producer_fn, 0xBB);

    int num_incoherent = 0;
    int num_from_a = 0;
    TornReadPacket out;
    for (int n = 0; n < 2 * kNumPacketsPerProducer;) {
        if (!queue.Dequeue(out)) {
            std::this_thread::yield();
            continue;
        }
        ++n;
        if (!out.IsCoherent()) ++num_incoherent;
        if (out.fill == 0xAA) ++num_from_a;
    }
    producer_a.join();
    producer_b.join();

    EXPECT_EQ(num_incoherent, 0);
    EXPECT_EQ(num_from_a, kNumPacketsPerProducer);
    EXPECT_TRUE(queue.IsEmpty());
}

// ── Unlocked queue, one writer and one reader ────────────────────────────────

// 192 bytes like ADSBee::Capture. Every fill word equals the sequence number, so a torn copy is visible.
struct SequencedElement {
    uint32_t sequence = 0;
    uint32_t fill[47] = {};

    void Set(uint32_t sequence_in) {
        sequence = sequence_in;
        for (uint32_t& word : fill) word = sequence_in;
    }
    bool IsCoherent() const {
        for (uint32_t word : fill) {
            if (word != sequence) return false;
        }
        return true;
    }
};

// Checks that elements arrive whole, in order and without gaps.
struct SequenceChecker {
    uint32_t num_received = 0;
    uint32_t num_torn = 0;
    uint32_t num_out_of_sequence = 0;

    void Check(const SequencedElement& element) {
        if (!element.IsCoherent()) num_torn = num_torn + 1;
        if (element.sequence != num_received) num_out_of_sequence = num_out_of_sequence + 1;
        num_received = element.sequence + 1;
    }
};

static double SecondsSince(std::chrono::steady_clock::time_point start) {
    return std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
}

// One writer thread and one reader thread, like a writer and a reader on two cores.
static void RunTwoThreads(uint16_t queue_depth, uint32_t num_elements, double timeout_s) {
    PFBQueue<SequencedElement> queue({.buf_len_num_elements = queue_depth});
    std::atomic<bool> writer_done{false};
    std::atomic<bool> length_violation{false};
    auto start = std::chrono::steady_clock::now();

    std::thread writer([&] {
        SequencedElement element;
        for (uint32_t i = 0; i < num_elements; ++i) {
            element.Set(i);
            while (!queue.Enqueue(element)) {
                if (queue.Length() > queue_depth) length_violation = true;
                if ((i & 0xFF) == 0 && SecondsSince(start) > timeout_s) break;
            }
        }
        writer_done = true;
    });

    SequenceChecker checker;
    SequencedElement element;
    while (true) {
        // Read the flag first: elements enqueued before it was set are then still found below.
        bool last_pass = writer_done;
        if (queue.Length() > queue_depth) length_violation = true;
        if (queue.Dequeue(element)) {
            checker.Check(element);
        } else if (last_pass) {
            break;
        }
    }
    writer.join();

    EXPECT_EQ(checker.num_received, num_elements);
    EXPECT_EQ(checker.num_torn, 0u);
    EXPECT_EQ(checker.num_out_of_sequence, 0u);
    EXPECT_FALSE(length_violation.load());
    EXPECT_TRUE(queue.IsEmpty());
}

TEST(PFBQueueUnlocked, TwoThreads_Depth2) { RunTwoThreads(2, 1000000, 20.0); }
TEST(PFBQueueUnlocked, TwoThreads_Depth16) { RunTwoThreads(16, 3000000, 20.0); }
TEST(PFBQueueUnlocked, TwoThreads_Depth3) { RunTwoThreads(3, 1000000, 20.0); }

// An "interrupt" is a signal handler on the loop's own thread: it preempts the loop between any two instructions and
// runs to completion, like an interrupt and the loop it interrupts on one core.
static PFBQueue<SequencedElement>* interrupt_queue = nullptr;
static volatile int interrupt_burst = 1;                // Queue operations per interrupt.
static volatile bool interrupt_in_place = false;        // Use Back() and Push() / Front() and Pop().
static volatile uint32_t interrupt_num_enqueued = 0;    // Writer interrupt.
static volatile uint32_t interrupt_num_refused = 0;     // Writer interrupt.
static volatile bool interrupt_length_violation = false;
static SequenceChecker interrupt_checker;               // Reader interrupt.

static void EnqueueInterrupt(int) {
    SequencedElement element;
    for (int i = 0; i < interrupt_burst; i++) {
        bool enqueued;
        if (interrupt_in_place) {
            SequencedElement* slot = interrupt_queue->Back();
            enqueued = slot != nullptr;
            if (enqueued) {
                slot->Set(interrupt_num_enqueued);
                interrupt_queue->Push();
            }
        } else {
            element.Set(interrupt_num_enqueued);
            enqueued = interrupt_queue->Enqueue(element);
        }
        if (enqueued) {
            interrupt_num_enqueued = interrupt_num_enqueued + 1;
        } else {
            interrupt_num_refused = interrupt_num_refused + 1;
        }
    }
    if (interrupt_queue->Length() > interrupt_queue->MaxNumElements()) interrupt_length_violation = true;
}

static void DequeueInterrupt(int) {
    SequencedElement element;
    for (int i = 0; i < interrupt_burst; i++) {
        if (interrupt_queue->Dequeue(element)) interrupt_checker.Check(element);
    }
    if (interrupt_queue->Length() > interrupt_queue->MaxNumElements()) interrupt_length_violation = true;
}

// Fires the handler on the calling thread as fast as possible until destroyed.
class InterruptSource {
   public:
    InterruptSource(void (*handler)(int)) {
        struct sigaction action = {};
        action.sa_handler = handler;
        sigemptyset(&action.sa_mask);
        sigaction(SIGUSR1, &action, &old_action_);
        pthread_t target = pthread_self();
        kicker_ = std::thread([this, target] {
            while (!stop_) pthread_kill(target, SIGUSR1);
        });
    }
    ~InterruptSource() { Stop(); }
    void Stop() {
        if (!kicker_.joinable()) return;
        stop_ = true;
        kicker_.join();
        // Take a signal that is still pending before the old action (terminate) comes back.
        sigset_t signals;
        sigemptyset(&signals);
        sigaddset(&signals, SIGUSR1);
        pthread_sigmask(SIG_BLOCK, &signals, nullptr);
        sigset_t pending;
        sigpending(&pending);
        if (sigismember(&pending, SIGUSR1)) {
            int signal_number;
            sigwait(&signals, &signal_number);
        }
        sigaction(SIGUSR1, &old_action_, nullptr);
        pthread_sigmask(SIG_UNBLOCK, &signals, nullptr);
    }

   private:
    struct sigaction old_action_ = {};
    std::atomic<bool> stop_{false};
    std::thread kicker_;
};

// The interrupt writes, the loop reads: ADSBee::FinishCapture() and ADSBee::DemodulateCaptures().
static void RunInterruptWriter(uint16_t queue_depth, int burst, double duration_s, bool in_place = false) {
    PFBQueue<SequencedElement> queue({.buf_len_num_elements = queue_depth});
    interrupt_queue = &queue;
    interrupt_burst = burst;
    interrupt_in_place = in_place;
    interrupt_num_enqueued = 0;
    interrupt_num_refused = 0;
    interrupt_length_violation = false;

    SequenceChecker checker;
    SequencedElement element;
    bool length_violation = false;
    auto start = std::chrono::steady_clock::now();
    InterruptSource interrupt_source(EnqueueInterrupt);
    while (SecondsSince(start) < duration_s) {
        for (int i = 0; i < 1000; i++) {
            if (in_place) {
                if (const SequencedElement* front = queue.Front()) {
                    checker.Check(*front);
                    queue.Pop();
                }
            } else if (queue.Dequeue(element)) {
                checker.Check(element);
            }
            if (queue.Length() > queue_depth) length_violation = true;
        }
    }
    interrupt_source.Stop();
    while (queue.Dequeue(element)) checker.Check(element);

    EXPECT_GT(checker.num_received, 0u);
    EXPECT_EQ(checker.num_received, interrupt_num_enqueued);
    EXPECT_EQ(checker.num_torn, 0u);
    EXPECT_EQ(checker.num_out_of_sequence, 0u);
    EXPECT_FALSE(length_violation);
    EXPECT_FALSE(interrupt_length_violation);
    interrupt_queue = nullptr;
}

// The loop writes, the interrupt reads.
static void RunInterruptReader(uint16_t queue_depth, int burst, double duration_s) {
    PFBQueue<SequencedElement> queue({.buf_len_num_elements = queue_depth});
    interrupt_queue = &queue;
    interrupt_burst = burst;
    interrupt_checker = SequenceChecker();
    interrupt_length_violation = false;

    SequencedElement element;
    uint32_t num_enqueued = 0;
    bool length_violation = false;
    auto start = std::chrono::steady_clock::now();
    InterruptSource interrupt_source(DequeueInterrupt);
    while (SecondsSince(start) < duration_s) {
        for (int i = 0; i < 1000; i++) {
            element.Set(num_enqueued);
            if (queue.Enqueue(element)) num_enqueued++;
            if (queue.Length() > queue_depth) length_violation = true;
        }
    }
    interrupt_source.Stop();
    while (queue.Dequeue(element)) interrupt_checker.Check(element);

    EXPECT_GT(num_enqueued, 0u);
    EXPECT_EQ(interrupt_checker.num_received, num_enqueued);
    EXPECT_EQ(interrupt_checker.num_torn, 0u);
    EXPECT_EQ(interrupt_checker.num_out_of_sequence, 0u);
    EXPECT_FALSE(length_violation);
    EXPECT_FALSE(interrupt_length_violation);
    interrupt_queue = nullptr;
}

TEST(PFBQueueUnlocked, InterruptWriter_Depth2) { RunInterruptWriter(2, 1, 1.0); }
// Two elements per interrupt fill a queue of two while the loop is in the middle of a Dequeue().
TEST(PFBQueueUnlocked, InterruptWriter_Depth2_Burst2) { RunInterruptWriter(2, 2, 2.0); }
TEST(PFBQueueUnlocked, InterruptWriter_Depth16_Burst2) { RunInterruptWriter(16, 2, 1.0); }
TEST(PFBQueueUnlocked, InterruptWriter_InPlace_Depth2_Burst2) { RunInterruptWriter(2, 2, 1.0, true); }
TEST(PFBQueueUnlocked, InterruptWriter_InPlace_Depth16_Burst2) { RunInterruptWriter(16, 2, 1.0, true); }
TEST(PFBQueueUnlocked, InterruptReader_Depth2) { RunInterruptReader(2, 1, 1.0); }
TEST(PFBQueueUnlocked, InterruptReader_Depth2_Burst2) { RunInterruptReader(2, 2, 2.0); }
TEST(PFBQueueUnlocked, InterruptReader_Depth16_Burst2) { RunInterruptReader(16, 2, 1.0); }
