#ifndef DATA_STRUCTURES_HH_
#define DATA_STRUCTURES_HH_

#include <stdint.h>

#include <atomic>
#include <type_traits>  // For std::is_trivially_copyable.

#include "pfb_mutex.hh"

/**
 * Fixed-size first in, first out queue. Holds up to buf_len_num_elements elements.
 *
 * Which mode to use:
 * - Unlocked (is_thread_safe = false, the default): one writer context and one reader context. Either may be an
 *   interrupt that preempts the other, or run on another core. No lock is taken, so this is the mode for interrupts.
 *   The writer calls Enqueue() or Back() and Push(); the reader calls Dequeue(), Front() and Pop(), Peek(), Discard()
 *   and Clear(). Length(), IsFull() and IsEmpty() are allowed on both sides: the reader may see fewer elements than
 *   there are, the writer more.
 * - Locked (is_thread_safe = true): any number of writers and readers in tasks or on both cores. Never call it from an
 *   interrupt: the lock would deadlock against the code it interrupted.
 * - overwrite_when_full: a full queue drops its oldest element, so the writer moves the reader's position. Use it
 *   locked, or with writer and reader in one context, or with interrupts masked around every reader call when the
 *   writer is an interrupt. Unlocked with a reader that can be preempted by the writer, it can return a torn element.
 */
template <class T>
class PFBQueue {
   public:
    struct PFBQueueConfig {
        uint16_t buf_len_num_elements = 0;
        T* buffer = nullptr;
        bool overwrite_when_full = false;  // Not interrupt safe without a lock or masked interrupts, see above.
        bool is_thread_safe = false;       // Take a lock around every call. Never for queues used in an interrupt.
    };

    /**
     * Constructor.
     * NOTE: PFBQueue can't be copied. Pass it by reference.
     * @param[in] config_in Defines length of the buffer, and points to the buffer of size buf_len_num_elements if
     * PFBQueue should work with a pre-allocated buffer (which must hold buf_len_num_elements constructed T objects).
     * If config_in.buffer is left as nullptr, an array of buf_len_num_elements default-constructed T objects will be
     * dynamically allocated.
     * Elements are stored with T's copy assignment (not memcpy), so non-trivially-copyable element types such as
     * structs holding a std::function are supported.
     * @retval PFBQueue object.
     */
    PFBQueue(PFBQueueConfig config_in) : config_(config_in), buffer_length_(config_in.buf_len_num_elements) {
        if (config_.buffer == nullptr) {
            config_.buffer = new T[buffer_length_];
            buffer_was_dynamically_allocated_ = true;
        }
        if (config_.is_thread_safe) {
            PFB_MUTEX_INIT(mutex_);
        }
    }

    /**
     * Move constructor: takes over the buffer and contents and leaves the other queue with zero length. For setup
     * code only, never while another context uses either queue.
     */
    PFBQueue(PFBQueue&& other)
        : config_(other.config_),
          buffer_was_dynamically_allocated_(other.buffer_was_dynamically_allocated_),
          buffer_length_(other.buffer_length_),
          head_(other.head_.load()),
          tail_(other.tail_.load()) {
        if (config_.is_thread_safe) {
            PFB_MUTEX_INIT(mutex_);
        }
        other.config_.buffer = nullptr;
        other.config_.buf_len_num_elements = 0;
        other.buffer_was_dynamically_allocated_ = false;
        other.buffer_length_ = 0;
        other.head_ = 0;
        other.tail_ = 0;
    }

    /**
     * Destructor. Frees the buffer buffer if it was dynamically allocated.
     */
    ~PFBQueue() {
        if (buffer_was_dynamically_allocated_ && config_.buffer != nullptr) {
            delete[] config_.buffer;
            config_.buffer = nullptr;
        }
    }

    inline bool IsFull() { return Length() == buffer_length_; }
    inline bool IsEmpty() { return Length() == 0; }

    /**
     * Enqueues an element to the back of the buffer. Writer side.
     * @param[in] element Object to push onto the back of the buffer.
     * @retval True if succeeded, false if the buffer is full.
     */
    bool Enqueue(const T& element) {
        if (config_.is_thread_safe) PFB_MUTEX_LOCK(mutex_);
        uint32_t tail = tail_.load(std::memory_order_relaxed);
        uint32_t head = head_.load(std::memory_order_acquire);
        if (Distance(head, tail) >= buffer_length_) {
            if (!config_.overwrite_when_full || buffer_length_ == 0) {
                // Buffer is full and not overwriting; cannot push.
                if (config_.is_thread_safe) PFB_MUTEX_UNLOCK(mutex_);
                return false;
            }
            head_.store(Advance(head), std::memory_order_release);  // Drop the oldest element.
        }

        config_.buffer[Slot(tail)] = element;
        tail_.store(Advance(tail), std::memory_order_release);  // Publish only after the element is written.

        if (config_.is_thread_safe) PFB_MUTEX_UNLOCK(mutex_);
        return true;
    }

    /**
     * Dequeues an element from the front of the buffer. Reader side.
     * @param[out] element Reference to an object that will be overwritten by the contents of the popped element.
     * @retval True if successful, false if the buffer is empty.
     */
    bool Dequeue(T& element) {
        if (config_.is_thread_safe) PFB_MUTEX_LOCK(mutex_);
        uint32_t head = head_.load(std::memory_order_relaxed);
        if (head == tail_.load(std::memory_order_acquire)) {
            if (config_.is_thread_safe) PFB_MUTEX_UNLOCK(mutex_);
            return false;
        }
        element = config_.buffer[Slot(head)];
        if constexpr (!std::is_trivially_copyable<T>::value) {
            // Release whatever the vacated slot owned (e.g. a std::function target) instead of holding it until the
            // slot is overwritten.
            config_.buffer[Slot(head)] = T();
        }
        head_.store(Advance(head), std::memory_order_release);  // Free the slot only after the element is read.
        if (config_.is_thread_safe) PFB_MUTEX_UNLOCK(mutex_);
        return true;
    }

    /**
     * Returns the contents of an element in the buffer without removing it from the buffer. Reader side.
     * @param[out] element Reference to an object that will be overwritten by the contents of the peeked element.
     * @param[in] index Position in the buffer to peek. Defaults to 0 (the front of the buffer).
     * @retval True if successful, false if the buffer is empty or index is out of bounds.
     */
    bool Peek(T& element, uint16_t index = 0) {
        if (config_.is_thread_safe) PFB_MUTEX_LOCK(mutex_);
        uint32_t head = head_.load(std::memory_order_relaxed);
        if (index >= Distance(head, tail_.load(std::memory_order_acquire))) {
            if (config_.is_thread_safe) PFB_MUTEX_UNLOCK(mutex_);
            return false;
        }
        element = config_.buffer[Slot(Advance(head, index))];
        if (config_.is_thread_safe) PFB_MUTEX_UNLOCK(mutex_);
        return true;
    }

    /**
     * Discards a specified number of elements from the front of the buffer. Reader side.
     * @param[in] num_elements Number of elements to discard from the front of the buffer.
     * @retval True if successful, false if there are not enough elements to discard.
     */
    inline bool Discard(uint16_t num_elements) {
        if (config_.is_thread_safe) PFB_MUTEX_LOCK(mutex_);
        uint32_t head = head_.load(std::memory_order_relaxed);
        if (num_elements > Distance(head, tail_.load(std::memory_order_acquire))) {
            if (config_.is_thread_safe) PFB_MUTEX_UNLOCK(mutex_);
            return false;  // Not enough elements to discard.
        }
        head_.store(Advance(head, num_elements), std::memory_order_release);
        if (config_.is_thread_safe) PFB_MUTEX_UNLOCK(mutex_);
        return true;
    }

    // In-place access, for unlocked queues without overwrite_when_full: the element is filled or read where it is
    // stored, which saves a copy on each side. On other queues Back() and Front() return nullptr.

    /**
     * Writer side: slot for the next element.
     * @retval Slot to fill before calling Push(), or nullptr if the queue is full.
     */
    inline T* Back() {
        if (config_.is_thread_safe || config_.overwrite_when_full) return nullptr;
        uint32_t tail = tail_.load(std::memory_order_relaxed);
        if (Distance(head_.load(std::memory_order_acquire), tail) >= buffer_length_) return nullptr;
        return &config_.buffer[Slot(tail)];
    }

    /**
     * Writer side: makes the slot returned by Back() visible to the reader.
     */
    inline void Push() { tail_.store(Advance(tail_.load(std::memory_order_relaxed)), std::memory_order_release); }

    /**
     * Reader side: oldest element.
     * @retval Element to use before calling Pop(), or nullptr if the queue is empty.
     */
    inline const T* Front() {
        if (config_.is_thread_safe || config_.overwrite_when_full) return nullptr;
        uint32_t head = head_.load(std::memory_order_relaxed);
        if (head == tail_.load(std::memory_order_acquire)) return nullptr;
        return &config_.buffer[Slot(head)];
    }

    /**
     * Reader side: removes the element returned by Front().
     */
    inline void Pop() {
        uint32_t head = head_.load(std::memory_order_relaxed);
        if constexpr (!std::is_trivially_copyable<T>::value) {
            config_.buffer[Slot(head)] = T();  // Release what the slot owned, like Dequeue().
        }
        head_.store(Advance(head), std::memory_order_release);
    }

    /**
     * Returns the number of elements currently in the buffer.
     * @retval Number of elements in the buffer.
     */
    inline uint16_t Length() {
        if (config_.is_thread_safe) PFB_MUTEX_LOCK(mutex_);
        uint32_t head = head_.load(std::memory_order_acquire);
        uint16_t len = Distance(head, tail_.load(std::memory_order_acquire));
        if (config_.is_thread_safe) PFB_MUTEX_UNLOCK(mutex_);
        return len;
    }

    /**
     * Return the maximum number of elements that can be stored in the queue.
     * @retval Number of elements that can be stored in the queue.
     */
    inline uint16_t MaxNumElements() { return config_.buf_len_num_elements; }

    /**
     * Empty out the buffer by moving the head up to the tail. Reader side.
     */
    void Clear() {
        if (config_.is_thread_safe) PFB_MUTEX_LOCK(mutex_);
        head_.store(tail_.load(std::memory_order_acquire), std::memory_order_release);
        if (config_.is_thread_safe) PFB_MUTEX_UNLOCK(mutex_);
    }

   private:
    // head_ and tail_ count elements modulo 2 * buffer_length_, so that a full queue (tail_ is buffer_length_ ahead
    // of head_) differs from an empty one (tail_ == head_) without a flag that both sides would have to write.

    /**
     * Number of elements between two positions.
     * @param[in] head Position of the oldest element.
     * @param[in] tail Position one past the newest element.
     * @retval Number of elements, 0 to buffer_length_.
     */
    inline uint16_t Distance(uint32_t head, uint32_t tail) {
        return tail >= head ? tail - head : tail + 2 * buffer_length_ - head;
    }

    /**
     * Moves a position forward.
     * @param[in] position Value to increment and wrap.
     * @param[in] increment Number of elements to move by, up to buffer_length_. Defaults to 1.
     * @retval Incremented and wrapped position.
     */
    inline uint32_t Advance(uint32_t position, uint32_t increment = 1) {
        position += increment;
        return position >= 2 * buffer_length_ ? position - 2 * buffer_length_ : position;
    }

    /**
     * Buffer index of a position.
     */
    inline uint32_t Slot(uint32_t position) {
        return position >= buffer_length_ ? position - buffer_length_ : position;
    }

    PFBQueueConfig config_;
    bool buffer_was_dynamically_allocated_ = false;
    uint32_t buffer_length_;
    // Word-sized so that a load or store is a single instruction. Unlocked, only the reader stores head_ and only the
    // writer stores tail_ (except for overwrite_when_full).
    std::atomic<uint32_t> head_{0};
    std::atomic<uint32_t> tail_{0};
    mutable PFB_MUTEX_TYPE mutex_;
};

#endif
