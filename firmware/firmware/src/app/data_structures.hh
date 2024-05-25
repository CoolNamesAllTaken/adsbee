#ifndef DATA_STRUCTURES_HH_
#define DATA_STRUCTURES_HH_

#include <stdint.h>

#include <algorithm>  // For std::copy.

#include "comms.hh"  // For debug prints.

template <class T>
class PFBQueue {
   public:
    struct PFBQueueConfig {
        uint16_t max_num_elements = 0;
        T* buffer = nullptr;
    };

    /**
     * Constructor.
     * NOTE: Copy and move constructors are not implemented! Pass by reference only to avoid creating a "double free"
     * error, which is caused by two PFBQueues sharing the same buffer, and both trying to free it when they are
     * destroyed.
     * @param[in] config_in Defines length of the buffer, and points to the buffer of size max_num_elements+1 if
     * PFBQueue should work with a pre-allocated buffer. If config_in.buffer is left as nullptr, a buffer will be
     * dynamically allocated of size max_num_elements * sizeof(T).
     * @retval PFBQueue object.
     */
    PFBQueue(PFBQueueConfig config_in) : config_(config_in), buffer_length_(config_in.max_num_elements + 1) {
        if (config_.buffer == nullptr) {
            config_.buffer = (T*)malloc(sizeof(T) * buffer_length_);
            buffer_was_dynamically_allocated_ = true;
        }
    }

    /**
     * Destructor. Frees the buffer buffer if it was dynamically allocated.
     */
    ~PFBQueue() {
        if (buffer_was_dynamically_allocated_ && config_.buffer != nullptr) {
            free(config_.buffer);
            config_.buffer = nullptr;  // Prevent double free in case of shallow copy.
        }
    }

    /**
     * Pushes an element onto the buffer.
     * @param[in] element Object to push onto the back of the buffer.
     * @retval True if succeeded, false if the buffer is full.
     */
    bool Push(T element) {
        uint16_t next_tail = IncrementIndex(tail_);
        if (next_tail == head_) {
            return false;
        }
        config_.buffer[tail_] = element;
        tail_ = next_tail;
        return true;
    }

    /**
     * Pops an element from the front of the buffer.
     * @param[out] element Reference to an object that will be overwritten by the contents of the popped element.
     * @retval True if successful, false if the buffer is empty.
     */
    bool Pop(T& element) {
        if (head_ == tail_) {
            return false;
        }
        element = config_.buffer[head_];
        head_ = IncrementIndex(head_);
        return true;
    }

    /**
     * Returns the contents of an element in the buffer without removing it from the buffer.
     * @param[out] element Reference to an object that will be overwritten by the contents of the peeked element.
     * @param[in] index Position in the buffer to peek. Defaults to 0 (the front of the buffer).
     * @retval True if successful, false if the buffer is empty or index is out of bounds.
     */
    bool Peek(T& element, uint16_t index = 0) {
        if (index >= Length()) {
            return false;
        }
        element = config_.buffer[IncrementIndex(head_, index)];
        return true;
    }

    /**
     * Returns the number of elements currently in the buffer.
     * @retval Number of elements in the buffer.
     */
    uint16_t Length() {
        if (head_ == tail_) {
            return 0;  // Empty.
        } else if (head_ > tail_) {
            return buffer_length_ - (head_ - tail_);  // Wrapped.
        } else {
            return tail_ - head_;  // Not wrapped.
        }
    }

   private:
    /**
     * Increments and wraps a buffer index. Index must be < 2*(config_.max_num_elements+1)!
     * @param[in] index Value to increment and wrap.
     * @param[in] increment Value to increment the index by. Defaults to 1.
     * @retval Incremented and wrapped value.
     */
    uint16_t IncrementIndex(uint16_t index, uint16_t increment = 1) {
        index += increment;
        return index >= buffer_length_ ? index - buffer_length_ : index;
    }

    PFBQueueConfig config_;
    bool buffer_was_dynamically_allocated_ = false;
    uint16_t buffer_length_;
    uint16_t head_ = 0;
    uint16_t tail_ = 0;
};

#endif