#ifndef DATA_STRUCTURES_HH_
#define DATA_STRUCTURES_HH_

#include <stdint.h>

#include <algorithm>  // For std::copy.
#include <cstring>    // For memcpy.

template <class T>
class PFBQueue {
   public:
    struct PFBQueueConfig {
        uint16_t buf_len_num_elements = 0;
        T *buffer = nullptr;
        bool overwrite_when_full = false;
    };

    /**
     * Constructor.
     * NOTE: Copy and move constructors are not implemented! Pass by reference only to avoid creating a "double free"
     * error, which is caused by two PFBQueues sharing the same buffer, and both trying to free it when they are
     * destroyed.
     * @param[in] config_in Defines length of the buffer, and points to the buffer of size buf_len_num_elements if
     * PFBQueue should work with a pre-allocated buffer. If config_in.buffer is left as nullptr, a buffer will be
     * dynamically allocated of size buf_len_num_elements * sizeof(T).
     * @retval PFBQueue object.
     */
    PFBQueue(PFBQueueConfig config_in) : config_(config_in), buffer_length_(config_in.buf_len_num_elements) {
        if (config_.buffer == nullptr) {
            config_.buffer = (T *)malloc(sizeof(T) * buffer_length_);
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

    inline bool IsFull() { return is_full_; }
    inline bool IsEmpty() { return (!is_full_ && (head_ == tail_)); }

    /**
     * Enqueues an element to the back of the buffer.
     * @param[in] element Object to push onto the back of the buffer.
     * @retval True if succeeded, false if the buffer is full.
     */
    bool Enqueue(T element) {
        if (is_full_) {
            if (!config_.overwrite_when_full) {
                // Buffer is full and not overwriting; cannot push.
                return false;
            } else {
                head_ = IncrementIndex(head_);  // Move head forward to overwrite the oldest element.
            }
        }

        // config_.buffer[tail_] = element;
        memcpy((uint8_t *)(&config_.buffer[tail_]), (uint8_t *)(&element), sizeof(T));
        tail_ = IncrementIndex(tail_);

        if (tail_ == head_) {
            is_full_ = true;
        }

        return true;
    }

    /**
     * Dequeues an element from the front of the buffer.
     * @param[out] element Reference to an object that will be overwritten by the contents of the popped element.
     * @retval True if successful, false if the buffer is empty.
     */
    bool Dequeue(T &element) {
        if (head_ == tail_ && !is_full_) {
            return false;
        }
        // element = config_.buffer[head_];
        memcpy((uint8_t *)(&element), (uint8_t *)(&config_.buffer[head_]), sizeof(T));
        head_ = IncrementIndex(head_);
        is_full_ = false;
        return true;
    }

    /**
     * Returns the contents of an element in the buffer without removing it from the buffer.
     * @param[out] element Reference to an object that will be overwritten by the contents of the peeked element.
     * @param[in] index Position in the buffer to peek. Defaults to 0 (the front of the buffer).
     * @retval True if successful, false if the buffer is empty or index is out of bounds.
     */
    bool Peek(T &element, uint16_t index = 0) {
        if (index >= Length()) {
            return false;
        }
        element = config_.buffer[IncrementIndex(head_, index)];
        return true;
    }

    /**
     * Discards a specified number of elements from the front of the buffer.
     * @param[in] num_elements Number of elements to discard from the front of the buffer.
     * @retval True if successful, false if there are not enough elements to discard.
     */
    inline bool Discard(uint16_t num_elements) {
        if (num_elements > Length()) {
            return false;  // Not enough elements to discard.
        }
        head_ = IncrementIndex(head_, num_elements);
        if (num_elements > 0) {
            is_full_ = false;
        }
        return true;
    }

    /**
     * Returns the number of elements currently in the buffer.
     * @retval Number of elements in the buffer.
     */
    inline uint16_t Length() {
        if (is_full_) {
            return buffer_length_;
        } else if (head_ > tail_) {
            return buffer_length_ - (head_ - tail_);  // Wrapped.
        } else {
            return tail_ - head_;  // Not wrapped.
        }
    }

    /**
     * Return the maximum number of elements that can be stored in the queue.
     * @retval Number of elements that can be stored in the queue.
     */
    inline uint16_t MaxNumElements() { return config_.buf_len_num_elements; }

    /**
     * Empty out the buffer by setting the head equal to the tail.
     */
    void Clear() {
        head_ = tail_ = 0;
        is_full_ = false;
    }

   private:
    /**
     * Increments and wraps a buffer index.
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
    bool is_full_ = false;  // New flag to distinguish full from empty when head == tail
    uint16_t buffer_length_;
    uint16_t head_ = 0;
    uint16_t tail_ = 0;
};

#endif