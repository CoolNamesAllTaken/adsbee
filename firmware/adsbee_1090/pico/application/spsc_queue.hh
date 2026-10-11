#pragma once

#include <stdint.h>

/**
 * Lock-free queue for one writer and one reader, each of which may be an interrupt or run on its own core. The writer
 * only writes the tail index and the reader only the head index. Holds up to kDepth - 1 elements, which are filled and
 * read in place.
 */
template <class T, uint16_t kDepth>
class SPSCQueue {
   public:
    /**
     * Writer: slot for the next element.
     * @retval Slot to fill before calling Push(), or nullptr if the queue is full.
     */
    inline T* Back() {
        uint16_t tail = tail_;
        return Next(tail) == head_ ? nullptr : &buffer_[tail];
    }

    /**
     * Writer: makes the slot returned by Back() visible to the reader.
     */
    inline void Push() { tail_ = Next(tail_); }

    /**
     * Reader: oldest element.
     * @retval Element to use before calling Pop(), or nullptr if the queue is empty.
     */
    inline const T* Front() {
        uint16_t head = head_;
        return head == tail_ ? nullptr : &buffer_[head];
    }

    /**
     * Reader: releases the element returned by Front().
     */
    inline void Pop() { head_ = Next(head_); }

    inline uint16_t Length() const {
        uint16_t head = head_;
        uint16_t tail = tail_;
        return tail >= head ? tail - head : kDepth - head + tail;
    }

   private:
    static inline uint16_t Next(uint16_t index) { return index + 1 == kDepth ? 0 : index + 1; }

    T buffer_[kDepth] = {};
    volatile uint16_t head_ = 0;
    volatile uint16_t tail_ = 0;
};
