#pragma once

#include <array>
#include <cassert>
#include <cstdint>
#include <stack>

template <typename T, uint_fast32_t _itemCount>
class FreePoolAllocator {
   public:
    T* allocate(size_t allocCount) {
        if (allocCount == 1) {
            if (!released.empty()) {
                auto element = released.top();
                released.pop();
                return &pool[element];
            } else {
                if (ringPointer == _itemCount) {
                    // out of elements in FPA
                    return nullptr; //should throw std::bad_alloc
                }
                return &pool[ringPointer++];
            }
        } else {
            if ( (_itemCount - ringPointer) < allocCount ){
                // not enough new elements to allocate all requested
                // TODO: check released list, that will be hard...
                return nullptr; //should throw std::bad_alloc
            } else {
                auto start = &pool[ringPointer];
                ringPointer += allocCount;
                return start;
            }
        }
    }

    void deallocate(T* ptr, size_t count) {
        auto startElement = (ptr - &pool[0]) / sizeof(ptr);
        for (size_t i = 0; i < count; i++) {
            released.push(startElement + i);
        }
    }

   private:
    std::stack<uint_fast32_t> released;
    std::array<T, _itemCount> pool;
    uint_fast32_t ringPointer = 0;
};