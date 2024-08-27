#pragma once

#include <array>
#include <cassert>
#include <cstdint>
#include <stack>

template <typename T, uint_fast32_t _itemCount>
class FreePoolAllocator {
   public:

    T* allocate(size_t allocCount) {

    }

    void deallocate() {

    }
    

   private:
    std::stack<uint_fast32_t> released;
    std::array<T, _itemCount> pool;
    uint_fast32_t ringPointer = 0;
};