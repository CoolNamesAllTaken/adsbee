#pragma once

#include <array>
#include <cstdint>
#include <functional>
#include <memory>
#include <utility>

template <typename Key, typename T, uint_fast32_t MaxSize, class Hash = std::hash<Key>,
          class KeyEqual = std::equal_to<Key>>
class HashMap {
   public:
    // Moveable but not copyable. Makes managing the underlying data easier
    HashMap() = default;
    ~HashMap() = default;
    HashMap(const HashMap& other) = delete;
    HashMap& operator=(const HashMap& other) = delete;
    HashMap(HashMap&& other) noexcept = default;
    HashMap& operator=(HashMap&& other) noexcept = default;

   private:
    using ElementT = std::pair<Key, T>;
    using DataArrayT = std::array<ElementT, MaxSize>;

    std::unique_ptr<DataArrayT> data = std::make_unique<DataArrayT>();
};