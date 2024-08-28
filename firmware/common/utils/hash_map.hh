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

    // standard STL unordered map functions and semantics
    class Iterator {
       public:
        using iterator_category = std::forward_iterator_tag;
        using difference_type = std::ptrdiff_t;
        using value_type = std::pair<Key, T>;
        using pointer = value_type*;
        using reference = value_type&;
        using size_type = uint_fast32_t;

        Iterator(std::shared_ptr<std::array<value_type, MaxSize>> data, std::shared_ptr<const std::array<bool, MaxSize>> usageList,
                 size_type index = 0)
            : _data(data), _usageList(usageList), _index(index) {
            // Move to the first used element
            advance_to_next_used();
        }

        reference operator*() const { return (*_data)[_index]; }

        pointer operator->() { return &((*_data)[_index]); }

        Iterator& operator++() {
            ++_index;
            advance_to_next_used();
            return *this;
        }

        Iterator operator++(int) {
            Iterator tmp = *this;
            ++(*this);
            return tmp;
        }

        friend bool operator==(const Iterator& a, const Iterator& b) { return a._index == b._index; }

        friend bool operator!=(const Iterator& a, const Iterator& b) { return a._index != b._index; }

        void advance_to_next_used() {
            while (_index < MaxSize && !(*_usageList)[_index]) {
                ++_index;
            }
        }

        std::shared_ptr<std::array<value_type, MaxSize>> _data;
        std::shared_ptr<const std::array<bool, MaxSize>> _usageList;
        size_type _index;
    };

    using size_type = uint_fast32_t;
    using value_type = std::pair<Key, T>;
    using pointer = value_type*;
    using reference = value_type&;
    using iterator = Iterator;
    using const_iterator = const Iterator;

    void clear() noexcept {
        for (size_type i = 0; i < MaxSize; i++){
            (*_usageList)[i] = false;
        }
    }

    iterator begin() noexcept {
        return Iterator(_data, _usageList);
    }

    const_iterator begin() const noexcept {
        return Iterator(_data, _usageList);
    }

    const_iterator cbegin() const noexcept {
        return Iterator(_data, _usageList);
    }

    iterator end() noexcept{
        return Iterator(_data, _usageList, MaxSize);
    }

    const_iterator end() const noexcept {
        return Iterator(_data, _usageList, MaxSize);
    }

    const_iterator cend() const noexcept {
        return Iterator(_data, _usageList, MaxSize);
    }

    iterator erase(iterator pos) {
        //todo
    }

    size_type erase(const Key& key) {
        //todo
    }

    size_type size() const noexcept {
        // todo
    }

    T& operator[](const Key& key) {
        // todo
    }

    iterator find(const Key& key) {
        //todo
    }

    const_iterator find(const Key& key) const {
        //todo
    }
    //end STL standard 

   private:
    using DataArrayT = std::array<value_type, MaxSize>;

    std::shared_ptr<DataArrayT> _data = std::make_shared<DataArrayT>();
    std::shared_ptr<std::array<bool, MaxSize>> _usageList = std::make_shared<std::array<bool, MaxSize>>();
    size_type _size = 0;
};