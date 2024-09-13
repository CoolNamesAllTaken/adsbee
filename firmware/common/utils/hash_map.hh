#pragma once

#include <array>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <utility>
#include <cassert>

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
        (*_usageList)[pos._index] = false;
        _size--;
        return Iterator(_data, _usageList, pos._index+1);
    }

    size_type erase(const Key& key) {
        auto& element = (*_usageList)[find(key)._index];
        if (element) {
            _size--;
            element = false;
            return 1;
        } else {
            return 0;
        }
    }

    size_type size() const noexcept {
        return _size;
    }

    T& operator[](const Key& key) {
        auto itr = find(key);
        if (itr == end()) {
            auto inserted = insert(std::pair<Key, T>(key, {}));
            assert(inserted.second && inserted.first != end());
            return inserted.first->second;
        } else {
            return itr->second;
        }
    }

    iterator find(const Key& key) {
        auto element = Hash{}(key) % MaxSize;
        const auto start = element;
        auto looped = false;
        while ((*_data)[element].first != key && (looped && element == start)) {
            element++;
            if (element == MaxSize) {
                element = 0;
                looped = true;
            }
        }

        if (looped && element == start) {
            return end();
        } else {
            return Iterator(_data, _usageList, element);
        }

    }

    const_iterator find(const Key& key) const {
        auto element = Hash{}(key) % MaxSize;
        const auto start = element;
        auto looped = false;
        while ((*_data)[element].first != key && (looped && element == start)) {
            element++;
            if (element == MaxSize) {
                element = 0;
                looped = true;
            }
        }

        if (looped && element == start) {
            return end();
        } else {
            return Iterator(_data, _usageList, element);
        }
    }

    bool empty() const noexcept {
        return _size == 0;
    }
    //end STL standard 

    std::pair<iterator, bool> insert(const value_type& value) {
        //early return for out of space
        if (size() == MaxSize) {
            return std::pair(end(), false);
        }

        auto element = findElement(value.first);

        if (!element.has_value()) {
            return std::pair(end(), false);
        } else if ((*_data)[element.value()].first == value.first) {
            return std::pair(Iterator(_data, _usageList, element.value()), false);
        } else {
            (*_data)[element.value()] = value;
            return std::pair(Iterator(_data, _usageList, element.value()), true);
        }
    }

   private:
    using DataArrayT = std::array<value_type, MaxSize>;

    std::optional<size_type> findElement(const Key& key) {
        auto element = Hash{}(key) % MaxSize;
        const auto start = element;
        auto looped = false;
        while ((*_usageList)[element] && (*_data)[element].first != key && (looped && element == start)) {
            element++;
            if (element == MaxSize) {
                element = 0;
                looped = true;
            }
        }
        if (looped && element == start) {
            return std::nullopt;
        } else {
            return element;
        }
    }

    std::shared_ptr<DataArrayT> _data = std::make_shared<DataArrayT>();
    std::shared_ptr<std::array<bool, MaxSize>> _usageList = std::make_shared<std::array<bool, MaxSize>>();
    size_type _size = 0;
};