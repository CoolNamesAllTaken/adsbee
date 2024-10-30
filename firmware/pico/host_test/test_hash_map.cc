#include <functional>
#include <utility>
#include "gtest/gtest-death-test.h"
#include "gtest/gtest.h"
#include "hash_map.hh"
#include "gmock/gmock.h"

class HashMapTest : public testing::Test {
    protected:
        using MapType = HashMap<int, int, 3>;
        using MapIter = MapType::Iterator;

        MapType map;

};

using HashMapDeathTest = HashMapTest;

TEST_F(HashMapTest, NewMapShouldBeEmpty) {
    EXPECT_EQ(map.size(), 0ul);
    EXPECT_TRUE(map.empty());
    EXPECT_EQ(map.begin(), map.end());
}

TEST_F(HashMapTest, InsertOneShouldInsert) {
    map.insert(std::make_pair(1, 1));

    EXPECT_EQ(map.size(), 1ul);
    EXPECT_FALSE(map.empty());
    EXPECT_NE(map.begin(), map.end());

}

TEST_F(HashMapTest, InsertOneWith0HashShouldInsert) {
    map.insert(std::make_pair(0, 1));
    ASSERT_EQ(std::hash<int>{}(0), 0ul);

    EXPECT_EQ(map.size(), 1ul);
    EXPECT_FALSE(map.empty());
    EXPECT_NE(map.begin(), map.end());
}

TEST_F(HashMapTest,Insert2ShouldInsert) {
    map.insert(std::make_pair(1, 1));
    map.insert(std::make_pair(2, 2));

    EXPECT_EQ(map.size(), 2ul);
    EXPECT_FALSE(map.empty());
    EXPECT_NE(map.begin(), map.end());
}

TEST_F(HashMapTest, InsertTooManyShouldNotInsert) {
    map.insert(std::make_pair(1, 1));
    map.insert(std::make_pair(2, 2));
    map.insert(std::make_pair(3, 3));
    auto res = map.insert(std::make_pair(4, 4));
    
    EXPECT_EQ(res.first, map.end());
    EXPECT_FALSE(res.second);

    EXPECT_EQ(map.size(), 3ul);
    EXPECT_FALSE(map.empty());
    EXPECT_NE(map.begin(), map.end());
}

TEST_F(HashMapTest, InsertTwiceShouldNotInsert) {
    auto firstIns = map.insert(std::make_pair(1, 1));
    auto secondIns = map.insert(std::make_pair(1, 1));

    EXPECT_EQ(firstIns.first, secondIns.first);
    EXPECT_FALSE(secondIns.second);

    EXPECT_EQ(map.size(), 1ul);
    EXPECT_FALSE(map.empty());
    EXPECT_NE(map.begin(), map.end());
}

TEST_F(HashMapTest, ClearShouldEmptyMap) {
    map.insert(std::make_pair(1, 1));
    map.insert(std::make_pair(2, 2));

    EXPECT_EQ(map.size(), 2ul);
    EXPECT_FALSE(map.empty());
    EXPECT_NE(map.begin(), map.end());

    map.clear();

    EXPECT_EQ(map.size(), 0ul);
    EXPECT_TRUE(map.empty());
    EXPECT_EQ(map.begin(), map.end());
}

TEST_F(HashMapTest, EraseWIthIterShouldDecrementSize) {
    auto res = map.insert(std::make_pair(1, 1));
    map.erase(res.first);

    EXPECT_EQ(map.size(), 0ul);
    EXPECT_TRUE(map.empty());
    EXPECT_EQ(map.begin(), map.end());
}

TEST_F(HashMapDeathTest, EraseWithEndIterShouldFail) {
    auto res = map.insert(std::make_pair(1, 1));
    EXPECT_DEATH(map.erase(map.end()), testing::_);
}

TEST_F(HashMapTest, FindOnEmptyShouldReturnEnd) {
    auto res = map.find(1);

    EXPECT_EQ(res, map.end());
}

TEST_F(HashMapTest, FindShouldFindInsertedElement) {
    auto ins = map.insert(std::make_pair(1, 1));
    auto res = map.find(1);

    EXPECT_NE(res, map.end());
    EXPECT_EQ(res, ins.first);
}

TEST_F(HashMapTest, FindShouldNotFindNotInsertedElement) {
    auto ins = map.insert(std::make_pair(1, 1));
    auto res = map.find(2);

    EXPECT_EQ(res, map.end());
    EXPECT_NE(res, ins.first);
}

TEST_F(HashMapTest, FindShouldWorkOnFullMap) {
    //this test is sensitive to ordering. It really should be fixed

    std::vector<std::pair<MapIter, bool>> insertList;
    insertList.push_back(map.insert(std::make_pair(3, 3)));
    insertList.push_back(map.insert(std::make_pair(1, 1)));
    insertList.push_back(map.insert(std::make_pair(2, 2)));

    auto res = map.find(1);
    EXPECT_EQ(insertList[1].first, res) << "insertList[" << 1 << "] != map.find(" << 1 << ")";
    res = map.find(2);
    EXPECT_EQ(insertList[2].first, res) << "insertList[" << 2 << "] != map.find(" << 1 << ")";
    res = map.find(3);
    EXPECT_EQ(insertList[0].first, res) << "insertList[" << 0 << "] != map.find(" << 1 << ")";

    res = map.find(4);
    EXPECT_EQ(res, map.end());
}

TEST_F(HashMapTest, EraseWithKeyOnEmptyShouldNotErase){
    EXPECT_EQ(map.erase(1), 0ul);
}

TEST_F(HashMapTest, EraseWithKeyShouldErase) {
    auto ins = map.insert(std::make_pair(1, 1));
    EXPECT_EQ(map.erase(1), 1ul);
}

TEST_F(HashMapTest, EraseWithNonInsertedKeyShouldErase) {
    auto ins = map.insert(std::make_pair(1, 1));
    EXPECT_EQ(map.erase(2), 0ul);
}

//todo add tests for operator[]