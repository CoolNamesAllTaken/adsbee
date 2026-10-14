// Chain steal rule (lr2021_drain_state.hh): when the IRQ-paced chain may take the bus from the loop drain.
#include <vector>

#include "gtest/gtest.h"
#include "lr2021_drain_state.hh"

using S = LR2021DrainState;

static constexpr uint16_t kOnePacket = 14;

// Loop drain states in order, kLevelCmdWait to kError.
static std::vector<S> LoopStates() {
    std::vector<S> states;
    for (uint8_t i = static_cast<uint8_t>(S::kLevelCmdWait); i <= static_cast<uint8_t>(S::kError); i++) {
        states.push_back(static_cast<S>(i));
    }
    return states;
}

TEST(LR2021DrainState, NeverStolenWithAFrameOnTheBus) {
    for (S s : LoopStates()) {
        EXPECT_EQ(LR2021ChainStealCheck(s, true, 0), LR2021DrainSteal::kBusy) << static_cast<int>(s);
        EXPECT_EQ(LR2021ChainStealCheck(s, true, kOnePacket), LR2021DrainSteal::kBusy) << static_cast<int>(s);
    }
}

TEST(LR2021DrainState, StolenWithAnUnparsedReadKeepsIt) {
    // From the completed ReadRxFifo frame through the whole clear tail, the payload is only in the async buffer.
    for (S s : {S::kFifoRead, S::kClearFifoWait, S::kClearFifoCmd, S::kClearFifoRsp, S::kIrqCmdWait, S::kIrqCmd,
                S::kIrqRspWait, S::kIrqRsp}) {
        EXPECT_EQ(LR2021ChainStealCheck(s, false, kOnePacket), LR2021DrainSteal::kKeepRead) << static_cast<int>(s);
    }
}

TEST(LR2021DrainState, EveryStealOfAHeldReadKeepsIt) {
    for (S s : LoopStates()) {
        for (uint16_t len : {uint16_t{0}, kOnePacket}) {
            if (LR2021ChainStealCheck(s, false, len) == LR2021DrainSteal::kAllowed) {
                EXPECT_FALSE(LR2021LoopDrainHoldsRead(s, len)) << static_cast<int>(s);
            }
        }
    }
}

TEST(LR2021DrainState, ChainTakesTheClearTailAfterAGoodReadWithTheLineHigh) {
    for (S s : LoopStates()) {
        EXPECT_EQ(LR2021ChainTakesLoopTail(s, true, true), s == S::kFifoRead) << static_cast<int>(s);
        EXPECT_FALSE(LR2021ChainTakesLoopTail(s, false, true)) << static_cast<int>(s);
        EXPECT_FALSE(LR2021ChainTakesLoopTail(s, true, false)) << static_cast<int>(s);
    }
    EXPECT_FALSE(LR2021ChainTakesLoopTail(S::kIdle, true, true));
    EXPECT_FALSE(LR2021ChainTakesLoopTail(S::kChainFifoRead, true, true));
}

TEST(LR2021DrainState, SkippedEdgeIsRetriedOnlyWhereNothingWasPoppedSince) {
    for (S s : LoopStates()) {
        bool retried = (s == S::kLevelCmd || s == S::kLevelRsp || s == S::kIrqRsp || s == S::kDataReady);
        EXPECT_EQ(LR2021ChainRetriesSkippedEdge(s), retried) << static_cast<int>(s);
    }
    // A completed ReadRxFifo frame goes to LR2021ChainTakesLoopTail() instead.
    EXPECT_FALSE(LR2021ChainRetriesSkippedEdge(S::kFifoRead));
    EXPECT_FALSE(LR2021ChainRetriesSkippedEdge(S::kIdle));
    EXPECT_FALSE(LR2021ChainRetriesSkippedEdge(S::kChainFifoRead));
}

TEST(LR2021DrainState, StolenBeforeTheReadIsPosted) {
    // Nothing popped from the FIFO yet: the chain reads it instead.
    for (S s : {S::kLevelCmdWait, S::kLevelCmd, S::kLevelRspWait, S::kLevelRsp, S::kFifoWait}) {
        EXPECT_EQ(LR2021ChainStealCheck(s, false, kOnePacket), LR2021DrainSteal::kAllowed) << static_cast<int>(s);
    }
}

TEST(LR2021DrainState, ClearTailWithoutAReadIsStolenExceptWithFifoFlagsPending) {
    for (S s : {S::kClearFifoWait, S::kClearFifoCmd, S::kClearFifoRsp, S::kIrqCmdWait, S::kIrqCmd, S::kIrqRspWait,
                S::kIrqRsp}) {
        EXPECT_EQ(LR2021ChainStealCheck(s, false, 0), LR2021DrainSteal::kAllowed) << static_cast<int>(s);
    }
    EXPECT_EQ(LR2021ChainStealCheck(S::kClearFifoRspWait, false, 0), LR2021DrainSteal::kBusy);
    EXPECT_EQ(LR2021ChainStealCheck(S::kClearFifoRspWait, false, kOnePacket), LR2021DrainSteal::kBusy);
}

TEST(LR2021DrainState, TerminalStatesAreNeverStolen) {
    for (uint16_t len : {uint16_t{0}, kOnePacket}) {
        EXPECT_EQ(LR2021ChainStealCheck(S::kDataReady, false, len), LR2021DrainSteal::kBusy);
        EXPECT_EQ(LR2021ChainStealCheck(S::kError, false, len), LR2021DrainSteal::kBusy);
    }
}

TEST(LR2021DrainState, ChainStatesAreTheLastBlock) {
    EXPECT_FALSE(LR2021DrainIsChainState(S::kIdle));
    EXPECT_FALSE(LR2021DrainIsChainState(S::kError));
    EXPECT_TRUE(LR2021DrainIsChainState(S::kChainFifoWait));
    EXPECT_TRUE(LR2021DrainIsChainState(S::kChainIrqRsp));
}
