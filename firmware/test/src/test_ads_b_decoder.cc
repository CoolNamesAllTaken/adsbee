#include "gtest/gtest.h"
#include "ads_b_decoder.hh"

TEST(ADSBDecoder, RxQueuePush) {
    ADSBDecoder decoder = ADSBDecoder();
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 0);
    ASSERT_EQ(decoder.GetRxQueueFront(), 0);
    ASSERT_EQ(decoder.GetRxQueueRear(), 0);
    ASSERT_EQ(decoder.GetRxQueueBitOffset(), 0);

    ASSERT_TRUE(decoder.PushWord(0xDEADBEEF));
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 32);
    ASSERT_EQ(decoder.GetRxQueueFront(), 0);
    ASSERT_EQ(decoder.GetRxQueueRear(), 1);

    ASSERT_TRUE(decoder.PushWord(0xDEADBEEF));
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 64);
    ASSERT_EQ(decoder.GetRxQueueFront(), 0);
    ASSERT_EQ(decoder.GetRxQueueRear(), 2);

    ASSERT_EQ(decoder.GetRxQueueBitOffset(), 0);
}

TEST(ADSBDecoder, RxQueuePeek) {
    ADSBDecoder decoder = ADSBDecoder();
    uint32_t buffer = 0xFFFFEEEE;

    // try peeking when there's nothing there
    ASSERT_EQ(decoder.PeekBits(10, buffer), 0);
    // buffer modification in this case is OK

    // add some stuff
    ASSERT_TRUE(decoder.PushWord(0xDEADBEEF));
    ASSERT_TRUE(decoder.PushWord(0xFEEDBEEF));
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 64);
    
    // try peeking too many
    ASSERT_EQ(decoder.PeekBits(57, buffer), 32);
    ASSERT_EQ(buffer, 0xDEADBEEF);
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 64);

    // peek a regular amount
    ASSERT_EQ(decoder.PeekBits(16, buffer), 16);
    ASSERT_EQ(buffer, 0xBEEFu);
}

TEST(ADSBDecoder, RxQueuePopWholeWord) {
    ADSBDecoder decoder = ADSBDecoder();
    uint32_t buffer;

    ASSERT_TRUE(decoder.PushWord(0xDEADBEEF));
    ASSERT_TRUE(decoder.PushWord(0xFEEDBEEF));
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 64);

    // single word pop
    ASSERT_EQ(decoder.PopBits(32, buffer), 32);
    ASSERT_EQ(buffer, 0xDEADBEEF);
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 32);

    // too big pop
    ASSERT_TRUE(decoder.PushWord(0xEFEFEFEF));
    ASSERT_EQ(decoder.PopBits(89, buffer), 32);
    ASSERT_EQ(buffer, 0xFEEDBEEF);
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 32);

    // partial pop
    ASSERT_EQ(decoder.GetRxQueueBitOffset(), 0);
    ASSERT_EQ(decoder.PopBits(16, buffer), 16);
    ASSERT_EQ(decoder.GetRxQueueBitOffset(), 16);
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 16);
    ASSERT_EQ(buffer, 0xEFEFu);

    ASSERT_EQ(decoder.PopBits(16, buffer), 16);
    ASSERT_EQ(decoder.GetRxQueueBitOffset(), 0);
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 0);
    ASSERT_EQ(buffer, 0xEFEFu);

    // partial pop then push
    decoder.ClearRxQueue();
    ASSERT_EQ(decoder.GetRxQueueRear(), 0);
    ASSERT_TRUE(decoder.PushWord(0xDEADBEEF));
    // [ 0xDEADBEEF ]
    ASSERT_EQ(decoder.GetRxQueueRear(), 1);
    ASSERT_EQ(decoder.PopBits(4, buffer), 4);
    // [ 0xDEADBEE ]
    ASSERT_EQ(decoder.GetRxQueueBitOffset(), 4);
    ASSERT_EQ(decoder.GetRxQueueFront(), 0);
    ASSERT_EQ(buffer, 0b1111u);

    ASSERT_TRUE(decoder.PushWord(0xFEEDBEEF));
    // [ 0xFEEDBEEF | 0xDEADBEE ]
    ASSERT_EQ(decoder.GetRxQueueRear(), 2);
    ASSERT_EQ(decoder.PopBits(32, buffer), 32);
    // [ 0xFEEDBEE ]
    ASSERT_EQ(decoder.GetRxQueueFront(), 1);
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 28);
    ASSERT_EQ(decoder.GetRxQueueBitOffset(), 4);
    ASSERT_EQ(buffer, 0xFDEADBEE);

    ASSERT_EQ(decoder.PopBits(32, buffer), 28); // will only pop what's left
    // [ ]
    ASSERT_EQ(buffer, 0xFEEDBEEu);
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 0);
    ASSERT_EQ(decoder.GetRxQueueBitOffset(), 0);
    ASSERT_EQ(decoder.GetRxQueueFront(), 2);
    ASSERT_EQ(decoder.GetRxQueueRear(), 2);

    // pop with nothing there
    ASSERT_EQ(decoder.PopBits(45, buffer), 0);
}

TEST(ADSBDecoder, RxQueueSimple) {
    ADSBDecoder decoder = ADSBDecoder();
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 0);

    decoder.PushWord(0xDEADBEEF);
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 32);
    uint32_t buffer;
    ASSERT_EQ(decoder.PopBits(32, buffer), 32);
    ASSERT_EQ(buffer, 0xDEADBEEF);

    decoder.PushWord(0xBEEFBEEF);
    ASSERT_EQ(decoder.PopBits(8, buffer), 8);
    ASSERT_EQ(buffer, 0xEFu);
    ASSERT_EQ(decoder.PopBits(8, buffer), 8);
    ASSERT_EQ(buffer, 0xBEu);
    ASSERT_EQ(decoder.PopBits(4, buffer), 4);
    ASSERT_EQ(buffer, 0xFu);
    ASSERT_EQ(decoder.PopBits(4, buffer), 4);
    ASSERT_EQ(buffer, 0xEu);
    ASSERT_EQ(decoder.PopBits(8, buffer), 8);
    ASSERT_EQ(buffer, 0xBEu);
}

TEST(ADSBDecoder, RXQueueOverflow) {
    ADSBDecoder decoder = ADSBDecoder();
    uint32_t buffer;

    // aligned overflow
    for (uint16_t i = 0; i < decoder.kRxQueueMaxLenWords; i++) {
        ASSERT_TRUE(decoder.PushWord(0xDEADBEEF));
    }
    ASSERT_EQ(decoder.GetRxQueueLenBits(), decoder.kRxQueueMaxLenWords * 32); 
    ASSERT_FALSE(decoder.PushWord(0xCCCCCCCC)); // RX queue should reject overflow.
    for (uint16_t i = 0; i < decoder.kRxQueueMaxLenWords; i++) {
        ASSERT_EQ(decoder.PopBits(32, buffer), 32);
        ASSERT_EQ(buffer, 0xDEADBEEF);
        ASSERT_EQ(decoder.GetRxQueueLenBits(), (decoder.kRxQueueMaxLenWords - (i+1))*32);
    }

    // scooch down the circular buffer a little bit so that unaligned overflow test wraps
    ASSERT_TRUE(decoder.PushWord(0xDEEDBEED));
    ASSERT_EQ(decoder.PopBits(32, buffer), 32);
    ASSERT_EQ(buffer, 0xDEEDBEED);
    ASSERT_EQ(decoder.GetRxQueueFront(), 1);

    // unaligned overflow
    for (uint16_t i = 0; i < decoder.kRxQueueMaxLenWords; i++) {
        ASSERT_TRUE(decoder.PushWord(0xDEADBEEF));
    }
    ASSERT_EQ(decoder.GetRxQueueLenBits(), decoder.kRxQueueMaxLenWords * 32); 
    ASSERT_FALSE(decoder.PushWord(0xCCCCCCCC)); // RX queue should reject overflow.
    ASSERT_EQ(decoder.PopBits(8, buffer), 8);
    ASSERT_EQ(buffer, 0xEFu);
    for (uint16_t i = 0; i < decoder.kRxQueueMaxLenWords-1; i++) {
        ASSERT_EQ(decoder.PopBits(32, buffer), 32);
        ASSERT_EQ(buffer, 0xEFDEADBE);
        ASSERT_EQ(decoder.GetRxQueueLenBits(), (decoder.kRxQueueMaxLenWords - (i+1))*32 - 8);
    }
    ASSERT_EQ(decoder.PopBits(24, buffer), 24);
    ASSERT_EQ(buffer, 0xDEADBEu);
    ASSERT_EQ(decoder.GetRxQueueLenBits(), 0);
}