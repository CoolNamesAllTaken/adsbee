#include <functional>
#include <vector>

#include "gtest/gtest.h"
#include "websocket_frame_writer.hh"

static constexpr uint8_t kOpcodeBinary = 0x2;
static constexpr uint32_t kTimeoutMs = 1000;

// Stream socket with a bounded send buffer. Like lwIP, it is writable while more than half the buffer is free.
class FakeSocket {
   public:
    static constexpr size_t kSendBufNumBytes = 5760;

    std::vector<uint8_t> wire;                 // Every byte the socket accepted, in order.
    std::function<void()> on_wait = nullptr;   // Runs while the writer waits for room.
    uint32_t time_ms = 0;

    bool IsWritable() { return kSendBufNumBytes - num_unread_ > kSendBufNumBytes / 2; }
    bool WaitWritable(uint32_t timeout_ms) {
        if (!IsWritable() && timeout_ms > 0) {
            time_ms += timeout_ms;
            if (on_wait) on_wait();
        }
        return IsWritable();
    }
    int Send(const uint8_t* data, size_t num_bytes, bool wait) {
        if (num_unread_ == kSendBufNumBytes && wait) {
            time_ms += kTimeoutMs;  // The socket's own send timeout.
            if (on_wait) on_wait();
        }
        size_t num_taken = std::min(num_bytes, kSendBufNumBytes - num_unread_);
        if (num_taken == 0) return -1;
        wire.insert(wire.end(), data, data + num_taken);
        num_unread_ += num_taken;
        return num_taken;
    }
    uint32_t TimeMs() { return time_ms; }

    // The client reads from its end.
    void ClientReads(size_t num_bytes) { num_unread_ -= std::min(num_bytes, num_unread_); }
    void ClientReadsAll() { num_unread_ = 0; }
    // The client stops reading with this many bytes still unread.
    void Fill(size_t num_bytes) {
        wire.clear();
        num_unread_ = num_bytes;
    }

   private:
    size_t num_unread_ = 0;
};

// Splits a byte stream into frames. Returns false if the stream holds anything but whole binary frames.
static bool ParseFrames(const std::vector<uint8_t>& wire, std::vector<std::vector<uint8_t>>& payloads) {
    size_t i = 0;
    while (i < wire.size()) {
        if (wire.size() - i < 2 || wire[i] != (0x80 | kOpcodeBinary) || (wire[i + 1] & 0x80)) return false;
        size_t num_bytes = wire[i + 1];
        i += 2;
        if (num_bytes == 127) return false;
        if (num_bytes == 126) {
            if (wire.size() - i < 2) return false;
            num_bytes = (wire[i] << 8) | wire[i + 1];
            i += 2;
        }
        if (wire.size() - i < num_bytes) return false;
        payloads.emplace_back(wire.begin() + i, wire.begin() + i + num_bytes);
        i += num_bytes;
    }
    return true;
}

static std::vector<uint8_t> MakePayload(uint16_t num_bytes, uint8_t seed) {
    std::vector<uint8_t> payload(num_bytes);
    for (uint16_t i = 0; i < num_bytes; i++) payload[i] = seed + i;
    return payload;
}

static WebSocketFrameWriter::Result Write(FakeSocket& socket, const std::vector<uint8_t>& payload,
                                          uint32_t writable_timeout_ms = 0) {
    return WebSocketFrameWriter::WriteFrame(socket, kOpcodeBinary, payload.data(), payload.size(), writable_timeout_ms,
                                            kTimeoutMs);
}

TEST(WebSocketFrameWriter, Header) {
    uint8_t header[WebSocketFrameWriter::kHeaderMaxNumBytes];
    EXPECT_EQ(WebSocketFrameWriter::WriteHeader(header, 0x1, 0), 2);
    EXPECT_EQ(header[0], 0x81);
    EXPECT_EQ(header[1], 0);
    EXPECT_EQ(WebSocketFrameWriter::WriteHeader(header, 0x2, 125), 2);
    EXPECT_EQ(header[0], 0x82);
    EXPECT_EQ(header[1], 125);
    EXPECT_EQ(WebSocketFrameWriter::WriteHeader(header, 0xA, 126), 4);
    EXPECT_EQ(header[0], 0x8A);
    EXPECT_EQ(header[1], 126);
    EXPECT_EQ(header[2], 0);
    EXPECT_EQ(header[3], 126);
    EXPECT_EQ(WebSocketFrameWriter::WriteHeader(header, 0x2, 4000), 4);
    EXPECT_EQ(header[2], 4000 >> 8);
    EXPECT_EQ(header[3], 4000 & 0xFF);
}

TEST(WebSocketFrameWriter, SendsWholeFrames) {
    FakeSocket socket;
    std::vector<std::vector<uint8_t>> sent = {MakePayload(0, 0), MakePayload(125, 1), MakePayload(126, 2),
                                              MakePayload(4000, 3)};
    for (auto& payload : sent) {
        EXPECT_EQ(Write(socket, payload), WebSocketFrameWriter::kSent);
        socket.ClientReadsAll();
    }
    std::vector<std::vector<uint8_t>> received;
    ASSERT_TRUE(ParseFrames(socket.wire, received));
    EXPECT_EQ(received, sent);
}

TEST(WebSocketFrameWriter, SkipsFrameForSocketThatIsNotWritable) {
    FakeSocket socket;
    socket.Fill(FakeSocket::kSendBufNumBytes / 2);
    EXPECT_EQ(Write(socket, MakePayload(10, 0)), WebSocketFrameWriter::kSkipped);
    EXPECT_TRUE(socket.wire.empty());
    EXPECT_EQ(socket.time_ms, 0u);  // Did not wait.
}

TEST(WebSocketFrameWriter, WaitsForSocketToBecomeWritable) {
    FakeSocket socket;
    socket.Fill(FakeSocket::kSendBufNumBytes);
    // Still full after the wait: skipped, nothing on the wire.
    EXPECT_EQ(Write(socket, MakePayload(512, 0), 250), WebSocketFrameWriter::kSkipped);
    EXPECT_TRUE(socket.wire.empty());
    EXPECT_EQ(socket.time_ms, 250u);
    // The client reads during the wait: sent whole.
    socket.on_wait = [&socket]() { socket.ClientReadsAll(); };
    EXPECT_EQ(Write(socket, MakePayload(512, 0), 250), WebSocketFrameWriter::kSent);
    std::vector<std::vector<uint8_t>> received;
    ASSERT_TRUE(ParseFrames(socket.wire, received));
    EXPECT_EQ(received.size(), 1u);
}

TEST(WebSocketFrameWriter, FinishesFrameThatFitsOnlyInPart) {
    FakeSocket socket;
    socket.Fill(FakeSocket::kSendBufNumBytes / 2 - 100);  // Writable, with less room than the frame needs.
    socket.on_wait = [&socket]() { socket.ClientReadsAll(); };
    std::vector<uint8_t> payload = MakePayload(4000, 7);
    EXPECT_EQ(Write(socket, payload), WebSocketFrameWriter::kSent);
    std::vector<std::vector<uint8_t>> received;
    ASSERT_TRUE(ParseFrames(socket.wire, received));
    ASSERT_EQ(received.size(), 1u);
    EXPECT_EQ(received[0], payload);
}

TEST(WebSocketFrameWriter, ReportsBrokenStreamWhenRestOfFrameDoesNotFit) {
    FakeSocket socket;
    socket.Fill(FakeSocket::kSendBufNumBytes / 2 - 100);
    EXPECT_EQ(Write(socket, MakePayload(4000, 7)), WebSocketFrameWriter::kBroken);
    EXPECT_EQ(socket.time_ms, kTimeoutMs);  // Waited once.
    std::vector<std::vector<uint8_t>> received;
    EXPECT_FALSE(ParseFrames(socket.wire, received));  // Part of a frame is on the wire.
}

TEST(WebSocketFrameWriter, ReportsBrokenStreamWhenRestOfFrameTricklesPastTimeout) {
    FakeSocket socket;
    socket.Fill(FakeSocket::kSendBufNumBytes / 2 - 100);
    socket.on_wait = [&socket]() { socket.ClientReads(1); };
    EXPECT_EQ(Write(socket, MakePayload(4000, 7)), WebSocketFrameWriter::kBroken);
    EXPECT_EQ(socket.time_ms, kTimeoutMs);
}

// A client that stops reading for a while and then resumes sees only whole frames. Frames that fit a writable socket
// (up to half the send buffer) never leave the stream broken.
TEST(WebSocketFrameWriter, StalledClientKeepsValidStream) {
    for (uint16_t payload_num_bytes : {100, 440, 512, 2048, 2876}) {
        FakeSocket socket;
        std::vector<std::vector<uint8_t>> sent;
        uint16_t num_skipped = 0;
        bool stalled = false;
        for (uint16_t i = 0; i < 300; i++) {
            if (i == 200) socket.ClientReadsAll();  // Stalled for the first 200 frames.
            std::vector<uint8_t> payload = MakePayload(payload_num_bytes, i);
            // The server waits for a client once, then skips its frames without waiting until one is sent.
            WebSocketFrameWriter::Result result = Write(socket, payload, stalled ? 0 : 250);
            stalled = result != WebSocketFrameWriter::kSent;
            ASSERT_NE(result, WebSocketFrameWriter::kBroken) << "frame " << i << " of " << payload_num_bytes;
            if (result == WebSocketFrameWriter::kSent) {
                sent.push_back(payload);
            } else {
                num_skipped++;
            }
            if (i >= 200) socket.ClientReadsAll();
        }
        std::vector<std::vector<uint8_t>> received;
        ASSERT_TRUE(ParseFrames(socket.wire, received)) << payload_num_bytes;
        EXPECT_EQ(received, sent);
        EXPECT_GT(num_skipped, 150);
        EXPECT_GE(sent.size(), 101u);  // At least one before the stall and every frame after it.
        EXPECT_EQ(socket.time_ms, 250u);  // Waited once.
    }
}
