#pragma once

#include <stddef.h>
#include <stdint.h>

/**
 * Writes unmasked, unfragmented WebSocket frames (RFC 6455) to a stream socket so that the stream always holds whole
 * frames. A frame is skipped when the socket does not become writable in time, which leaves the stream intact. Once
 * part of a frame is on the wire the rest must follow: the writer waits for it, and reports the stream as broken if
 * it could not be written in time.
 */
class WebSocketFrameWriter {
   public:
    static constexpr uint8_t kHeaderMaxNumBytes = 4;
    static constexpr uint16_t kShortPayloadMaxNumBytes = 125;  // Longer payloads use the 16 bit length field.

    enum Result : uint8_t {
        kSent,     // The whole frame was written.
        kSkipped,  // Nothing was written. The stream is intact.
        kBroken    // Part of a frame was written. The connection must be closed.
    };

    /**
     * @param[out] header Buffer of at least kHeaderMaxNumBytes.
     * @retval Number of header bytes.
     */
    static uint8_t WriteHeader(uint8_t* header, uint8_t opcode, uint16_t payload_num_bytes) {
        header[0] = 0x80 | (opcode & 0x0F);  // Final fragment.
        if (payload_num_bytes <= kShortPayloadMaxNumBytes) {
            header[1] = payload_num_bytes;
            return 2;
        }
        header[1] = 126;
        header[2] = payload_num_bytes >> 8;
        header[3] = payload_num_bytes & 0xFF;
        return 4;
    }

    /**
     * @param[in] socket Provides:
     *      bool WaitWritable(uint32_t timeout_ms): true once a send would take bytes without waiting, false if that
     *          took longer than timeout_ms. 0 checks without waiting.
     *      int Send(const uint8_t* data, size_t num_bytes, bool wait): sends up to num_bytes and returns the number
     *          sent, or <= 0 if none could be sent. With wait false it returns right away, with wait true it waits
     *          for room up to the socket's own send timeout.
     *      uint32_t TimeMs(): time in milliseconds.
     * @param[in] writable_timeout_ms Longest time to wait for the socket before skipping the frame.
     * @param[in] completion_timeout_ms Longest time to wait for the rest of a partly written frame.
     */
    template <class Socket>
    static Result WriteFrame(Socket& socket, uint8_t opcode, const uint8_t* payload, uint16_t payload_num_bytes,
                             uint32_t writable_timeout_ms, uint32_t completion_timeout_ms) {
        if (!socket.WaitWritable(writable_timeout_ms)) {
            return kSkipped;
        }
        uint8_t header[kHeaderMaxNumBytes];
        const uint8_t header_num_bytes = WriteHeader(header, opcode, payload_num_bytes);
        const size_t frame_num_bytes = header_num_bytes + static_cast<size_t>(payload_num_bytes);

        size_t num_sent = 0;
        bool wait = false;
        uint32_t wait_start_ms = 0;
        while (num_sent < frame_num_bytes) {
            int ret;
            if (num_sent < header_num_bytes) {
                ret = socket.Send(header + num_sent, header_num_bytes - num_sent, wait);
            } else {
                ret = socket.Send(payload + (num_sent - header_num_bytes), frame_num_bytes - num_sent, wait);
            }
            if (ret > 0) {
                num_sent += ret;
                if (wait && num_sent < frame_num_bytes && socket.TimeMs() - wait_start_ms >= completion_timeout_ms) {
                    return kBroken;
                }
            } else if (num_sent == 0) {
                return kSkipped;
            } else if (wait) {
                return kBroken;
            } else {
                wait = true;
                wait_start_ms = socket.TimeMs();
            }
        }
        return kSent;
    }
};
