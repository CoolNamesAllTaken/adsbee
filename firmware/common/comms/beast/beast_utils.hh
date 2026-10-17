#pragma once

#include <stdio.h>

#include "mode_s_packet.hh"
#include "receiver_position.hh"
#include "uat_packet.hh"

namespace BeastReporter {

const uint8_t kBeastEscapeChar = 0x1a;
const uint16_t kBeastMLATTimestampNumBytes = 6;

// Beast Frame Structure
// <preceded by 0x1a escape character>
// 1 Byte Frame type (does not need escape).
// 1-2 Byte RSSI (may need escape Byte).
// 6-12 Byte MLAT Timestamp (may need 6x escape Bytes).
// Mode-S data (2 bytes + escapes for Mode A/C, 7 bytes + escapes for squitter, 14 bytes + escapes for extended
// squitter)

/**
 * Mode S Packet Format
 *
 * 0x1a | frame type byte (no escapes) | timestamp | rssi | payload
 */

/**
 * UAT Packet Format
 *
 * 0x1a | 0xec (frame type UAT) | uat message type byte (no escapes) | timestamp | rssi | payload
 */

constexpr uint16_t kModeSBeastFrameMaxLenBytes =
    1 /* Frame Type */ + 2 * 6 /* MLAT timestamp + escapes */ + 2 /* RSSI + escape */ +
    2 * RawModeSPacket::kExtendedSquitterPacketLenBytes /* Longest Mode S data + escapes */;  // [Bytes]
constexpr uint16_t kUATADSBBeastFrameMaxLenBytes = 1 /* Frame Type */ + 1 /* UAT Message Type */ +
                                                   2 * 6 /* MLAT timestamp + escapes */ + 2 /* RSSI + escape */ +
                                                   2 * RawUATADSBPacket::kADSBMessageMaxSizeBytes;  // [Bytes]
constexpr uint16_t kUATUplinkBeastFrameMaxLenBytes = 1 /* Frame Type */ + 1 /* UAT Message Type */ +
                                                     2 * 6 /* MLAT timestamp + escapes */ + 2 /* RSSI + escape */ +
                                                     2 * RawUATUplinkPacket::kUplinkMessageNumBytes;  // [Bytes]

constexpr uint16_t kUuidNumChars = 36;
constexpr uint16_t kReceiverIDLenBytes = 8;

enum BeastFrameType {
    kBeastFrameTypeInvalid = 0x0,
    kBeastFrameTypeIngestId = 0xe3,  // Used by readsb for forwarding messages internally.
    kBeastFrameTypeFeedId = 0xe4,    // Used by readsb for establishing a feed with a UUID.
    kBeastFrameTypeUAT =
        0xec,  // Used for encapsulated UAT ADSB short messages, UAT ADSB long messages, and UAT uplink messages.
    kBeastFrameTypeModeAC = 0x31,  // Note: This is not used, since I'm assuming it does NOT refer to DF 4,5.
    kBeastFrameTypeModeSShort = 0x32,
    kBeastFrameTypeModeSLong = 0x33,
    kBeastFrameTypeReceiverInfo = 0xe9  // ADSBee MLAT feed (software/adsbee_mlat/PROTOCOL.md).
};

enum UATMessageTypeChar : char {
    kUATMessageTypeADSBShort = 's',
    kUATMessageTypeADSBLong = 'l',
    kUATMessageTypeUplink = 'u'
};

/**
 * Returns the Beast frame type corresponding to a RawModeSPacket.
 * NOTE: kBeastFrameTypeModeAC is not used, since ADSBee only decodes Mode S.
 * @param[in] packet RawModeSPacket to get the downlink format from.
 * @retval BeastFrameType corresponding the packet, or kBeastFrameTypeInvalid if it wasn't recognized.
 */
BeastFrameType GetBeastFrameType(RawModeSPacket packet);

/**
 * Writes the specified number of bytes from from_buf to to_buf, adding 0x1a escape characters as necessary.
 * @param[out] to_buf Buffer to write to.
 * @param[in] from_buf Buffer to read from.
 * @param[in] from_buf_num_bytes Number of Bytes to write, not including escape characters that will be added.
 * @retval Number of bytes (including escapes) that were written to to_buf.
 */
uint16_t WriteBufferWithBeastEscapes(uint8_t to_buf[], const uint8_t from_buf[], uint16_t from_buf_num_bytes);

uint16_t BuildFeedStartFrame(uint8_t *beast_frame_buf, uint8_t *receiver_id);

/**
 * Converts a DecodedModeSPacket payload to a data buffer in Mode S Beast output format.
 * @param[out] beast_frame_buf Pointer to byte buffer to fill with payload.
 * @param[in] packet Reference to DecodedModeSPacket to convert.
 * @param[in] timestamp_48mhz Send the 48MHz timestamp (MLAT feed) instead of the 12MHz one (classic Beast).
 * @retval Number of bytes written to beast_frame_buf.
 */
uint16_t BuildModeSBeastFrame(uint8_t *beast_frame_buf, const DecodedModeSPacket &packet,
                              bool timestamp_48mhz = false);

constexpr uint32_t kMLATFeedClockHz = 48000000;  // Timestamp clock of the MLAT feed.
constexpr uint16_t kReceiverInfoFrameMaxLenBytes = 512;
constexpr uint16_t kReceiverInfoIDMaxLen = 32;
constexpr uint16_t kReceiverInfoNameMaxLen = 32;
constexpr uint16_t kReceiverInfoFirmwareVersionMaxLen = 40;

/**
 * Contents of an MLAT feed receiver info frame (0x1a 0xe9 <key=value;...> 0x0a).
 */
struct ReceiverInfo {
    char id[kReceiverInfoIDMaxLen + 1] = {0};  // Characters outside [0-9A-Za-z_.-] are sent as '_'.
    uint32_t clock_hz = kMLATFeedClockHz;
    uint32_t epoch = 0;  // Changes whenever the timestamp counter restarts.
    ReceiverPosition position;
    ReceiverPPS pps;
    char name[kReceiverInfoNameMaxLen + 1] = {0};  // Optional. ';' '=' and non-printable characters are sent as '_'.
    char firmware_version[kReceiverInfoFirmwareVersionMaxLen + 1] = {0};  // Optional, same rule as name.
};

/**
 * Writes a firmware version as in release tags: <product>-M.m.p, with -rcN for a release candidate.
 */
inline void FormatFirmwareVersion(char *buf, uint16_t buf_len, const char *product, uint8_t major, uint8_t minor,
                                  uint8_t patch, uint8_t release_candidate) {
    int n = snprintf(buf, buf_len, "%s-%u.%u.%u", product, major, minor, patch);
    if (release_candidate != 0 && n > 0 && n < buf_len) {
        snprintf(buf + n, buf_len - n, "-rc%u", release_candidate);
    }
}

/**
 * Writes a receiver info frame. The payload is printable ASCII, so it needs no Beast escapes.
 * @param[out] buf Buffer to write to.
 * @param[in] buf_len Size of buf. kReceiverInfoFrameMaxLenBytes is always enough.
 * @param[in] info Values to send. Position fields are left out when info.position has no source.
 * @retval Number of bytes written, or 0 if the frame didn't fit or info.id is empty.
 */
uint16_t BuildReceiverInfoFrame(uint8_t *buf, uint16_t buf_len, const ReceiverInfo &info);

/**
 * Writes the short receiver info frame that starts every MLAT UDP datagram: v, id, clk and ep. clk is there so that
 * a server that first hears of the receiver from it doesn't assume another clock rate.
 * @retval Number of bytes written, or 0 if the frame didn't fit or info.id is empty.
 */
uint16_t BuildShortReceiverInfoFrame(uint8_t *buf, uint16_t buf_len, const ReceiverInfo &info);

/**
 * When an MLAT feed sink sends its next receiver info frame: first on each connection, then every 10 seconds, every
 * second while the receiver may move, and right away when the clock epoch, the moving flag or the position source
 * changes.
 */
class ReceiverInfoSchedule {
   public:
    static constexpr uint32_t kIntervalMs = 10000;
    static constexpr uint32_t kMovingIntervalMs = 1000;

    bool Due(uint32_t timestamp_ms, const ReceiverInfo &info) const {
        return !sent_ || info.epoch != epoch_ || info.position.moving != moving_ ||
               info.position.source != source_ ||
               timestamp_ms - last_sent_timestamp_ms_ >= (moving_ ? kMovingIntervalMs : kIntervalMs);
    }
    void MarkSent(uint32_t timestamp_ms, const ReceiverInfo &info) {
        sent_ = true;
        epoch_ = info.epoch;
        moving_ = info.position.moving;
        source_ = info.position.source;
        last_sent_timestamp_ms_ = timestamp_ms;
    }
    // Call when the sink's connection (re)starts.
    void Restart() { sent_ = false; }

   private:
    bool sent_ = false;
    uint32_t epoch_ = 0;
    bool moving_ = false;
    ReceiverPosition::Source source_ = ReceiverPosition::kSourceNone;
    uint32_t last_sent_timestamp_ms_ = 0;
};

/**
 * Sends an Ingest Beast frame (0xe3) with a 16-Byte receiver ID prepended. This type of frame is used by readsb when
 * forwarding messages internally. For feeding, see BuildModeSBeastFrame.
 * @param[out] beast_frame_buf Pointer to byte buffer to fill with payload.
 * @param[in] packet Reference to DecodedModeSPacket to convert.
 * @param[in] receiver_id Pointer to 16-Byte receiver ID.
 * @retval Number of bytes written to beast_frame_buf.
 */
uint16_t BuildModeSIngestBeastFrame(uint8_t *beast_frame_buf, const DecodedModeSPacket &packet,
                                    const uint8_t *receiver_id);

/**
 * Write a UAT ADSB frame.
 * @param[out] beast_frame_buf Pointer to byte buffer to fill with payload.
 * @param[in] packet Reference to RawUATADSBPacket to write to the buffer. Takes the raw packet (not the decoded one) so
 * that callers holding raw packets don't trigger an implicit DecodedUATADSBPacket construction (a full RS decode on
 * FEC-capable platforms) just to build a frame.
 * @retval Number of bytes written to beast_frame_buf.
 */
uint16_t BuildUATADSBBeastFrame(uint8_t *beast_frame_buf, const RawUATADSBPacket &packet);

/**
 * Write a UAT uplink frame.
 * @param[out] beast_frame_buf Pointer to byte buffer to fill with payload.
 * @param[in] packet Reference to RawUATUplinkPacket to write to the buffer. Takes the raw packet (not the decoded one)
 * so that callers holding raw packets don't trigger an implicit DecodedUATUplinkPacket construction (6 RS block
 * decodes on FEC-capable platforms) just to build a frame.
 * @retval Number of bytes written to beast_frame_buf.
 */
uint16_t BuildUATUplinkBeastFrame(uint8_t *beast_frame_buf, const RawUATUplinkPacket &packet);

}  // namespace BeastReporter
