#include "hardware_unit_tests.hh"

#include "adsbee.hh"
#include "eeprom.hh"

UTEST_STATE();

static bool utest_main_called = false;

CPP_AT_CALLBACK(ATTestCallback) {
    if (op == '=') {
        if (CPP_AT_HAS_ARG(0)) {
            if (args[0].compare("DUMP_EEPROM") == 0) {
                eeprom.Dump();
                CPP_AT_SILENT_SUCCESS();
            } else if (args[0].compare("CLEAR_EEPROM") == 0) {
                uint16_t eeprom_size_bytes = eeprom.GetSizeBytes();
                uint8_t buf[eeprom_size_bytes];
                memset(buf, 0xFF, eeprom_size_bytes);
                eeprom.WriteBuf(0x0, buf, eeprom_size_bytes);
                CPP_AT_SUCCESS();
            }
        }
    }

    if (!utest_main_called) {
        int argc = 0;
        const char* argv[1];
        int ret = utest_main(argc, argv);
        utest_main_called = true;
        if (ret >= 0) {
            CPP_AT_SUCCESS();
        } else {
            CPP_AT_ERROR("utest_main returned code %d", ret);
        }
    }

    CPP_AT_ERROR("Can't run utest_main multiple times because it'll break (janky af).");
}

CPP_AT_CALLBACK(ATIngestModeSCallback) {
    if (op == '=') {
        if (!CPP_AT_HAS_ARG(0)) {
            CPP_AT_ERROR(
                "Usage: AT+INGEST_MODE_S=<hex_data>,<sigs_dbm>,<sigq_db>,<mlat_counts>\r\n\t"
                "hex_data: 14 hex chars (squitter) or 28 hex chars (extended squitter).\r\n\t"
                "sigs_dbm, sigq_db, mlat_counts are optional.");
        }
        int32_t sigs_dbm_arg = INT16_MIN;
        int32_t sigq_db_arg = INT16_MIN;
        uint32_t mlat_counts_arg = 0;
        if (CPP_AT_HAS_ARG(1)) CPP_AT_TRY_ARG2NUM(1, sigs_dbm_arg);
        if (CPP_AT_HAS_ARG(2)) CPP_AT_TRY_ARG2NUM(2, sigq_db_arg);
        if (CPP_AT_HAS_ARG(3)) CPP_AT_TRY_ARG2NUM(3, mlat_counts_arg);

        std::string hex_str(args[0]);
        RawModeSPacket packet(hex_str.data(), -1, static_cast<int16_t>(sigs_dbm_arg),
                              static_cast<int16_t>(sigq_db_arg), static_cast<uint64_t>(mlat_counts_arg));

        if (packet.buffer_len_bytes != RawModeSPacket::kSquitterPacketLenBytes &&
            packet.buffer_len_bytes != RawModeSPacket::kExtendedSquitterPacketLenBytes) {
            CPP_AT_ERROR(
                "Invalid Mode S packet: got %d bytes, expected %d (squitter) or %d (extended squitter).",
                packet.buffer_len_bytes, RawModeSPacket::kSquitterPacketLenBytes,
                RawModeSPacket::kExtendedSquitterPacketLenBytes);
        }
        if (!adsbee.raw_mode_s_packet_queue.Enqueue(packet)) {
            CPP_AT_ERROR("Failed to enqueue Mode S packet: queue full.");
        }
        CPP_AT_SUCCESS();
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(ATIngestUATCallback) {
    if (op == '=') {
        if (!CPP_AT_HAS_ARG(0)) {
            CPP_AT_ERROR(
                "Usage: AT+INGEST_UAT=<hex_data|UPLINK>,<sigs_dbm>,<sigq_bits>,<mlat_counts>\r\n\t"
                "hex_data: %d hex chars (short ADS-B) or %d (long ADS-B).\r\n\t"
                "UPLINK: send UPLINK as hex_data, then send %d hex chars followed by newline.\r\n\t"
                "sigs_dbm, sigq_bits, mlat_counts are optional.",
                RawUATADSBPacket::kShortADSBMessageNumBytes * 2,
                RawUATADSBPacket::kLongADSBMessageNumBytes * 2,
                RawUATUplinkPacket::kUplinkMessageNumBytes * 2);
        }
        int32_t sigs_dbm_arg = INT16_MIN;
        int32_t sigq_bits_arg = INT16_MIN;
        uint32_t mlat_counts_arg = 0;
        if (CPP_AT_HAS_ARG(1)) CPP_AT_TRY_ARG2NUM(1, sigs_dbm_arg);
        if (CPP_AT_HAS_ARG(2)) CPP_AT_TRY_ARG2NUM(2, sigq_bits_arg);
        if (CPP_AT_HAS_ARG(3)) CPP_AT_TRY_ARG2NUM(3, mlat_counts_arg);

        const int16_t sigs_dbm = static_cast<int16_t>(sigs_dbm_arg);
        const int16_t sigq_bits = static_cast<int16_t>(sigq_bits_arg);
        const uint64_t mlat_counts = static_cast<uint64_t>(mlat_counts_arg);

        if (args[0].compare("UPLINK") == 0) {
            // Uplink hex strings are too long for a CppAT argument. Signal readiness and read the next line.
            static constexpr uint16_t kUplinkHexMaxLen = RawUATUplinkPacket::kUplinkMessageNumBytes * 2;
            static constexpr uint32_t kUplinkReadTimeoutMs = 5000;
            char hex_buf[kUplinkHexMaxLen + 1];
            CPP_AT_PRINTF("READY\r\n");

            int32_t hex_buf_len =
                comms_manager.ATReadConsole(hex_buf, kUplinkHexMaxLen, kUplinkReadTimeoutMs, /*terminate_on_newline=*/true);
            if (hex_buf_len < 0) {
                CPP_AT_ERROR("Timed out after %ums waiting for uplink hex data.", kUplinkReadTimeoutMs);
            }
            hex_buf[hex_buf_len] = '\0';

            RawUATUplinkPacket packet(hex_buf, sigs_dbm, sigq_bits, mlat_counts);
            if (packet.encoded_message_len_bytes != RawUATUplinkPacket::kUplinkMessageNumBytes) {
                CPP_AT_ERROR("Failed to construct UAT uplink packet (%d bytes parsed, expected %d).",
                             packet.encoded_message_len_bytes, RawUATUplinkPacket::kUplinkMessageNumBytes);
            }
            if (!adsbee.raw_uat_uplink_packet_queue.Enqueue(packet)) {
                CPP_AT_ERROR("Failed to enqueue UAT uplink packet: queue full.");
            }
        } else {
            uint16_t data_bytes = static_cast<uint16_t>(args[0].size() / 2);
            std::string hex_str(args[0]);

            if (data_bytes == RawUATADSBPacket::kShortADSBMessageNumBytes ||
                data_bytes == RawUATADSBPacket::kLongADSBMessageNumBytes) {
                RawUATADSBPacket packet(hex_str.c_str(), sigs_dbm, sigq_bits, mlat_counts);
                if (packet.buffer_len_bytes != data_bytes) {
                    CPP_AT_ERROR("Failed to construct UAT ADS-B packet from hex data (%d bytes parsed, expected %d).",
                                 packet.buffer_len_bytes, data_bytes);
                }
                if (!adsbee.raw_uat_adsb_packet_queue.Enqueue(packet)) {
                    CPP_AT_ERROR("Failed to enqueue UAT ADS-B packet: queue full.");
                }
            } else {
                CPP_AT_ERROR(
                    "Invalid UAT ADS-B packet length %d bytes. Expected %d (short) or %d (long). Use UPLINK for "
                    "uplink packets.",
                    data_bytes, RawUATADSBPacket::kShortADSBMessageNumBytes,
                    RawUATADSBPacket::kLongADSBMessageNumBytes);
            }
        }
        CPP_AT_SUCCESS();
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}