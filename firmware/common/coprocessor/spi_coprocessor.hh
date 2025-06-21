#ifndef SPI_COPROCESSOR_HH_
#define SPI_COPROCESSOR_HH_

#include "aircraft_dictionary.hh"
#include "comms.hh"
#include "hal.hh"
#include "macros.hh"
#include "object_dictionary.hh"
#include "settings.hh"
#include "spi_coprocessor_interface.hh"
#include "transponder_packet.hh"

class SPICoprocessor : public SPICoprocessorInterface {
   public:
    static constexpr uint16_t kSPITransactionQueueLenTransactions = 3;

    static constexpr uint16_t kSPITransactionMaxNumRetries =
        3;  // Max num retries per block in a multi-transfer transaction.

    struct SPICoprocessorConfig {
#ifdef ON_COPRO_MASTER
        SPICoprocessorSlaveInterface &interface;  // Reference to the slave interface.
#elif defined(ON_COPRO_SLAVE)
        SPICoprocessorMasterInterface &interface;  // Reference to the master interface.
#else
        SPICoprocessorInterface &interface;  // Reference to the interface. Not used on other platforms.
#endif
    };

    /**
     * Constructor
     */
    SPICoprocessor(SPICoprocessorConfig config_in)
        : config_(config_in) {

          };

    bool Init();
    bool DeInit();

#ifdef ON_COPRO_MASTER
    bool IsEnabled() { return config_.interface.IsEnabled(); }
    void SetEnable(bool enabled) { config_.interface.SetEnable(enabled); }
#endif
    /**
     *
     * @param[in] blocking On RP2040, blocks until kSPIMinTransactionIntervalUs after the previous transaction to check
     * to see if the ESP32 has anything to say. Set to true if using this as a way to flush the ESP32 of messages before
     * writing to it. On ESP32, has no effect.
     */
    bool Update(bool blocking = false);

    void UpdateNetworkLED() {
#ifdef ON_COPRO_SLAVE
        config_.interface.UpdateNetworkLED();
#endif
    }

    /**
     * Top level function that translates a write to an object (with associated address) into SPI transaction(s).
     * Included in the header file since the template function implementation needs to be visible to any file that
     * utilizes it.
     */
    template <typename T>
    bool Write(ObjectDictionary::Address addr, T &object, bool require_ack = false, uint16_t len_bytes = 0) {
        if (len_bytes == 0) {
            len_bytes = sizeof(object);
        }
#ifdef ON_COPRO_SLAVE
        if (!config_.interface.SPIClaimNextTransaction()) {
            CONSOLE_ERROR("SPICoprocessor::Write", "Failed to claim SPI transaction mutex.");
            return false;
        }
#elif ON_PICO

#else
        return false;  // Not supported on other platforms.
#endif
        if (len_bytes < SCWritePacket::kDataMaxLenBytes) {
            // Single write. Write the full object at once, no offset, require ack if necessary.
            bool ret = PartialWrite(addr, (uint8_t *)&object, len_bytes, 0, require_ack);
            config_.interface.SPIReleaseNextTransaction();
            return ret;
        }
        // Multi write.
        int16_t bytes_remaining = len_bytes;
        while (bytes_remaining > 0) {
            if (!PartialWrite(addr,                                                   // addr
                              (uint8_t *)(&object),                                   // object
                              MIN(SCWritePacket::kDataMaxLenBytes, bytes_remaining),  // len
                              len_bytes - bytes_remaining,                            // offset
                              require_ack)                                            // require_ack
            ) {
                CONSOLE_ERROR("SPICoprocessor::Write",
                              "Multi-transfer %d Byte write of object at address 0x%x failed with %d Bytes remaining.",
                              len_bytes, addr, bytes_remaining);
                config_.interface.SPIReleaseNextTransaction();
                return false;
            }
            bytes_remaining -= SCWritePacket::kDataMaxLenBytes;
        }
        // No bytes remaining.
        config_.interface.SPIReleaseNextTransaction();
        return true;
    }

    /**
     * Top level function that translates a read from an object (with associated address) into SPI transaction(s).
     * Included in the header file since the template function implementation needs to be visible to any file that
     * utilizes it.
     */
    template <typename T>
    bool Read(ObjectDictionary::Address addr, T &object, uint16_t len_bytes = 0) {
        if (len_bytes == 0) {
            len_bytes = sizeof(object);
        }
#ifdef ON_COPRO_MASTER
#elif defined(ON_COPRO_SLAVE)
        if (!config_.interface.SPIClaimNextTransaction()) {
            CONSOLE_ERROR("SPICoprocessor::Read", "Failed to claim SPI transaction mutex.");
            return false;
        }
#else
        return false;  // Not supported on other platforms.
#endif
        if (len_bytes < SCResponsePacket::kDataMaxLenBytes) {
            // Single read.
            bool ret = PartialRead(addr, (uint8_t *)&object, len_bytes);
            config_.interface.SPIReleaseNextTransaction();
            return ret;
        }
        // Multi-read.
#ifdef ON_COPRO_MASTER
        // Write and read are separate transactions.
        uint16_t max_chunk_size_bytes = SCResponsePacket::kDataMaxLenBytes;
#elif defined(ON_COPRO_SLAVE)
        // Write and read are a single transaction.
        uint16_t max_chunk_size_bytes = SCResponsePacket::kDataMaxLenBytes - SCReadRequestPacket::kBufLenBytes;
#else
        uint16_t max_chunk_size_bytes = 0;  // Dummy to stop compile errors.
#endif
        int16_t bytes_remaining = len_bytes;
        while (bytes_remaining > 0) {
            if (!PartialRead(addr,                                        // address
                             (uint8_t *)(&object),                        // object
                             MIN(max_chunk_size_bytes, bytes_remaining),  // len
                             len_bytes - bytes_remaining)                 // offset
            ) {
                CONSOLE_ERROR("SPICoprocessor::Read",
                              "Multi-transfer %d Byte read of object at address 0x%x failed with %d Bytes remaining.",
                              len_bytes, addr, bytes_remaining);
                config_.interface.SPIReleaseNextTransaction();
                return false;
            }
            bytes_remaining -=
                max_chunk_size_bytes;  // Overshoot on purpose on the last chunk. Bytes remaining will go negative.
        }
        // No bytes remaining.
        config_.interface.SPIReleaseNextTransaction();
        return true;
    }

#ifdef ON_COPRO_SLAVE
    /**
     * Log a message to the coprocessor. Not available on RP2040 since it's the master (other stuff logs to it).
     * @param[in] log_level Log level of the message.
     * @param[in] tag Tag to prepend to the message.
     * @param[in] format Format string for the message.
     * @param[in] ... Variable arguments for the format string.
     */
    bool LogMessage(SettingsManager::LogLevel log_level, const char *tag, const char *format, va_list args);
#endif

   protected:
    bool PartialWrite(ObjectDictionary::Address addr, uint8_t *object_buf, uint16_t len, uint16_t offset = 0,
                      bool require_ack = false);

    bool PartialRead(ObjectDictionary::Address addr, uint8_t *object_buf, uint16_t len, uint16_t offset = 0);

    /**
     * Send an SCResponse packet with a single byte ACK payload.
     * @param[in] success True if sending an ACK, false if sending a NACK.
     * @retval True if ACK was transmitted successfully, false if something went wrong.
     */
    bool SPISendAck(bool success);

    /**
     * Blocks until an ACK is received or a timeout is reached.
     * @retval True if received an ACK, false if received NACK or timed out.
     */
    bool SPIWaitForAck();

    /**
     * Low level HAL for SPI Write Read call. Transmits the contents of tx_buf and receives into rx_buf.
     * Both buffers MUST be at least kSPITransactionMaxLenBytes Bytes long.
     * @param[in] tx_buf Buffer with data to transmit.
     * @param[in] rx_buf Buffer to fill with data that is received.
     * @param[in] len_bytes Number of bytes to transmit. Only has an effect when this function is being called on the
     * master.
     * @param[in] end_transaction Whether to de-assert chip select at the end of the transaction. Only has an effect
     * when this function is being called on the master.
     * @retval Number of bytes that were written and read, or a negative value if something broke.
     */
    int SPIWriteReadBlocking(uint8_t *tx_buf, uint8_t *rx_buf, uint16_t len_bytes = kSPITransactionMaxLenBytes,
                             bool end_transaction = true);

    // Write / Read aliases for SPIWriteReadBlocking.
    inline int SPIWriteBlocking(uint8_t *tx_buf, uint16_t len_bytes = kSPITransactionMaxLenBytes,
                                bool end_transaction = true) {
        return SPIWriteReadBlocking(tx_buf, nullptr, len_bytes, end_transaction);
    }
    inline int SPIReadBlocking(uint8_t *rx_buf, uint16_t len_bytes = kSPITransactionMaxLenBytes,
                               bool end_transaction = true) {
        return SPIWriteReadBlocking(nullptr, rx_buf, len_bytes, end_transaction);
    }

    SPICoprocessorConfig config_;
};

#ifdef ON_COPRO_MASTER
extern SPICoprocessor esp32;
extern SPICoprocessor cc1312;
#elif defined(ON_COPRO_SLAVE)
extern SPICoprocessor pico;
#endif

#endif /* SPI_COPROCESSOR_HH_ */