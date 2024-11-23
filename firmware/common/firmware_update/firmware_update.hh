#include "RP2040.h"
#include "comms.hh"  // For errors.
#include "hal.hh"
#include "hardware/dma.h"  // for CRC32 calculation
#include "hardware/flash.h"
#include "hardware/sync.h"

class FirmwareUpdateManager {
   public:
    /* Original flash length: 16384k Bytes.
     FLASH MAP
         0x10000000	(176k)	FLASH_BL	Bootloader
         0x1002C000	(4k)	FLASH_HDR0	Application 0 Header
         0x1002D000	(8100k)	FLASH_APP0	Application 0 Data
         0x10816000	(4k)	FLASH_HDR1	Application 1 Header
         0x10817000	(8100k)	FLASH_APP1	Application 1 Data

     */

    static const uint32_t kFlashBlStartAddr = 0x10000000;
    static const uint32_t kFlashBlLenBytes = 176 * 1024;  // 176 kBytes
    static const uint16_t kNumPartitions = 2;  // Partition = header and application (not counting bootloader).
    static const uint32_t kFlashHeaderLenBytes = 4 * 1024;  // 4 kBytes
    static const uint32_t kFlashAppLenBytes = 8100 * 1024;  // 8100 kBytes

    static const uint32_t kFlashHeaderStartAddrs[kNumPartitions];
    static const uint32_t kFlashAppStartAddrs[kNumPartitions];

    static const uint32_t kFlashHeaderMagicWord = 0xAD5BEEE;
    static const uint32_t kFlashHeaderVersion = 0;

    enum FlashPartitionStatus : uint32_t {
        kFlashPartitionStatusBlank = 0xFFFFFFFF,   // Freshly erased.
        kFlashPartitionStatusNew = 0xFFADFFFF,     // Freshly flashed.
        kFlashPartitionStatusStale = 0xDEADFFFF,   // Not the newest firmware, but OK to boot.
        kFlashpartitionStatusInvalid = 0xDEADDEAD  // Do not boot.
    };

    struct __attribute__((__packed__)) FlashPartitionHeader {
        uint32_t magic_word;
        uint32_t header_version;
        uint32_t app_size_bytes;
        uint32_t app_crc;
        uint32_t status;
    };

    /**
     * Boots to a given flash partition.
     * @param[in] partition Partition index to boot to. Must be less than kNumPartitions.
     */
    static inline void BootPartition(uint16_t partition) {
        if (partition >= kNumPartitions) {
            CONSOLE_ERROR("FirmwareUpdateManager::BootPartition",
                          "Can't boot partition %u, value must be less than %u.", partition, kNumPartitions);
            return;
        }
        DisableInterrupts();
        ResetPeripherals();
        JumpToVTOR(kFlashAppStartAddrs[partition]);
    }

    /**
     * Calculate a CRC-32 with the IEEE802.3 polynomial.
     */
    static inline uint32_t CalculateCRC32(const uint8_t *buffer, size_t len_bytes) {
        const uint32_t kSnifferMode = 0x1;  // Calculate a CRC-32 (IEEE802.3 polynomial) with bit reversed data
        // Good RP2040 CRC with DMA discussion: https://github.com/raspberrypi/pico-feedback/issues/247

        // Allocate a DMA channel
        int dma_chan = dma_claim_unused_channel(true);  // Panic if no DMA channels are available.

        // Configure the DMA channel
        dma_channel_config config = dma_channel_get_default_config(dma_chan);
        channel_config_set_transfer_data_size(&config, DMA_SIZE_32);  // 32-bit transfers
        channel_config_set_read_increment(&config, true);             // Increment source address
        channel_config_set_write_increment(&config, false);           // Fixed destination address
        // Set up the source and destination
        uint32_t scratch;  // Write doesn't increment, just dump here since we aren't using it.
        uint32_t len_words = len_bytes / kBytesPerWord + (len_bytes % kBytesPerWord ? 1 : 0);
        dma_channel_configure(dma_chan, &config,
                              &scratch,   // Destination
                              buffer,     // Source (buffer to calculate CRC for)
                              len_words,  // Number of bytes to transfer
                              false);     // Don't start yet

        // Configure SNIFF hardware for CRC32
        dma_sniffer_enable(dma_chan, kSnifferMode, true);                   // Enable SNIFF for the DMA channel
        hw_set_bits(&dma_hw->sniff_ctrl, DMA_SNIFF_CTRL_OUT_INV_BITS |      // Output inversion (for CRC32)
                                             DMA_SNIFF_CTRL_OUT_REV_BITS);  // Output reversal (for CRC32)

        // Clear sniff data register before starting
        dma_hw->sniff_data = 0xFFFFFFFF;

        // Start the transfer
        dma_channel_start(dma_chan);

        // Wait for the transfer to complete
        dma_channel_wait_for_finish_blocking(dma_chan);

        // Retrieve the CRC value (invert it for CRC32 finalization)
        // uint32_t crc = ~dma_hw->sniff_data;
        volatile uint32_t crc = dma_hw->sniff_data;

        // Clean up
        dma_sniffer_disable();
        dma_channel_unclaim(dma_chan);

        return crc;
    }

    /**
     * Erase all contents of a flash partition, including the header and application.
     * @param[in] partition Partition index to erase. Must be < kNumPartitions.
     */
    static inline bool EraseFlashParition(uint16_t partition) {
        if (partition >= kNumPartitions) {
            CONSOLE_ERROR("FirmwareUpdateManager::EraseFlashPartition",
                          "Can't erase partition %u, value must be less than %u.", partition, kNumPartitions);
            return false;
        }
        DisableInterrupts();
        flash_range_erase(kFlashHeaderStartAddrs[partition], kFlashHeaderLenBytes + kFlashAppLenBytes);
        RestoreInterrupts();
    }

    /**
     * Checks whether the program counter is currently within the specified flash partition.
     * @param[in] partition Partition index. Must be < kNumPartitions
     * @retval True if within partition, false if not or partition does not exist.
     */
    static inline bool AmWithinFlashPartition(uint16_t partition) {
        if (partition >= kNumPartitions) {
            CONSOLE_ERROR("FirmwareUpdateManager::AmWithinFlashPartition",
                          "Can't check if within partition %u, value must be less than %u.", partition, kNumPartitions);
            return false;
        }
        uint32_t pc_addr = (uint32_t)__builtin_return_address(0);
        if (pc_addr >= kFlashAppStartAddrs[partition] && pc_addr < kFlashAppStartAddrs[partition] + kFlashAppLenBytes) {
            return true;
        }
        return false;
    }

    /**
     * Read Bytes from a flash partition starting at offset bytes from the beginning, and copy them to the provided
     * buffer.
     * @param[in] partition Partition index. Must be < kNumPartitions.
     * @param[in] offset Address offset within partition.
     * @param[in] len_bytes Length of partition contents starting at offset to read into buf.
     * @param[out] buf Buffer to write to. Must be at lest len_bytes long.
     * @retval True if bytes read successfully, false if error.
     */
    static inline bool PartialReadFlashPartition(uint16_t partition, uint32_t offset, uint32_t len_bytes,
                                                 uint8_t *buf) {}

    /**
     * Write to a section of a flash partition. Note that the section of flash to be written must be erased first.
     * @param[in] partition Partition index. Must be < kNumPartitions.
     * @param[in] offset Address offset within partition.
     * @param[in] len_bytes Length of buffer to flash into the partition beginning at offset.
     * @param[in] buf Buffer to read from. Must be at least len_bytes long.
     * @retval True if bytes written successfully, false if error.
     */
    static inline bool PartialWriteFlashPartition(uint16_t partition, uint32_t offset, uint32_t len_bytes,
                                                  const uint8_t *buf) {}

    /**
     * Calculates the CRC32 of a flash partition and confirms it matches the CRC32 provided in the header.
     */
    static inline bool VerifyFlashPartition(uint16_t partition) {
        if (partition >= kNumPartitions) {
            CONSOLE_ERROR("FirmwareUpdateManager::VerifyFlashPartition",
                          "Can't verify flash partition %u, value must be less than %u.", partition, kNumPartitions);
            return false;
        }
        uint32_t header_crc = flash_partition_headers[partition]->app_crc;
        uint32_t calculated_crc =
            CalculateCRC32(flash_partition_apps[partition],
                           MIN(flash_partition_headers[partition]->app_size_bytes, kFlashAppLenBytes));
        if (header_crc != calculated_crc) {
            CONSOLE_ERROR("FirmwareUpdateManager::VerifyFlashPartition",
                          "Flash partition %u has calculated CRC 0x%x but header crc 0x%x.", partition, calculated_crc,
                          header_crc);
            return false;
        }
        return true;
    }

    static const FlashPartitionHeader *flash_partition_headers[kNumPartitions];
    static const uint8_t *flash_partition_apps[kNumPartitions];

   private:
    /**
     * Disable interrupts and store them for use in a restore command. Call this before erasing flash or performing
     * boot jumps.
     */
    static inline void DisableInterrupts(void) { stored_interrupts_ = save_and_disable_interrupts(); }

    /**
     * Jumps to an address in XIP flash.
     * @param[in] vtor Address to jump to. Should be set to the beginning of a flash application sector (not a
     * header).
     */
    static inline void JumpToVTOR(uint32_t vtor) {
        // Derived from the Leaf Labs Cortex-M3 bootloader.
        // Copyright (c) 2010 LeafLabs LLC.
        // Modified 2021 Brian Starkey <stark3y@gmail.com>
        // Originally under The MIT License
        uint32_t reset_vector = *(volatile uint32_t *)(vtor + 0x04);

        SCB->VTOR = (volatile uint32_t)(vtor);

        asm volatile("msr msp, %0" ::"g"(*(volatile uint32_t *)vtor));
        asm volatile("bx %0" ::"r"(reset_vector));
    }

    /**
     * Reset peripherals so we don't end up "zombie peripherals" after the jump.
     */
    static inline void ResetPeripherals(void) {
        reset_block(~(RESETS_RESET_IO_QSPI_BITS | RESETS_RESET_PADS_QSPI_BITS | RESETS_RESET_SYSCFG_BITS |
                      RESETS_RESET_PLL_SYS_BITS));
    }

    /**
     * Restore interrupts from stored values. Call this after erasing flash or performing a boot jump.
     */
    static inline void RestoreInterrupts(void) { restore_interrupts(stored_interrupts_); }

    static uint32_t stored_interrupts_;
};