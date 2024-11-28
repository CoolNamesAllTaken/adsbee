
#ifdef ON_PICO
#include "RP2040.h"
#include "comms.hh"  // For errors.
#include "hal.hh"
#include "hardware/dma.h"  // for CRC32 calculation
#include "hardware/flash.h"
#include "hardware/sync.h"
#elif ON_ESP32
#include "stdint.h"
#endif

class FirmwareUpdateManager {
   public:
    /* Original flash length: 16384k Bytes.
    FLASH MAP
        0x10000000	(176k)	FLASH_BL	Bootloader
        0x1002C000	(4k)	FLASH_HDR0	Application 0 Header
        0x1002D000	(8096k)	FLASH_APP0	Application 0 Data
        0x10815000	(4k)	FLASH_HDR1	Application 1 Header
        0x10816000	(8096k)	FLASH_APP1	Application 1 Data
        0x10FFE000	(8k)	FLASH_EXTRA	Extra
    */

    static const uint32_t kFlashBlStartAddr = 0x10000000;
    static const uint32_t kFlashBlLenBytes = 176 * 1024;  // 176 kBytes
    static const uint16_t kNumPartitions = 2;  // Partition = header and application (not counting bootloader).
    static const uint32_t kFlashHeaderLenBytes = 4 * 1024;  // 4 kBytes
    static const uint32_t kFlashAppLenBytes = 8096 * 1024;  // 8096 kBytes

    static const uint32_t kFlashHeaderStartAddrs[kNumPartitions];
    static const uint32_t kFlashAppStartAddrs[kNumPartitions];

    static const uint32_t kFlashHeaderMagicWord = 0xAD5BEEE;
    static const uint32_t kFlashHeaderVersion = 0;

    // Leave some room in max length SPI packet (4096 Bytes) for other stuff.
    static const uint32_t kFlashWriteBufMaxLenBytes = 3840;

    // Set this value large enough to be efficient, but small enough that programs don't time out waiting for an update.
    static const uint16_t kMaxSectorsPerErase = 10 * FLASH_BLOCK_SIZE / FLASH_SECTOR_SIZE;

    static const uint16_t kFlashPartitionStatusStrMaxLen = 20;

    enum FlashPartitionStatus : uint32_t {
        kFlashPartitionStatusBlank = 0xFFFFFFFF,    // BLANK
        kFlashPartitionStatusValid = 0xFFADFFFF,    // VALID
        kFlashPartitionStatusStale = 0xDEADFFFF,    // STALE (Not the newest firmware, but OK to boot.)
        kFlashPartitionStatusInvalid = 0xDEADDEAD,  // INVALID (Do not boot.)
    };

    struct __attribute__((__packed__)) FlashPartitionHeader {
        uint32_t magic_word;
        uint32_t header_version;
        uint32_t app_size_bytes;
        uint32_t app_crc;
        uint32_t status;
    };

#ifdef ON_PICO
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
     * Boots to a given flash partition.
     * @param[in] partition Partition index to boot to. Must be less than kNumPartitions.
     */
    static inline void BootPartition(uint16_t partition) {
        if (partition >= kNumPartitions) {
            CONSOLE_ERROR("FirmwareUpdateManager::BootPartition",
                          "Can't boot partition %u, value must be less than %u.", partition, kNumPartitions);
            return;
        }

        // Check header magic word.
        uint32_t magic_word = flash_partition_headers[partition]->magic_word;
        if (magic_word != FirmwareUpdateManager::kFlashHeaderMagicWord) {
            CONSOLE_ERROR("FirmwareUpdateManager::BootPartition",
                          "Can't boot partition %u, header has invalid magic word 0x%x (expected 0x%x).", partition,
                          magic_word, FirmwareUpdateManager::kFlashHeaderMagicWord);
            return;
        }

        // Check header status.
        uint32_t status = flash_partition_headers[partition]->status;
        switch (status) {
            case kFlashPartitionStatusValid:
            case kFlashPartitionStatusStale:
                break;  // OK to boot these.
            case kFlashPartitionStatusInvalid:
            case kFlashPartitionStatusBlank:
            default:
                CONSOLE_ERROR("FirmwareUpdateManager::BootPartition", "Can't boot partition %u with status %u.",
                              partition, status);
                return;  // Not OK to boot these.
        }

        DisableInterruptsForJump();
        ResetPeripherals();
        JumpToVTOR(kFlashAppStartAddrs[partition]);
    }

    /**
     * Calculate a CRC-32 with the IEEE802.3 polynomial.
     */
    static inline uint32_t CalculateCRC32(const uint8_t *buffer, size_t len_bytes) {
        const uint32_t kSnifferMode = 0x1;  // Calculate a CRC-32 (IEEE802.3 polynomial) with bit reversed data
        // Good RP2040 CRC with DMA discussion: https://github.com/raspberrypi/pico-feedback/issues/247

        // Allocate a DMA channel.
        int dma_chan = dma_claim_unused_channel(true);  // Panic if no DMA channels are available.

        // Configure the DMA channel.
        dma_channel_config config = dma_channel_get_default_config(dma_chan);
        channel_config_set_transfer_data_size(&config, DMA_SIZE_8);  // 8-bit transfers
        channel_config_set_read_increment(&config, true);            // Increment source address
        channel_config_set_write_increment(&config, false);          // Fixed destination address
        // Set up the source and destination.
        uint32_t scratch;  // Write doesn't increment, just dump here since we aren't using it.
        dma_channel_configure(dma_chan, &config,
                              &scratch,   // Destination
                              buffer,     // Source (buffer to calculate CRC for)
                              len_bytes,  // Number of bytes to transfer
                              false);     // Don't start yet

        // Configure SNIFF hardware for CRC32.
        dma_sniffer_enable(dma_chan, kSnifferMode, true);                   // Enable SNIFF for the DMA channel
        hw_set_bits(&dma_hw->sniff_ctrl, DMA_SNIFF_CTRL_OUT_INV_BITS |      // Output inversion (for CRC32)
                                             DMA_SNIFF_CTRL_OUT_REV_BITS);  // Output reversal (for CRC32)

        // Clear sniff data register before starting.
        dma_hw->sniff_data = 0xFFFFFFFF;

        // Start the transfer.
        dma_channel_start(dma_chan);

        // Wait for the transfer to complete.
        dma_channel_wait_for_finish_blocking(dma_chan);

        // Retrieve the CRC value (invert it for CRC32 finalization).
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
        uint32_t bytes_to_erase = kFlashHeaderLenBytes + kFlashAppLenBytes;
        uint16_t total_sectors_to_erase =
            bytes_to_erase / FLASH_SECTOR_SIZE + (bytes_to_erase % FLASH_SECTOR_SIZE ? 1 : 0);
        uint16_t remaining_sectors_to_erase = total_sectors_to_erase;
        uint16_t num_sectors_to_erase;
        for (uint16_t sector = 0; remaining_sectors_to_erase > 0; sector += num_sectors_to_erase) {
            uint32_t sector_start_addr = kFlashHeaderStartAddrs[partition] + sector * FLASH_SECTOR_SIZE;
            num_sectors_to_erase = MIN(remaining_sectors_to_erase, kMaxSectorsPerErase);
            uint32_t num_bytes_to_erase = num_sectors_to_erase * FLASH_SECTOR_SIZE;
            CONSOLE_PRINTF("Erasing %u sector(s) starting at %u/%u (%u Bytes at 0x%x).\r\n", num_sectors_to_erase,
                           sector + 1, total_sectors_to_erase, num_bytes_to_erase * num_sectors_to_erase,
                           sector_start_addr);
            DisableInterrupts();
            flash_range_erase(FlashAddrToOffset(sector_start_addr), num_bytes_to_erase);
            RestoreInterrupts();
            remaining_sectors_to_erase -= num_sectors_to_erase;
        }
        return true;
    }

    /**
     * Converts from addresses in flash to flash offsets required by the Pico SDK flash functions.
     * @param[in] flash_addr Absolute address in flash.
     * @retval Offset from start of flash.
     */
    static inline uint32_t FlashAddrToOffset(uint32_t flash_addr) { return flash_addr - kFlashBlStartAddr; }

    /**
     * Converts flash partition status to a string.
     * @param[in] status Flash partition status.
     * @param[out] buf Buffer to write to. Must be at least kFlashPartitionStatusStrMaxLen long.
     */
    static inline void FlashPartitionStatusToStr(FlashPartitionStatus status, char *buf) {
        switch (status) {
            case kFlashPartitionStatusBlank:
                strncpy(buf, "BLANK", kFlashPartitionStatusStrMaxLen);
                break;
            case kFlashPartitionStatusInvalid:
                strncpy(buf, "INVALID", kFlashPartitionStatusStrMaxLen);
                break;
            case kFlashPartitionStatusStale:
                strncpy(buf, "STALE", kFlashPartitionStatusStrMaxLen);
                break;
            case kFlashPartitionStatusValid:
                strncpy(buf, "VALID", kFlashPartitionStatusStrMaxLen);
                break;
            default:
                strncpy(buf, "UNKNOWN", kFlashPartitionStatusStrMaxLen);
                break;
        }
    }

    /**
     * Returns the index of the other flash partition (e.g. the one we can safely operate on).
     * @retval Index of the flash aprtition that is currently not being executed from.
     */
    static inline uint16_t GetComplementaryFlashPartition() { return AmWithinFlashPartition(0) ? 1 : 0; }

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
                                                  const uint8_t *buf) {
        if (partition >= kNumPartitions) {
            CONSOLE_ERROR("FirmwareUpdateManager::PartialWriteFlashPartition",
                          "Can't write flash partition %u, value must be less than %u.", partition, kNumPartitions);
            return false;
        }
        if (offset > kFlashHeaderLenBytes + kFlashAppLenBytes) {
            CONSOLE_ERROR("FirmwareUpdateManager::PartialWriteFlashPartition",
                          "Offset %u is larger than maximum partition size %u Bytes.", offset,
                          kFlashHeaderLenBytes + kFlashAppLenBytes);
            return false;
        }
        if (len_bytes > kFlashHeaderLenBytes + kFlashAppLenBytes) {
            CONSOLE_ERROR("FirmwareUpdateManager::PartialWriteFlashPartition",
                          "Length %u is larger than maximum partition size %u Bytes.", len_bytes,
                          kFlashHeaderLenBytes + kFlashAppLenBytes);
            return false;
        }
        uint32_t padded_len_bytes = len_bytes + FLASH_PAGE_SIZE - (len_bytes % FLASH_PAGE_SIZE);
        DisableInterrupts();
        if (padded_len_bytes != len_bytes) {
            CONSOLE_WARNING("FirmwareUpdateManager::PartialWriteFlashPartition",
                            "Length %u is not a multiple of flash sector size %u Bytes.", len_bytes, FLASH_PAGE_SIZE);
            uint8_t padded_buf[padded_len_bytes];
            memcpy(padded_buf, buf, len_bytes);
            memset(padded_buf + len_bytes, 0xFF, padded_len_bytes - len_bytes);  // Pad the extra with 0xFF.

            flash_range_program(FlashAddrToOffset(kFlashHeaderStartAddrs[partition]) + offset, padded_buf,
                                padded_len_bytes);
        } else {
            // Buffer was already sector-aligned.
            flash_range_program(FlashAddrToOffset(kFlashHeaderStartAddrs[partition]) + offset, buf, len_bytes);
        }
        RestoreInterrupts();
        return true;
    }

    /**
     * Calculates the CRC32 of a flash partition and confirms it matches the CRC32 provided in the header.
     * @param[in] partition Index of partition to verify.
     * @param[in] modify_header True to modify the status word with the verification result, false to not touch it.
     */
    static inline bool VerifyFlashPartition(uint16_t partition, bool modify_header = false) {
        if (partition >= kNumPartitions) {
            CONSOLE_ERROR("FirmwareUpdateManager::VerifyFlashPartition",
                          "Can't verify flash partition %u, value must be less than %u.", partition, kNumPartitions);
            return false;
        }
        uint32_t header_crc = flash_partition_headers[partition]->app_crc;
        uint32_t len_bytes = flash_partition_headers[partition]->app_size_bytes;
        if (len_bytes > kFlashAppLenBytes) {
            CONSOLE_ERROR("FirmwareUpdateManager::VerifyFlashPartition",
                          "Flash partition %u is described by header as having %u Bytes, but maximum permissible size "
                          "is %u Bytes.",
                          partition, len_bytes, kFlashAppLenBytes);
            if (modify_header) {
                WriteHeaderStatusWord(partition, kFlashPartitionStatusInvalid);
            }
            return false;
        }
        uint32_t calculated_crc = CalculateCRC32(flash_partition_apps[partition], len_bytes);
        if (header_crc != calculated_crc) {
            CONSOLE_ERROR(
                "FirmwareUpdateManager::VerifyFlashPartition",
                "Flash partition %u (%d Bytes beginning at 0x%x) has calculated CRC 0x%x but header crc 0x%x.",
                partition, len_bytes, flash_partition_apps[partition], calculated_crc, header_crc);
            if (modify_header) {
                WriteHeaderStatusWord(partition, kFlashPartitionStatusInvalid);
            }
            return false;
        }

        // Verification passed: mark flash partition as valid.
        if (modify_header) {
            WriteHeaderStatusWord(partition, kFlashPartitionStatusValid);
        }
        return true;
    }

    static const FlashPartitionHeader *flash_partition_headers[kNumPartitions];
    static const uint8_t *flash_partition_apps[kNumPartitions];

   private:
    /**
     * Disable interrupts and store them for use in a restore command. Call this for TEMPORARILY disabling interrupts,
     * like during flash operations.
     */
    static inline void DisableInterrupts(void) { stored_interrupts_ = save_and_disable_interrupts(); }

    /**
     * Permanently disable interrupts, for use before jumping to a new application.
     */
    static inline void DisableInterruptsForJump(void) {
        SysTick->CTRL &= ~1;

        NVIC->ICER[0] = 0xFFFFFFFF;
        NVIC->ICPR[0] = 0xFFFFFFFF;
    }

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

    /**
     * Modifies the header status word of a flash partition header by re-writing the full header. Note that not all
     * values are possible for the status word, since bits can only be flipped from 1->0 and not the other way around,
     * without erasing the full sector.
     * @param[in] partition Index of the partition to modify the header of.
     * @param[in] status New status word to write.
     */
    static inline void WriteHeaderStatusWord(uint16_t partition, FlashPartitionStatus status) {
        FlashPartitionHeader header = *(flash_partition_headers[partition]);  // Copy the existing header.
        header.status = status;
        PartialWriteFlashPartition(partition, 0, sizeof(FlashPartitionHeader), (uint8_t *)&header);
    }

    static uint32_t stored_interrupts_;

#endif /* ON_PICO */
};
