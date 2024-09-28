#ifndef OBJECT_DICTIONARY_HH_
#define OBJECT_DICTIONARY_HH_

#include "comms.hh"
#include "settings.hh"
#include "stdint.h"
#ifdef ON_ESP32
#include "adsbee_server.hh"
#endif

class ObjectDictionary {
   public:
    static const uint8_t kFirmwareVersionMajor;
    static const uint8_t kFirmwareVersionMinor;
    static const uint8_t kFirmwareVersionPatch;
    static const uint32_t kFirmwareVersion;

    enum Address : uint8_t {
        kAddrInvalid = 0,             // Default value.
        kAddrFirmwareVersion = 0x01,  // Firmware version as a uint32_t.
        kAddrScratch,                 // Used for testing SPI communications.
        kAddrSettingsData,            // Used to transfer settings information.
        kAddrRawTransponderPacket,    // Used to forward raw packets from RP2040 to ESP32.
        kAddrDecodedTransponderPacket,
        kNumAddrs
    };

    /**
     * Setter for writing data to the address space.
     * @param[in] addr Address to write to.
     * @param[in] buf Buffer to read from.
     * @param[in] buf_len Number of Bytes to write.
     * @param[in] offset Byte offset from beginning of object. Used for partial reads.
     * @retval Returns true if successfully wrote, false if address was invalid or something else borked.
     */
    bool SetBytes(Address addr, uint8_t *buf, uint16_t buf_len, uint16_t offset = 0) {
        switch (addr) {
            case kAddrScratch:
                // Warning: printing here will cause a timeout and tests will fail.
                // CONSOLE_INFO("ObjectDictionary::SetBytes", "Setting %d settings Bytes at offset %d.", buf_len,
                // offset);
                memcpy((uint8_t *)&scratch_ + offset, buf, buf_len);
                break;
#ifdef ON_ESP32
            case kAddrRawTransponderPacket: {
                RawTransponderPacket tpacket = *(RawTransponderPacket *)buf;
                // Warning: printing here will cause a timeout and tests will fail.
                // CONSOLE_INFO("SPICoprocessor::SetBytes", "Received a raw %d-bit transponder packet.",
                //              tpacket.buffer_len_bits);
                adsbee_server.HandleRawTransponderPacket(tpacket);
                break;
            }
#endif
            case kAddrSettingsData:
                // Warning: printing here will cause a timeout and tests will fail.
                // CONSOLE_INFO("ObjectDictionary::SetBytes", "Setting %d settings Bytes at offset %d.", buf_len,
                // offset);
                memcpy((uint8_t *)&(settings_manager.settings) + offset, buf, buf_len);
                if (buf + buf_len == (uint8_t *)(&(settings_manager.settings)) + sizeof(SettingsManager::Settings)) {
                    CONSOLE_INFO("SPICoprocessor::SetBytes", "Wrote last chunk of settings data. Applying new values.");
                    settings_manager.Apply();
                    settings_manager.Print();
                }
                break;
            default:
                CONSOLE_ERROR("SPICoprocessor::SetBytes", "No behavior implemented for writing to address 0x%x.", addr);
                return false;
        }
        return true;
    }

    /**
     * Getter for reading data from the address space.
     @param[in] addr Address to read from.
     @param[out] buf Buffer to write to.
     @param[in] buf_len Number of Bytes to read.
     @param[in] offset Byte offset from beginning of object. Used for partial reads.
     @retval Returns true if successfully read, false if address was invalid or something else borked.
     */
    bool GetBytes(Address addr, uint8_t *buf, uint16_t buf_len, uint16_t offset = 0) {
        switch (addr) {
            case kAddrFirmwareVersion:
                memcpy(buf, (uint8_t *)(&kFirmwareVersion) + offset, buf_len);
                break;
            case kAddrScratch:
                // Warning: printing here will cause a timeout and tests will fail.
                // CONSOLE_INFO("ObjectDictionary::GetBytes", "Getting %d scratch Bytes at offset %d.", buf_len,
                // offset);
                memcpy(buf, (uint8_t *)(&scratch_) + offset, buf_len);
                break;
            case kAddrSettingsData:
                // Warning: printing here will cause a timeout and tests will fail.
                // CONSOLE_INFO("ObjectDictionary::GetBytes", "Getting %d settings Bytes at offset %d.", buf_len,
                // offset);
                memcpy(buf, (uint8_t *)&(settings_manager.settings) + offset, buf_len);
                break;
            default:
                CONSOLE_ERROR("SPICoprocessor::SetBytes", "No behavior implemented for reading from address 0x%x.",
                              addr);
                return false;
        }
        return true;
    }

   private:
    uint32_t scratch_ = 0x0;  // Scratch register used for testing.
};

extern ObjectDictionary object_dictionary;

#endif /* OBJECT_DICTIONARY_HH_ */
