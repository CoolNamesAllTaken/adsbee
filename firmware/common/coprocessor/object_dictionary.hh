#ifndef OBJECT_DICTIONARY_HH_
#define OBJECT_DICTIONARY_HH_

#include "comms.hh"
#include "settings.hh"
#include "stdint.h"
#ifdef ON_ESP32
#include "adsbee_server.hh"
#include "esp_mac.h"   // For retrieving Base MAC address.
#include "esp_wifi.h"  // For retrieving WiFi Station MAC address.
#endif

class ObjectDictionary {
   public:
    static const uint8_t kFirmwareVersionMajor;
    static const uint8_t kFirmwareVersionMinor;
    static const uint8_t kFirmwareVersionPatch;
    static const uint32_t kFirmwareVersion;

    static const uint16_t kMACAddrLenBytes = 6;

    static const uint16_t kNetworkConsoleMessageMaxLenBytes = 4000;

    enum Address : uint8_t {
        kAddrInvalid = 0,                  // Default value.
        kAddrFirmwareVersion = 0x01,       // Firmware version as a uint32_t.
        kAddrScratch = 0x02,               // Used for testing SPI communications.
        kAddrSettingsData = 0x03,          // Used to transfer settings information.
        kAddrRawTransponderPacket = 0x04,  // Used to forward raw packets from RP2040 to ESP32.
        kAddrDecodedTransponderPacket = 0x05,
        kAddrRawTransponderPacketArray = 0x06,
        kAddrDecodedTransponderPacketArray = 0x07,
        kAddrAircraftDictionaryMetrics = 0x08,  // For forwarding dictionary metrics from RP2040 to ESP32.
        kAddrDeviceInfo = 0x09,                 // ESP32 MAC addresses.
        kAddrConsole = 0xA,                     // Pipe for console characters.
        kNumAddrs
    };

    struct ESP32DeviceInfo {
        uint8_t base_mac[kMACAddrLenBytes];
        uint8_t wifi_station_mac[kMACAddrLenBytes];
        uint8_t wifi_ap_mac[kMACAddrLenBytes];
        uint8_t bluetooth_mac[kMACAddrLenBytes];
        uint8_t ethernet_mac[kMACAddrLenBytes];
    };

    /**
     * Setter for writing data to the address space.
     * @param[in] addr Address to write to.
     * @param[in] buf Buffer to read from.
     * @param[in] buf_len Number of Bytes to write.
     * @param[in] offset Byte offset from beginning of object. Used for partial reads.
     * @retval Returns true if successfully wrote, false if address was invalid or something else borked.
     */
    bool SetBytes(Address addr, uint8_t *buf, uint16_t buf_len, uint16_t offset = 0);

    /**
     * Getter for reading data from the address space.
     * @param[in] addr Address to read from.
     * @param[out] buf Buffer to write to.
     * @param[in] buf_len Number of Bytes to read.
     * @param[in] offset Byte offset from beginning of object. Used for partial reads.
     * @retval Returns true if successfully read, false if address was invalid or something else borked.
     */
    bool GetBytes(Address addr, uint8_t *buf, uint16_t buf_len, uint16_t offset = 0);

   private:
    uint32_t scratch_ = 0x0;  // Scratch register used for testing.
};

extern ObjectDictionary object_dictionary;

#endif /* OBJECT_DICTIONARY_HH_ */
