#include "object_dictionary.hh"
#ifdef ON_ESP32
#include "device_info.hh"
#endif

#include "comms.hh"

const uint8_t ObjectDictionary::kFirmwareVersionMajor = 0;
const uint8_t ObjectDictionary::kFirmwareVersionMinor = 7;
const uint8_t ObjectDictionary::kFirmwareVersionPatch = 5;
// NOTE: Indicate a final release with RC = 0.
const uint8_t ObjectDictionary::kFirmwareVersionReleaseCandidate = 0;

const uint32_t ObjectDictionary::kFirmwareVersion = (kFirmwareVersionMajor << 24) | (kFirmwareVersionMinor << 16) |
                                                    (kFirmwareVersionPatch << 8) | kFirmwareVersionReleaseCandidate;

bool ObjectDictionary::SetBytes(Address addr, uint8_t *buf, uint16_t buf_len, uint16_t offset) {
    switch (addr) {
        case kAddrScratch:
            // Warning: printing here will cause a timeout and tests will fail.
            // CONSOLE_INFO("ObjectDictionary::SetBytes", "Setting %d settings Bytes at offset %d.", buf_len,
            // offset);
            memcpy((uint8_t *)&scratch_ + offset, buf, buf_len);
            break;
#ifdef ON_PICO
        case kAddrConsole:
            // ESP32 writing to the RP2040's network console interface.
            for (uint16_t i = 0; i < buf_len; i++) {
                char c = (char)buf[i];
                if (!comms_manager.esp32_console_rx_queue.Push(c)) {
                    CONSOLE_ERROR("ObjectDictionary::SetBytes", "ESP32 overflowed RP2040's network console queue.");
                    comms_manager.esp32_console_rx_queue.Clear();
                }
            }
            break;
#elif ON_ESP32
        case kAddrConsole: {
            // RP2040 writing to the ESP32's network console interface.
            char message[kNetworkConsoleMessageMaxLenBytes + 1] = {'\0'};
            strncpy(message, (char *)buf, buf_len);
            message[kNetworkConsoleMessageMaxLenBytes] = '\0';  // Null terminate for safety.
            CONSOLE_INFO("ObjectDictionary::SetBytes", "Forwarding message to network console: %s", message);
            adsbee_server.network_console.BroadcastMessage(message);
            break;
        }
        case kAddrRaw1090Packet: {
            Raw1090Packet tpacket;
            memcpy(&tpacket, buf, sizeof(Raw1090Packet));
            // Warning: printing here will cause a timeout and tests will fail.
            // CONSOLE_INFO("SPICoprocessor::SetBytes", "Received a raw %d-bit transponder packet.",
            //              tpacket.buffer_len_bits);
            adsbee_server.HandleRaw1090Packet(tpacket);
            break;
        }
        case kAddrRaw1090PacketArray: {
            uint8_t num_packets = buf[0];
            Raw1090Packet tpacket;
            for (uint16_t i = 0; i < num_packets && i * sizeof(Raw1090Packet) + sizeof(uint8_t) < buf_len; i++) {
                memcpy(&tpacket, buf + sizeof(uint8_t) + i * sizeof(Raw1090Packet), sizeof(Raw1090Packet));
                adsbee_server.HandleRaw1090Packet(tpacket);
            }
            break;
        }
        case kAddrAircraftDictionaryMetrics: {
            AircraftDictionary::Metrics rp2040_metrics;
            memcpy(&rp2040_metrics, buf + offset, buf_len);
            xQueueSend(adsbee_server.rp2040_aircraft_dictionary_metrics_queue, &rp2040_metrics, 0);
            break;
        }
#endif
        case kAddrSettingsData:
            // Warning: printing here will cause a timeout and tests will fail.
            // CONSOLE_INFO("ObjectDictionary::SetBytes", "Setting %d settings Bytes at offset %d.", buf_len,
            // offset);
            memcpy((uint8_t *)&(settings_manager.settings) + offset, buf, buf_len);
            if (offset + buf_len == sizeof(SettingsManager::Settings)) {
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

bool ObjectDictionary::GetBytes(Address addr, uint8_t *buf, uint16_t buf_len, uint16_t offset) {
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
#ifdef ON_ESP32
        case kAddrDeviceInfo: {
            ESP32DeviceInfo esp32_device_info = GetESP32DeviceInfo();
            memcpy(buf, &esp32_device_info + offset, buf_len);
            break;
        }
        case kAddrNetworkInfo: {
            ESP32NetworkInfo network_info = comms_manager.GetNetworkInfo();
            memcpy(buf, &network_info + offset, buf_len);
            break;
        }
#endif
        default:
            CONSOLE_ERROR("SPICoprocessor::SetBytes", "No behavior implemented for reading from address 0x%x.", addr);
            return false;
    }
    return true;
}