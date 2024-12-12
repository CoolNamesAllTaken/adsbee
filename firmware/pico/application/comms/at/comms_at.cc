#include <stdio.h>  // for printing

#include <cstring>   // for strcat
#include <iostream>  // for AT command ingestion

#include "adsbee.hh"
#include "comms.hh"
#include "eeprom.hh"
#include "esp32_flasher.hh"
#include "firmware_update.hh"
#include "main.hh"
#include "pico/stdlib.h"  // for getchar etc
#include "settings.hh"
#include "spi_coprocessor.hh"  // For init / de-init before and after flashing ESP32.

#ifdef HARDWARE_UNIT_TESTS
#include "hardware_unit_tests.hh"
#endif

// For mapping cpp_at_printf
#include <cstdarg>
// #include "printf.h" // for using custom printf defined in printf.h
#include <cstdio>  // for using regular printf

// This is intended to stop people from accidentally modifying serial number information on their device.
const uint32_t kDeviceInfoProgrammingPassword = 0xDEDBEEF;
// Polling interval during OTA update. Faster than the normal ESP32 heartbeat for better transfer bandwidth.
// Heartbeat is required since the ESP32 firmware won't hand off the SPI mutex until it gets poked, so it needs a
// heartbeat between each message (no ACK required).
const uint32_t kOTAHeartbeatMs = 10;

/** CppAT Printf Override **/
int CppAT::cpp_at_printf(const char *format, ...) {
    va_list args;
    va_start(args, format);
    int ret = comms_manager.iface_vprintf(SettingsManager::SerialInterface::kConsole, format, args);
    va_end(args);

    return ret;
}

/** AT Command Callback Functions **/

CPP_AT_CALLBACK(CommsManager::ATBaudrateCallback) {
    switch (op) {
        case '?':
            CPP_AT_CMD_PRINTF("=%d(COMMS_UART),%d(GNSS_UART)", comms_uart_baudrate_, gnss_uart_baudrate_);
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            if (!(CPP_AT_HAS_ARG(0) && CPP_AT_HAS_ARG(1))) {
                CPP_AT_ERROR(
                    "Requires two arguments: AT+BAUDRATE=<iface>,<baudrate> where <iface> can be one of [COMMS_UART, "
                    "GNSS_UART].");
            }
            SettingsManager::SerialInterface iface;
            if (args[0].compare("COMMS_UART") == 0) {
                iface = SettingsManager::kCommsUART;
            } else if (args[0].compare("GNSS_UART") == 0) {
                iface = SettingsManager::kGNSSUART;
            } else {
                CPP_AT_ERROR("Invalid interface. Must be one of [COMMS_UART, GNSS_UART].");
            }
            uint32_t baudrate;
            CPP_AT_TRY_ARG2NUM(1, baudrate);
            if (!SetBaudrate(iface, baudrate)) {
                CPP_AT_ERROR("Unable to set baudrate %d on interface %d.", baudrate, iface);
            }
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATBiasTeeEnableCallback) {
    switch (op) {
        case '?':
            CPP_AT_CMD_PRINTF("=%d", adsbee.BiasTeeIsEnabled());
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            if (!(CPP_AT_HAS_ARG(0))) {
                CPP_AT_ERROR("Requires an argument (0 or 1). AT+BIAS_TEE_ENABLED=<enabled>");
            }
            bool enabled;
            CPP_AT_TRY_ARG2NUM(0, enabled);
            adsbee.SetBiasTeeEnable(enabled);
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATESP32EnableCallback) {
    switch (op) {
        case '?':
            CPP_AT_CMD_PRINTF("=%d", esp32.IsEnabled());
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Requires an argument (0 or 1). AT+ESP32_ENABLED=<enabled>");
            }
            bool enabled;
            bool already_enabled = esp32.IsEnabled();
            CPP_AT_TRY_ARG2NUM(0, enabled);
            if (enabled && !already_enabled) {
                esp32.Init();
            } else if (!enabled && already_enabled) {
                esp32.DeInit();
            }
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATDeviceInfoCallback) {
    switch (op) {
        case '?': {
            SettingsManager::DeviceInfo device_info;
            if (!settings_manager.GetDeviceInfo(device_info)) {
                CPP_AT_ERROR("Error while retrieving device info.");
            }
            device_info.part_code[SettingsManager::DeviceInfo::kPartCodeLen] =
                '\0';  // Use caution in case part code is invalid.
            CPP_AT_PRINTF("Part Code: %s\r\n", device_info.part_code);
            CPP_AT_PRINTF("RP2040 Firmware Version: %d.%d.%d\r\n", object_dictionary.kFirmwareVersionMajor,
                          object_dictionary.kFirmwareVersionMinor, object_dictionary.kFirmwareVersionPatch);
            for (uint16_t i = 0; i < SettingsManager::DeviceInfo::kNumOTAKeys; i++) {
                CPP_AT_PRINTF("OTA Key %d: %s\r\n", i, device_info.ota_keys[i]);
            }

            if (esp32.IsEnabled()) {
                // Read ESP32 firmware verison.
                uint32_t esp32_firmware_version;
                if (!esp32.Read(ObjectDictionary::kAddrFirmwareVersion, esp32_firmware_version)) {
                    CPP_AT_ERROR("ESP32 firmware version read failed!");
                }
                CPP_AT_PRINTF("ESP32 Firmware Version: %d.%d.%d\r\n", esp32_firmware_version >> 16,
                              (esp32_firmware_version >> 8) & 0xFF, esp32_firmware_version & 0xFF);

                ObjectDictionary::ESP32DeviceInfo esp32_device_info;
                if (!esp32.Read(ObjectDictionary::kAddrDeviceInfo, esp32_device_info, sizeof(esp32_device_info))) {
                    CPP_AT_ERROR("ESP32 device info read failed!");
                }
                CPP_AT_PRINTF("ESP32 Base MAC Address: %02X:%02X:%02X:%02X:%02X:%02X\r\n",
                              esp32_device_info.base_mac[0], esp32_device_info.base_mac[1],
                              esp32_device_info.base_mac[2], esp32_device_info.base_mac[3],
                              esp32_device_info.base_mac[4], esp32_device_info.base_mac[5]);
                CPP_AT_PRINTF("ESP32 WiFi Station MAC Address: %02X:%02X:%02X:%02X:%02X:%02X\r\n",
                              esp32_device_info.wifi_station_mac[0], esp32_device_info.wifi_station_mac[1],
                              esp32_device_info.wifi_station_mac[2], esp32_device_info.wifi_station_mac[3],
                              esp32_device_info.wifi_station_mac[4], esp32_device_info.wifi_station_mac[5]);
                CPP_AT_PRINTF("ESP32 WiFi AP MAC Address: %02X:%02X:%02X:%02X:%02X:%02X\r\n",
                              esp32_device_info.wifi_ap_mac[0], esp32_device_info.wifi_ap_mac[1],
                              esp32_device_info.wifi_ap_mac[2], esp32_device_info.wifi_ap_mac[3],
                              esp32_device_info.wifi_ap_mac[4], esp32_device_info.wifi_ap_mac[5]);
                CPP_AT_PRINTF("ESP32 Bluetooth MAC Address: %02X:%02X:%02X:%02X:%02X:%02X\r\n",
                              esp32_device_info.bluetooth_mac[0], esp32_device_info.bluetooth_mac[1],
                              esp32_device_info.bluetooth_mac[2], esp32_device_info.bluetooth_mac[3],
                              esp32_device_info.bluetooth_mac[4], esp32_device_info.bluetooth_mac[5]);
                CPP_AT_PRINTF("ESP32 Ethernet MAC Address: %02X:%02X:%02X:%02X:%02X:%02X\r\n",
                              esp32_device_info.ethernet_mac[0], esp32_device_info.ethernet_mac[1],
                              esp32_device_info.ethernet_mac[2], esp32_device_info.ethernet_mac[3],
                              esp32_device_info.ethernet_mac[4], esp32_device_info.ethernet_mac[5]);
            } else {
                CPP_AT_PRINTF("ESP32 Disabled\r\n");
            }

            CPP_AT_SILENT_SUCCESS();
            break;
        }
        case '=': {
            // AT+DEVICE_INFO=<programming_password>,<device_info_version>,<part_code>,<ota_key_0>,<ota_key_1>
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Missing programming password.");
            } else {
                uint32_t programming_password;
                CPP_AT_TRY_ARG2NUM_BASE(0, programming_password, 16);
                if (programming_password != kDeviceInfoProgrammingPassword) {
                    CPP_AT_ERROR("Programming password 0x%x does not match.", programming_password);
                }
                // Program device information here.
                SettingsManager::DeviceInfo device_info;

                if (CPP_AT_HAS_ARG(1)) {
                    uint16_t device_info_version;
                    CPP_AT_TRY_ARG2NUM(1, device_info_version);
                    if (device_info_version != kDeviceInfoVersion) {
                        CPP_AT_ERROR("Device info version must be %d, got %d.", device_info_version,
                                     kDeviceInfoVersion);
                    }
                    if (device_info_version == device_info.device_info_version) {
                        // Existing device info is compatible, use existing DeviceInfo struct as a starter.
                        settings_manager.GetDeviceInfo(device_info);
                    }
                }
                // Else (no argument provided for device info), use default values for everything.
                if (CPP_AT_HAS_ARG(2)) {
                    // Copy part code while guarding against part codes that are too long.
                    strncpy(device_info.part_code, args[2].data(), SettingsManager::DeviceInfo::kPartCodeLen);
                    device_info.part_code[SettingsManager::DeviceInfo::kPartCodeLen] = '\0';
                }
                for (uint16_t i = 0; i < SettingsManager::DeviceInfo::kNumOTAKeys; i++) {
                    uint16_t arg_index = i + 3;
                    if (CPP_AT_HAS_ARG(arg_index)) {
                        // Set OTA key 0.
                        strncpy(device_info.ota_keys[i], args[arg_index].data(),
                                SettingsManager::DeviceInfo::kOTAKeyMaxLen);
                        device_info.ota_keys[i][SettingsManager::DeviceInfo::kOTAKeyMaxLen] = '\0';
                    }
                }
                if (settings_manager.SetDeviceInfo(device_info)) {
                    CPP_AT_SUCCESS();
                }
                CPP_AT_ERROR("Error while attempting to set device info.");
            }
            break;
        }
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATEthernetCallback) {
    switch (op) {
        case '?':
            CPP_AT_CMD_PRINTF("=%d", settings_manager.settings.ethernet_enabled);
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Requires an argument (0 or 1). AT+ETHERNET_ENABLED=<enabled>");
            }
            bool enabled;
            CPP_AT_TRY_ARG2NUM(0, settings_manager.settings.ethernet_enabled);
            CPP_AT_CMD_PRINTF(": ethernet_enabled: %d\r\n", settings_manager.settings.ethernet_enabled);
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

void ATFeedHelpCallback() {
    CPP_AT_PRINTF(
        "\tAT+FEED=<index>,<uri>,<port>,<active>,<protocol>\r\n\tSet details for a "
        "network feed.\r\n\tindex = [0-%d], uri = ip address or URL, feed_port = [0-65535], "
        "active = [0 1], protocol = [BEAST BEAST_RAW].\r\n\t\r\n\tAT+FEED?\r\n\tPrint details for all "
        "feeds.\r\n\t\r\n\tAT+FEED?<index>\r\n\tPrint details for a specific feed.\r\n\tfeed_index = [0-%d]",
        SettingsManager::Settings::kMaxNumFeeds - 1, SettingsManager::Settings::kMaxNumFeeds - 1);
}

CPP_AT_CALLBACK(CommsManager::ATFeedCallback) {
    switch (op) {
        case '?':
            if (CPP_AT_HAS_ARG(0)) {
                // Querying info about a specific feed.
                uint16_t index = UINT16_MAX;
                CPP_AT_TRY_ARG2NUM(0, index);
                if (index >= SettingsManager::Settings::kMaxNumFeeds) {
                    CPP_AT_ERROR("Feed number must be between 0-%d, no details for feed with index %d.",
                                 SettingsManager::Settings::kMaxNumFeeds - 1, index);
                }
                char receiver_id_str[SettingsManager::Settings::kFeedReceiverIDNumBytes * 2 + 1];
                SettingsManager::ReceiverIDToStr(settings_manager.settings.feed_receiver_ids[index], receiver_id_str);
                CPP_AT_CMD_PRINTF(
                    "=%d(INDEX),%s(URI),%d(PORT),%d(ACTIVE),%s(PROTOCOL),%s(RECEIVER_ID)", index,
                    settings_manager.settings.feed_uris[index], settings_manager.settings.feed_ports[index],
                    settings_manager.settings.feed_is_active[index],
                    SettingsManager::kReportingProtocolStrs[settings_manager.settings.feed_protocols[index]],
                    receiver_id_str);
            } else {
                // Querying info about all feeds.
                for (uint16_t i = 0; i < SettingsManager::Settings::kMaxNumFeeds; i++) {
                    char receiver_id_str[SettingsManager::Settings::kFeedReceiverIDNumBytes * 2 + 1];
                    SettingsManager::ReceiverIDToStr(settings_manager.settings.feed_receiver_ids[i], receiver_id_str);
                    CPP_AT_CMD_PRINTF(
                        "=%d(INDEX),%s(URI),%d(PORT),%d(ACTIVE),%s(PROTOCOL),%s(RECEIVER_ID)", i,
                        settings_manager.settings.feed_uris[i], settings_manager.settings.feed_ports[i],
                        settings_manager.settings.feed_is_active[i],
                        SettingsManager::kReportingProtocolStrs[settings_manager.settings.feed_protocols[i]],
                        receiver_id_str);
                }
            }
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // Setting feed information for a specific feed.
            uint16_t index = UINT16_MAX;
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Feed index is required for setting feed information.");
            }
            CPP_AT_TRY_ARG2NUM(0, index);
            if (index >= SettingsManager::Settings::kMaxNumFeeds) {
                CPP_AT_ERROR("Feed index must be between 0-%d, no details for feed with index %d.",
                             SettingsManager::Settings::kMaxNumFeeds - 1, index);
            }
            // Set FEED_URI.
            if (CPP_AT_HAS_ARG(1)) {
                strncpy(settings_manager.settings.feed_uris[index], args[1].data(),
                        SettingsManager::Settings::kFeedURIMaxNumChars);
                settings_manager.settings.feed_uris[index][SettingsManager::Settings::kFeedURIMaxNumChars] = '\0';
            }
            // Set FEED_PORT
            if (CPP_AT_HAS_ARG(2)) {
                CPP_AT_TRY_ARG2NUM(2, settings_manager.settings.feed_ports[index]);
            }
            // Set ACTIVE
            if (CPP_AT_HAS_ARG(3)) {
                uint8_t is_active;
                CPP_AT_TRY_ARG2NUM(3, settings_manager.settings.feed_is_active[index]);
            }
            // Set PROTOCOL
            if (CPP_AT_HAS_ARG(4)) {
                SettingsManager::ReportingProtocol feed_protocol;
                for (uint16_t i = 0; i < SettingsManager::ReportingProtocol::kNumProtocols; i++) {
                    if (args[4].compare(SettingsManager::kReportingProtocolStrs[i]) == 0) {
                        feed_protocol = static_cast<SettingsManager::ReportingProtocol>(i);
                    }
                }
                // Check that the selected prototcol is valid for use with feeders.
                if (!(feed_protocol == SettingsManager::ReportingProtocol::kBeast ||
                      feed_protocol == SettingsManager::ReportingProtocol::kNoReports)) {
                    CPP_AT_ERROR("Protocol %s is not supported for network feeds.",
                                 SettingsManager::kReportingProtocolStrs[feed_protocol]);
                }
                settings_manager.settings.feed_protocols[index] = feed_protocol;
            }
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATFlashESP32Callback) {
    if (!esp32.DeInit()) {
        CPP_AT_ERROR("CommsManager::ATFlashESP32Callback", "Error while de-initializing ESP32 before flashing.");
    }
    adsbee.DisableWatchdog();
    bool flashed_successfully = esp32_flasher.FlashESP32();
    adsbee.EnableWatchdog();
    if (!flashed_successfully) {
        CPP_AT_ERROR("CommsManager::ATFlashESP32Callback", "Error while flashing ESP32.");
    }

    if (!esp32.Init()) {
        CPP_AT_ERROR("CommsManager::ATFlashESP32Callback", "Error while re-initializing ESP32 after flashing.");
    }

    CONSOLE_INFO("CommsManager::ATFlashESP32Callback", "ESP32 successfully flashed.");
    CPP_AT_SUCCESS();
}

CPP_AT_CALLBACK(CommsManager::ATHostnameCallback) {
    switch (op) {
        case '?':
            CPP_AT_CMD_PRINTF("=%s", settings_manager.settings.hostname);
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Requires an argument. AT+HOSTNAME=<hostname>");
            }
            strncpy(settings_manager.settings.hostname, args[0].data(), SettingsManager::Settings::kHostnameMaxLen);
            settings_manager.settings.hostname[SettingsManager::Settings::kHostnameMaxLen] = '\0';
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATOTACallback) {
    switch (op) {
        case '?':
            CPP_AT_PRINTF("Flash Partition Information\r\n");
            for (uint16_t partition = 0; partition < FirmwareUpdateManager::kNumPartitions; partition++) {
                CPP_AT_PRINTF("\tPartition %u %s\r\n", partition,
                              FirmwareUpdateManager::AmWithinFlashPartition(partition) ? "(ACTIVE)" : "");
                if (FirmwareUpdateManager::flash_partition_headers[partition]->magic_word !=
                    FirmwareUpdateManager::kFlashHeaderMagicWord) {
                    CPP_AT_PRINTF("\t\tNO VALID HEADER\r\n");
                    continue;
                }
                CPP_AT_PRINTF("\t\tLength: %u Bytes\r\n",
                              FirmwareUpdateManager::flash_partition_headers[partition]->app_size_bytes);
                CPP_AT_PRINTF("\t\tApplication CRC: 0x%x\r\n",
                              FirmwareUpdateManager::flash_partition_headers[partition]->app_crc);
                char status_str[FirmwareUpdateManager::kFlashPartitionStatusStrMaxLen];
                FirmwareUpdateManager::FlashPartitionStatusToStr(
                    (FirmwareUpdateManager::FlashPartitionStatus)
                        FirmwareUpdateManager::flash_partition_headers[partition]
                            ->status,
                    status_str);
                CPP_AT_PRINTF("\t\tStatus: %s (0x%x)\r\n", status_str,
                              FirmwareUpdateManager::flash_partition_headers[partition]->status);
                CPP_AT_PRINTF("\t\tSector %s verification.\r\n",
                              FirmwareUpdateManager::VerifyFlashPartition(partition, false) ? "PASSED" : "FAILED");
            }
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            if (CPP_AT_HAS_ARG(0)) {
                uint16_t complementary_partition = FirmwareUpdateManager::GetComplementaryFlashPartition();
                if (args[0].compare("ERASE") == 0) {
                    // Erase the complementary flash partition.
                    CPP_AT_PRINTF("Erasing partition %d.\r\n", complementary_partition);
                    // Flash erase can take a while, prevent watchdog from rebooting us during erase!
                    adsbee.DisableWatchdog();
                    bool flash_erase_succeeded = FirmwareUpdateManager::EraseFlashParition(complementary_partition);
                    adsbee.EnableWatchdog();
                    if (!flash_erase_succeeded) {
                        CPP_AT_ERROR("Failed to erase complmentary flash partition.");
                    }
                    CPP_AT_SUCCESS();
                } else if (args[0].compare("GET_PARTITION") == 0) {
                    // Reply with the complementary flash partition number. This is used to select the correct flash
                    // partition from the OTA file.
                    CPP_AT_PRINTF("Partition: %u\r\n", complementary_partition);
                    CPP_AT_SUCCESS();
                } else if (args[0].compare("WRITE") == 0) {
                    // Write a section of the complementary flash partition.
                    // AT+OTA=WRITE,<offset (base 16)>,<len_bytes (base 10)>,<crc (base 16)>
                    adsbee.SetReceiverEnable(0);  // Stop ADSB packets from mucking up the SPI bus.
                    uint32_t offset, len_bytes, crc;
                    CPP_AT_TRY_ARG2NUM_BASE(1, offset, 16);
                    CPP_AT_TRY_ARG2NUM_BASE(2, len_bytes, 10);
                    if (len_bytes > FirmwareUpdateManager::kFlashWriteBufMaxLenBytes) {
                        adsbee.SetReceiverEnable(1);  // Re-enable receiver before exit.
                        CPP_AT_ERROR("Write length %u exceeds maximum %u Bytes.", len_bytes,
                                     FirmwareUpdateManager::kFlashWriteBufMaxLenBytes);
                    }
                    uint8_t buf[len_bytes];
                    uint32_t buf_len_bytes = 0;
                    uint32_t timestamp_ms = get_time_since_boot_ms();
                    uint32_t data_read_start_timestamp_ms = timestamp_ms;
                    uint32_t last_ota_heartbeat_timestamp_ms = timestamp_ms;
                    // Read len_bytes from stdio and network console. Timeout after kOTAWriteTimeoutMs.
                    while (buf_len_bytes < len_bytes) {
                        // Priority 1: Check STDIO for data.
                        int stdio_console_getchar_reply = getchar_timeout_us(0);
                        if (stdio_console_getchar_reply >= 0) {
                            // Didn't have timeout or other error: got a valid data byte.
                            buf[buf_len_bytes] = static_cast<char>(stdio_console_getchar_reply);
                            buf_len_bytes++;
                            continue;  // Don't check network console if stdio had a byte.
                        }

                        // Priority 2: Check network console for data.
                        if (esp32.IsEnabled()) {
                            char network_console_byte;
                            if (esp32_console_rx_queue.Length() > 0) {
                                while (buf_len_bytes < len_bytes && esp32_console_rx_queue.Pop(network_console_byte)) {
                                    // Was able to read a char from the network buffer.
                                    buf[buf_len_bytes] = network_console_byte;
                                    buf_len_bytes++;
                                }
                            } else {
                                // Didn't receive any Bytes. Refresh network console and update timeout timestamp.
                                // esp32.Update();
                                // Poll the ESP32 by sending a heartbeat message (no ACK required) get the ESP32
                                // firmware to release the SPI mutex to the task that's forwarding data from the network
                                // console.
                                timestamp_ms = get_time_since_boot_ms();
                                if (timestamp_ms - last_ota_heartbeat_timestamp_ms > kOTAHeartbeatMs) {
                                    // Don't call update manually here, it gets taken care of in the Write function.
                                    // Calling Update twice will result in the network console buffer overflowing if two
                                    // blobs of characters are ready to be transmitted sequentially!
                                    esp32.Write(ObjectDictionary::kAddrScratch, timestamp_ms, false);
                                    last_ota_heartbeat_timestamp_ms = timestamp_ms;
                                }
                            }
                        }

                        timestamp_ms = get_time_since_boot_ms();
                        if (timestamp_ms - data_read_start_timestamp_ms > kOTAWriteTimeoutMs) {
                            adsbee.SetReceiverEnable(1);  // Re-enable receiver before exit.
                            CPP_AT_ERROR("Timed out after %u ms. Received %u Bytes.",
                                         timestamp_ms - data_read_start_timestamp_ms, buf_len_bytes);
                        }
                    }
                    CPP_AT_PRINTF("Writing %u Bytes to partition %u at offset 0x%x.\r\n", len_bytes,
                                  complementary_partition, offset);
                    adsbee.DisableWatchdog();  // Flash write can take a while, prevent watchdog from rebooting us
                    // during write!
                    bool flash_write_succeeded = FirmwareUpdateManager::PartialWriteFlashPartition(
                        complementary_partition, offset, len_bytes, buf);
                    adsbee.EnableWatchdog();
                    if (!flash_write_succeeded) {
                        adsbee.SetReceiverEnable(1);  // Re-enable receiver before exit.
                        CPP_AT_ERROR("Partial %u Byte write failed in partition %u at offset 0x%x.", len_bytes,
                                     complementary_partition, offset);
                    }
                    if (CPP_AT_HAS_ARG(3)) {
                        // CRC provided.
                        CPP_AT_TRY_ARG2NUM_BASE(3, crc, 16);
                        CPP_AT_PRINTF("Verifying with CRC 0x%x.\r\n", crc);
                        uint32_t calculated_crc = FirmwareUpdateManager::CalculateCRC32(
                            (uint8_t *)(FirmwareUpdateManager::flash_partition_headers[complementary_partition]) +
                                offset,
                            len_bytes);
                        if (calculated_crc != crc) {
                            adsbee.SetReceiverEnable(1);  // Re-enable receiver before exit.
                            CPP_AT_ERROR("Calculated CRC 0x%x did not match provided CRC 0x%x.", calculated_crc, crc);
                        }
                    }
                    adsbee.SetReceiverEnable(1);  // Re-enable receiver before exit.
                    CPP_AT_SUCCESS();
                } else if (args[0].compare("VERIFY") == 0) {
                    // Verify the complementary flash partition.
                    CPP_AT_PRINTF(
                        "Verifying partition %u: %u Bytes, status 0x%x, application CRC 0x%x\r\n",
                        complementary_partition,
                        FirmwareUpdateManager::flash_partition_headers[complementary_partition]->app_size_bytes,
                        FirmwareUpdateManager::flash_partition_headers[complementary_partition]->status,
                        FirmwareUpdateManager::flash_partition_headers[complementary_partition]->app_crc);
                    // Modify the partition header.
                    if (FirmwareUpdateManager::VerifyFlashPartition(complementary_partition, true)) {
                        CPP_AT_SUCCESS();
                    } else {
                        CPP_AT_ERROR("Partition %u failed verification.", complementary_partition);
                    }
                } else if (args[0].compare("BOOT") == 0) {
                    // Boot the complementary flash partition.
                    CPP_AT_PRINTF("Booting partition %u...", complementary_partition);
                    adsbee.DisableWatchdog();
                    FirmwareUpdateManager::BootPartition(complementary_partition);
                    adsbee.EnableWatchdog();
                    CPP_AT_ERROR("Failed to boot partition %u.", complementary_partition);
                }
            }
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_HELP_CALLBACK(CommsManager::ATOTAHelpCallback) {
    CPP_AT_PRINTF(
        "AT+OTA?\r\n\tQueries current OTA status.\r\n\tAT+OTA=ERASE\r\n\tErase the sector to "
        "update. Responds with status messages for each erase operation, then OK when "
        "complete.\r\n\tAT+OTA=WRITE,<offset>,<num_bytes>,<checksum>\r\n\tBegin an "
        "OTA write operation of num_bytes to offset bytes from the start of the partition with provided CRC32 "
        "checksum. Will respond with BEGIN, and then OK when complete, or ERROR if checksum doesn't match or timeout "
        "reached.\r\n");
}

CPP_AT_CALLBACK(CommsManager::ATLogLevelCallback) {
    switch (op) {
        case '?':
            // AT+CONFIG mode query.
            CPP_AT_CMD_PRINTF("=%s", SettingsManager::kConsoleLogLevelStrs[log_level]);
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // AT+CONFIG set command.
            if (!CPP_AT_HAS_ARG(0)) {
                CPP_AT_ERROR("Need to specify a config mode to run.");
            }
            for (uint16_t i = 0; i < SettingsManager::kNumLogLevels; i++) {
                if (args[0].compare(SettingsManager::kConsoleLogLevelStrs[i]) == 0) {
                    log_level = static_cast<SettingsManager::LogLevel>(i);
                    CPP_AT_SUCCESS();
                }
            }
            CPP_AT_ERROR("Verbosity level %s not recognized.", args[0].data());
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATNetworkInfoCallback) {
    switch (op) {
        case '?':
            ObjectDictionary::ESP32NetworkInfo network_info;
            if (!esp32.Read(ObjectDictionary::kAddrNetworkInfo, network_info, sizeof(network_info))) {
                CPP_AT_ERROR("Error while reading network info from ESP32.");
            }

            CPP_AT_PRINTF("Ethernet: %s\r\n", network_info.ethernet_enabled ? "ENABLED" : "DISABLED");
            if (!network_info.ethernet_has_ip) {
                CPP_AT_PRINTF("\tNo IP address assigned.\r\n");
            } else {
                CPP_AT_PRINTF("\tIP Address: %s\r\n", network_info.ethernet_ip);
                CPP_AT_PRINTF("\tSubnet Mask: %s\r\n", network_info.ethernet_netmask);
                CPP_AT_PRINTF("\tGateway: %s\r\n", network_info.ethernet_gateway);
            }

            CPP_AT_PRINTF("WiFi Station: %s\r\n", network_info.wifi_sta_enabled ? "ENABLED" : "DISABLED");
            CPP_AT_PRINTF("\tSSID: %s\r\n", network_info.wifi_sta_ssid);
            if (!network_info.wifi_sta_has_ip) {
                CPP_AT_PRINTF("\tNo IP address assigned.\r\n");
            } else {
                CPP_AT_PRINTF("\tIP Address: %s\r\n", network_info.wifi_sta_ip);
                CPP_AT_PRINTF("\tSubnet Mask: %s\r\n", network_info.wifi_sta_netmask);
                CPP_AT_PRINTF("\tGateway: %s\r\n", network_info.wifi_sta_gateway);
            }

            CPP_AT_PRINTF("WiFi Access Point: %s\r\n", network_info.wifi_ap_enabled ? "ENABLED" : "DISABLED");
            CPP_AT_PRINTF("\tNum Clients: %u\r\n", network_info.wifi_ap_num_clients);
            for (uint16_t i = 0; i < network_info.wifi_ap_num_clients; i++) {
                CPP_AT_PRINTF("\t\tClient %u | IP: %s MAC: %s\r\n", i, network_info.wifi_ap_client_ips[i],
                              network_info.wifi_ap_client_macs[i]);
            }
            CPP_AT_SILENT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATProtocolCallback) {
    switch (op) {
        case '?':
            // Print out reporting protocols for CONSOLE and COMMS_UART.
            for (uint16_t iface = 0; iface < SettingsManager::SerialInterface::kGNSSUART; iface++) {
                CPP_AT_CMD_PRINTF("=%s,%s", SettingsManager::kSerialInterfaceStrs[iface],
                                  SettingsManager::kReportingProtocolStrs[reporting_protocols_[iface]]);
            }
            CPP_AT_SILENT_SUCCESS();
            break;
        case '=':
            // Set the reporting protocol for a given interface.
            if (!(CPP_AT_HAS_ARG(0) && CPP_AT_HAS_ARG(1))) {
                CPP_AT_ERROR("Requires two arguments: AT+PROTOCOL=<iface>,<protocol>.");
            }

            // Match the selected serial interface. Don't allow selection of the GNSS interface.
            SettingsManager::SerialInterface selected_iface = SettingsManager::SerialInterface::kNumSerialInterfaces;
            for (uint16_t iface = 0; iface < SettingsManager::SerialInterface::kGNSSUART; iface++) {
                if (args[0].compare(SettingsManager::kSerialInterfaceStrs[iface]) == 0) {
                    selected_iface = static_cast<SettingsManager::SerialInterface>(iface);
                    break;
                }
            }
            if (selected_iface == SettingsManager::kNumSerialInterfaces) {
                CPP_AT_ERROR("Invalid serial interface %s.", args[0].data());
            }

            // Match the selected protocol.
            SettingsManager::ReportingProtocol selected_protocol = SettingsManager::ReportingProtocol::kNumProtocols;
            for (uint16_t protocol = 0; protocol < SettingsManager::ReportingProtocol::kNumProtocols; protocol++) {
                if (args[1].compare(SettingsManager::kReportingProtocolStrs[protocol]) == 0) {
                    selected_protocol = static_cast<SettingsManager::ReportingProtocol>(protocol);
                    break;
                }
            }
            if (selected_protocol == SettingsManager::kNumProtocols) {
                CPP_AT_ERROR("Invalid reporting protocol %s.", args[1].data());
            }

            // Assign the selected protocol to the selected interface.
            reporting_protocols_[selected_iface] = selected_protocol;
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_HELP_CALLBACK(CommsManager::ATProtocolHelpCallback) {
    CPP_AT_PRINTF("\tSet the reporting protocol used on a given serial interface:\r\n");
    CPP_AT_PRINTF("\tAT+PROTOCOL=<iface>,<protocol>\r\n\t<iface> = ");
    for (uint16_t iface = 0; iface < SettingsManager::kGNSSUART; iface++) {
        CPP_AT_PRINTF("%s ", SettingsManager::kSerialInterfaceStrs[iface]);
    }
    CPP_AT_PRINTF("\r\n\t<protocol> = ");
    for (uint16_t protocol = 0; protocol < SettingsManager::kNumProtocols; protocol++) {
        CPP_AT_PRINTF("\t\t%s ", SettingsManager::kReportingProtocolStrs[protocol]);
    }
    CPP_AT_PRINTF("\r\n\tQuery the reporting protocol used on all interfaces:\r\n");
    CPP_AT_PRINTF("\tAT+PROTOCOL?\r\n\t+PROTOCOL=<iface>,<protocol>\r\n\t...\r\n");
}

CPP_AT_CALLBACK(CommsManager::ATRebootCallback) {
    adsbee.Reboot();
    // Note: would need to block here if there was a reboot delay.
    CPP_AT_ERROR("Failed to reboot.");
}

CPP_AT_CALLBACK(CommsManager::ATRxEnableCallback) {
    switch (op) {
        case '=':
            if (CPP_AT_HAS_ARG(0)) {
                bool receiver_enabled;
                CPP_AT_TRY_ARG2NUM(0, receiver_enabled);
                adsbee.SetReceiverEnable(receiver_enabled);
                CPP_AT_SUCCESS();
            }
            break;
        case '?':
            CPP_AT_CMD_PRINTF("=%d", adsbee.ReceiverIsEnabled());
            CPP_AT_SILENT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATSettingsCallback) {
    switch (op) {
        case '=':
            // Note: Don't allow settings modification from here, do it directly through other commands.
            if (CPP_AT_HAS_ARG(0)) {
                if (args[0].compare("SAVE") == 0) {
                    if (!settings_manager.Save()) {
                        CPP_AT_ERROR("Error while writing to EEPROM.");
                    }
                } else if (args[0].compare("LOAD") == 0) {
                    if (!settings_manager.Load()) {
                        CPP_AT_ERROR("Error while reading from EEPROM.");
                    }
                } else if (args[0].compare("RESET") == 0) {
                    settings_manager.ResetToDefaults();
                } else {
                    CPP_AT_ERROR("Invalid argument %s.", args[0].data());
                }
                CPP_AT_SUCCESS();
            }
            CPP_AT_ERROR("No arguments provided.");
            break;
        case '?':
            settings_manager.Print();
            CPP_AT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATTLReadCallback) {
    switch (op) {
        case '?':
            // Read command.
            int tl_mv = adsbee.ReadTLMilliVolts();
            CPP_AT_CMD_PRINTF("=%dmV (%d dBm)\r\n", tl_mv, adsbee.AD8313MilliVoltsTodBm(tl_mv));
            CPP_AT_SILENT_SUCCESS();
            break;
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

/**
 * AT+TL_SET Callback
 * AT+TL_SET=<tl_mv>
 *  tl_mv = Trigger Level, in milliVolts.
 * AT+TL_SET?
 * +TL_SET=
 */
CPP_AT_CALLBACK(CommsManager::ATTLSetCallback) {
    switch (op) {
        case '?': {
            // AT+TL_SET value query.
            int tl_mv = adsbee.GetTLMilliVolts();
            CPP_AT_CMD_PRINTF("=%dmV (%d dBm)\r\n", tl_mv, adsbee.AD8313MilliVoltsTodBm(tl_mv));
            CPP_AT_SILENT_SUCCESS();
            break;
        }
        case '=': {
            // Attempt setting LO TL value, in milliVolts, if first argument is not blank.
            if (CPP_AT_HAS_ARG(0)) {
                if (args[0].compare("LEARN") == 0) {
                    // Starting a new trigger level learning session.
                    adsbee.StartTLLearning();
                } else {
                    // Assigning trigger level manually.
                    uint16_t new_tl_mv;
                    CPP_AT_TRY_ARG2NUM(0, new_tl_mv);
                    if (!adsbee.SetTLMilliVolts(new_tl_mv)) {
                        CPP_AT_ERROR("Failed to set tl_mv.");
                    }
                }
            }
            CPP_AT_SUCCESS();
            break;
        }
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATWatchdogCallback) {
    switch (op) {
        case '?': {
            CPP_AT_CMD_PRINTF("=%u\r\n", adsbee.GetWatchdogTimeoutSec());
            CPP_AT_SILENT_SUCCESS();
            break;
        }
        case '=': {
            if (CPP_AT_HAS_ARG(0)) {
                if (args[0].compare("TEST") == 0) {
                    // Block for watdog timeout + 1 seconds to try triggering a watchdog event.
                    uint32_t begin_timestamp_ms = get_time_since_boot_ms();
                    static const uint32_t kDotPrintIntervalMs = 1 * kMsPerSec;
                    uint32_t last_dot_print_timestamp_ms = begin_timestamp_ms;
                    uint32_t watchdog_test_blocking_interval_sec = adsbee.GetWatchdogTimeoutSec() + 1;
                    CPP_AT_PRINTF("Blocking for %d seconds.\r\n", watchdog_test_blocking_interval_sec);
                    while ((get_time_since_boot_ms() - begin_timestamp_ms) / kMsPerSec <
                           watchdog_test_blocking_interval_sec) {
                        if (get_time_since_boot_ms() - last_dot_print_timestamp_ms > kDotPrintIntervalMs) {
                            CPP_AT_PRINTF(".");
                            last_dot_print_timestamp_ms = get_time_since_boot_ms();
                        }
                    }
                    CPP_AT_ERROR("Watchdog failed to trigger in %d seconds.", watchdog_test_blocking_interval_sec);
                } else {
                    uint32_t watchdog_timeout_sec = 0;
                    CPP_AT_TRY_ARG2NUM(0, watchdog_timeout_sec);
                    if (!adsbee.SetWatchdogTimeoutSec(watchdog_timeout_sec)) {
                        CPP_AT_ERROR("Setting watchdog timeout to %d seconds failed.");
                    }
                }
            }
            CPP_AT_SUCCESS();
            break;
        }
        default: {
            CPP_AT_ERROR("Operator %c not supported.", op);
        }
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATWiFiAPCallback) {
    switch (op) {
        case '?': {
            char redacted_password[SettingsManager::Settings::kWiFiPasswordMaxLen + 1];
            CPP_AT_CMD_PRINTF("=%d,%s,%s,%d\r\n", wifi_ap_enabled, wifi_ap_ssid, wifi_ap_password, wifi_ap_channel);
            CPP_AT_SILENT_SUCCESS();
            break;
        }
        case '=': {
            if (CPP_AT_HAS_ARG(0)) {
                CPP_AT_TRY_ARG2NUM(0, wifi_ap_enabled);
                CPP_AT_CMD_PRINTF(": wifi_ap_enabled=%d\r\n", wifi_ap_enabled);
            }
            if (CPP_AT_HAS_ARG(1)) {
                strncpy(wifi_ap_ssid, args[1].data(), SettingsManager::Settings::kWiFiSSIDMaxLen);
                wifi_ap_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen] = '\0';
                CPP_AT_CMD_PRINTF(": wifi_ap_ssid=%s\r\n", wifi_ap_ssid);
            }
            if (CPP_AT_HAS_ARG(2)) {
                strncpy(wifi_ap_password, args[2].data(), SettingsManager::Settings::kWiFiPasswordMaxLen);
                wifi_ap_password[SettingsManager::Settings::kWiFiPasswordMaxLen] = '\0';
                CPP_AT_CMD_PRINTF(": wifi_ap_password=%s\r\n", wifi_ap_password);
            }
            if (CPP_AT_HAS_ARG(3)) {
                uint8_t channel;
                CPP_AT_TRY_ARG2NUM(3, channel);
                if (channel == 0 || channel > SettingsManager::kWiFiAPChannelMax) {
                    CPP_AT_ERROR("WiFi channel out of range, must be >0 and <=%d.", SettingsManager::kWiFiAPChannelMax);
                }
                wifi_ap_channel = channel;
                CPP_AT_CMD_PRINTF(": wifi_ap_channel = %d\r\n", wifi_ap_channel);
            }
            CPP_AT_SUCCESS();
            break;
        }
        default: {
            CPP_AT_ERROR("Operator %c not supported.", op);
        }
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

CPP_AT_CALLBACK(CommsManager::ATWiFiSTACallback) {
    switch (op) {
        case '?': {
            char redacted_password[SettingsManager::Settings::kWiFiPasswordMaxLen + 1];
            SettingsManager::RedactPassword(wifi_sta_password, redacted_password,
                                            SettingsManager::Settings::kWiFiPasswordMaxLen);
            CPP_AT_CMD_PRINTF("=%d,%s,%s\r\n", wifi_sta_enabled, wifi_sta_ssid, redacted_password);
            CPP_AT_SILENT_SUCCESS();
            break;
        }
        case '=': {
            if (CPP_AT_HAS_ARG(0)) {
                CPP_AT_TRY_ARG2NUM(0, wifi_sta_enabled);
                CPP_AT_CMD_PRINTF(": wifi_sta_enabled=%d\r\n", wifi_sta_enabled);
            }
            if (CPP_AT_HAS_ARG(1)) {
                strncpy(wifi_sta_ssid, args[1].data(), SettingsManager::Settings::kWiFiSSIDMaxLen);
                wifi_sta_ssid[SettingsManager::Settings::kWiFiSSIDMaxLen] = '\0';
                CPP_AT_CMD_PRINTF(": sta_ssid=%s\r\n", wifi_sta_ssid);
            }
            if (CPP_AT_HAS_ARG(2)) {
                strncpy(wifi_sta_password, args[2].data(), SettingsManager::Settings::kWiFiPasswordMaxLen);
                wifi_sta_password[SettingsManager::Settings::kWiFiPasswordMaxLen] = '\0';
                char redacted_password[SettingsManager::Settings::kWiFiPasswordMaxLen];
                SettingsManager::RedactPassword(wifi_sta_password, redacted_password,
                                                SettingsManager::Settings::kWiFiPasswordMaxLen);
                CPP_AT_CMD_PRINTF(": sta_password=%s\r\n", redacted_password);
            }

            CPP_AT_SUCCESS();
            break;
        }
        default: {
            CPP_AT_ERROR("Operator %c not supported.", op);
        }
    }
    CPP_AT_ERROR("Operator '%c' not supported.", op);
}

const CppAT::ATCommandDef_t at_command_list[] = {
    {.command_buf = "+BAUDRATE",
     .min_args = 0,
     .max_args = 2,
     .help_string_buf = "AT+BAUDRATE=<iface>,<baudrate>\r\n\tSet the baud rate of a serial "
                        "interface.\r\n\tAT_BAUDRATE?\r\n\tQuery the baud rate of all serial interfaces.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATBaudrateCallback, comms_manager)},
    {.command_buf = "+BIAS_TEE_ENABLE",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "AT+BIAS_TEE_ENABLE=<enabled>\r\n\tEnable or disable the bias "
                        "tee.\r\n\tBIAS_TEE_ENABLE?\r\n\tQuery the status of the bias tee.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATBiasTeeEnableCallback, comms_manager)},
    {.command_buf = "+DEVICE_INFO",
     .min_args = 0,
     .max_args = 5,  // TODO: check this value.
     .help_string_buf = "AT+DEVICE_INFO?\r\n\tQuery device information.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATDeviceInfoCallback, comms_manager)},
    {.command_buf = "+ETHERNET",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "AT+ETHERNET=<enabled>\r\n\tEnable or disable the Ethernet "
                        "interface.\r\n\tETHERNET?\r\n\tQuery the status of the Ethernet interface.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATEthernetCallback, comms_manager)},
    {.command_buf = "+ESP32_ENABLE",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "AT+ESP32_ENABLE=<enabled>\r\n\tEnable or disable the ESP32.\r\n\tAT+ESP32_ENABLE?\r\n\tQuery "
                        "the enable status of the ESP32.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATESP32EnableCallback, comms_manager)},
    {.command_buf = "+FEED",
     .min_args = 0,
     .max_args = 5,
     .help_callback = ATFeedHelpCallback,
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATFeedCallback, comms_manager)},
    {.command_buf = "+FLASH_ESP32",
     .min_args = 0,
     .max_args = 0,
     .help_string_buf = "AT+FLASH_ESP32\r\n\tTriggers a firmware update of the ESP32 from the firmware image stored in "
                        "the RP2040's flash memory.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATFlashESP32Callback, comms_manager)},
    {.command_buf = "+HOSTNAME",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "AT+HOSTNAME=<hostname>\r\n\tSet the hostname for all network "
                        "interfaces.\r\n\tAT+HOSTNAME?\r\n\tQuery the "
                        "hostname used for all network interfaces.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATHostnameCallback, comms_manager)},
    {.command_buf = "+LOG_LEVEL",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf =
         "AT+LOG_LEVEL=<log_level [SILENT ERRORS WARNINGS LOGS]>\r\n\tSet how much stuff gets printed to the "
         "console.\r\n\t",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATLogLevelCallback, comms_manager)},
    {.command_buf = "+NETWORK_INFO",
     .min_args = 0,
     .max_args = 0,
     .help_string_buf = "AT+NETWORK_INFO?\r\n\tQueries network information.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATNetworkInfoCallback, comms_manager)},
    {.command_buf = "+OTA",
     .min_args = 0,
     .max_args = 4,
     .help_callback = CPP_AT_BIND_MEMBER_HELP_CALLBACK(CommsManager::ATOTAHelpCallback, comms_manager),
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATOTACallback, comms_manager)},
    {.command_buf = "+PROTOCOL",
     .min_args = 0,
     .max_args = 2,
     .help_callback = CPP_AT_BIND_MEMBER_HELP_CALLBACK(CommsManager::ATProtocolHelpCallback, comms_manager),
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATProtocolCallback, comms_manager)},
    {.command_buf = "+REBOOT",
     .min_args = 0,
     .max_args = 0,
     .help_string_buf = "REBOOT\r\n\tReboots the RP2040.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATRebootCallback, comms_manager)},
    {.command_buf = "+RX_ENABLE",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "RX_ENABLE=<enabled [1,0]>\r\n\tOK\r\n\tEnables or disables the receiver from receiving "
                        "messages.\r\n\tAT+RX_ENABLE?\r\n\t+RX_ENABLE=<enabled [1,0]>\r\n\tQuery whether the "
                        "recevier is enabled.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATRxEnableCallback, comms_manager)

    },
    {.command_buf = "+SETTINGS",
     .min_args = 0,
     .max_args = 3,
     .help_string_buf = "Load, save, or reset nonvolatile settings.\r\n\tAT+SETTINGS=<op [LOAD SAVE RESET]>\r\n\t"
                        "Display nonvolatile settings.\r\n\tAT+SETTINGS?\r\n\t+SETTINGS=...\r\n\t",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATSettingsCallback, comms_manager)},
#ifdef HARDWARE_UNIT_TESTS
    {.command_buf = "+TEST",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "Run hardware self-tests.",
     .callback = ATTestCallback},
#endif
    {.command_buf = "+TL_READ",
     .min_args = 0,
     .max_args = 0,
     .help_string_buf =
         "Read ADC counts and mV value for the minimum trigger level threshold. Call with no ops nor arguments, "
         "AT+TL_READ.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATTLReadCallback, comms_manager)},
    {.command_buf = "+TL_SET",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "Set minimum trigger level threshold for RF power detector.\r\n\tAT+TLSet=<tl_mv>"
                        "\tQuery trigger level.\r\n\tAT+TL_SET?\r\n\t+TLSet=<tl_mv>.",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATTLSetCallback, comms_manager)},
    {.command_buf = "+WATCHDOG",
     .min_args = 0,
     .max_args = 1,
     .help_string_buf = "Set the watchdog timeout, in seconds, 0-65535. 0 = watchdog disabled, 65535 = "
                        "18.2hrs.\r\n\tAT+WATCHDOG=<timeout_sec>\r\n\tTest watchdog by blocking for timeout_sec+1 "
                        "seconds.\r\n\tAT+WATCHDOG=TEST",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATWatchdogCallback, comms_manager)},
    {.command_buf = "+WIFI_AP",
     .min_args = 0,
     .max_args = 4,
     .help_string_buf =
         "Set WiFi access point params.\r\n\tAT+WIFI_AP=<enabled>,<ap_ssid>,<ap_pwd>,<ap_channel>\r\n\t"
         "Get WiFi access point params.\r\n\tAT+WIFI_AP?\r\n\t+WIFI_AP=<enabled>,<ap_ssid>,<ap_pwd>,<ap_channel>",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATWiFiAPCallback, comms_manager)},
    {.command_buf = "+WIFI_STA",
     .min_args = 0,
     .max_args = 3,
     .help_string_buf = "Set WiFi station params.\r\n\tAT+WIFI_STA=<enabled>,<sta_ssid>,<sta_pwd>\r\n\t"
                        "Get WiFi station params.\r\n\tAT+WIFI_STA?\r\n\t+WIFI_STA=<enabled>,<sta_ssid>,<sta_pwd>",
     .callback = CPP_AT_BIND_MEMBER_CALLBACK(CommsManager::ATWiFiSTACallback, comms_manager)},
};
const uint16_t at_command_list_num_commands = sizeof(at_command_list) / sizeof(at_command_list[0]);

bool CommsManager::UpdateAT() {
    static char stdio_at_command_buf[kATCommandBufMaxLen];
    static uint16_t stdio_at_command_buf_len = 0;
    // Check for new AT commands from STDIO. Process up to one line per loop.
    char c = static_cast<char>(getchar_timeout_us(0));
    while (static_cast<int8_t>(c) != PICO_ERROR_TIMEOUT) {
        stdio_at_command_buf[stdio_at_command_buf_len] = c;
        stdio_at_command_buf_len++;
        stdio_at_command_buf[stdio_at_command_buf_len] = '\0';
        if (c == '\n') {
            at_parser_.ParseMessage(std::string_view(stdio_at_command_buf));
            stdio_at_command_buf_len = 0;
            stdio_at_command_buf[stdio_at_command_buf_len] = '\0';  // clear command buffer
        }
        c = static_cast<char>(getchar_timeout_us(0));
    }

    if (esp32.IsEnabled()) {
        // Receive incoming network console characters.
        static char esp32_console_rx_buf[kATCommandBufMaxLen];
        static uint16_t esp32_console_rx_buf_len = 0;
        while (esp32_console_rx_queue.Pop(c)) {
            esp32_console_rx_buf[esp32_console_rx_buf_len] = c;
            esp32_console_rx_buf_len++;
            esp32_console_rx_buf[esp32_console_rx_buf_len] = '\0';
            if (c == '\n') {
                CONSOLE_INFO("CommsManager::UpdateAT", "Received network console message: %s\r\n",
                             esp32_console_rx_buf);
                at_parser_.ParseMessage(std::string_view(esp32_console_rx_buf));
                esp32_console_rx_buf_len = 0;
                esp32_console_rx_buf[esp32_console_rx_buf_len] = '\0';  // clear command buffer
            }
        }
    }

    return true;
}