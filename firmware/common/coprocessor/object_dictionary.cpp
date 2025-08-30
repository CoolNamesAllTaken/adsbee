#include "object_dictionary.hh"

#include "hal.hh"  // for timestamping
#ifdef ON_ESP32
#include "adsbee_server.hh"
#include "device_info.hh"
#endif

#include "comms.hh"

const uint8_t ObjectDictionary::kFirmwareVersionMajor = 0;
const uint8_t ObjectDictionary::kFirmwareVersionMinor = 8;
const uint8_t ObjectDictionary::kFirmwareVersionPatch = 2;
// NOTE: Indicate a final release with RC = 0.
const uint8_t ObjectDictionary::kFirmwareVersionReleaseCandidate = 0;

const uint32_t ObjectDictionary::kFirmwareVersion = (kFirmwareVersionMajor << 24) | (kFirmwareVersionMinor << 16) |
                                                    (kFirmwareVersionPatch << 8) | kFirmwareVersionReleaseCandidate;

#ifdef ON_COPRO_SLAVE
bool ObjectDictionary::SetBytes(Address addr, uint8_t *buf, uint16_t buf_len, uint16_t offset) {
    switch (addr) {
        case kAddrScratch:
            // Warning: printing here will cause a timeout and tests will fail.
            // CONSOLE_INFO("ObjectDictionary::SetBytes", "Setting %d settings Bytes at offset %d.", buf_len,
            // offset);
            memcpy((uint8_t *)&scratch_ + offset, buf, buf_len);
            break;
        case kAddrSettingsData:
            // Warning: printing here will cause a timeout and tests will fail.
            // CONSOLE_INFO("ObjectDictionary::SetBytes", "Setting %d settings Bytes at offset %d.", buf_len,
            // offset);
            memcpy((uint8_t *)&(settings_manager.settings) + offset, buf, buf_len);
            if (offset + buf_len == sizeof(SettingsManager::Settings)) {
                CONSOLE_INFO("SPICoprocessor::SetBytes", "Wrote last chunk of settings data. Applying new values.");
                settings_manager.Apply();
            }
            break;
        case kAddrRollQueue: {
            // Ignore offset since we only allow full writes for this command.
            RollQueueRequest roll_request;
            memcpy(&roll_request, buf, sizeof(RollQueueRequest));
            switch (roll_request.queue_id) {
                case kQueueIDLogMessages:
                    // Roll the log message queue.
                    log_message_queue.Discard(roll_request.num_items);
                    break;
                case kQueueIDSCCommandRequests:
                    for (uint16_t i = 0; i < roll_request.num_items; i++) {
                        // Dequeue requests one by one so that we can call their callbacks.
                        SCCommandRequestWithCallback request_with_callback;
                        if (!sc_command_request_queue.Dequeue(request_with_callback)) {
                            CONSOLE_ERROR("ObjectDictionary::SetBytes",
                                          "Failed to pop SCCommand request from queue during roll.");
                            return false;
                        }
                        if (request_with_callback.complete_callback) {
                            request_with_callback.complete_callback();  // Call the callback if it exists.
                        }
                    }
                    break;
                case kQueueIDConsole:
#ifdef ON_ESP32
                    xSemaphoreTake(object_dictionary.network_console_rx_queue_mutex, portMAX_DELAY);
                    if (!network_console_rx_queue.Discard(roll_request.num_items)) {
                        CONSOLE_ERROR("ObjectDictionary::SetBytes",
                                      "Failed to discard %d chars from the network console TX queue.",
                                      roll_request.num_items);
                        xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
                        return false;
                    }
                    xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
#elif defined(ON_PICO)
                    if (!network_console_rx_queue.Discard(roll_request.num_items)) {
                        CONSOLE_ERROR("ObjectDictionary::SetBytes",
                                      "Failed to discard %d chars from the network console TX queue.",
                                      roll_request.num_items);

                        return false;
                    }
#else
                    CONSOLE_ERROR("ObjectDictionary::SetBytes",
                                  "Received roll queue request for network console on unsupported device.");
                    return false;
#endif
                    break;
                default:
                    CONSOLE_ERROR("ObjectDictionary::SetBytes",
                                  "Received roll queue request for nonexistent queue ID %d.", roll_request.queue_id);
                    return false;
            }
            break;
        }
#ifdef ON_ESP32
        case kAddrConsole: {
            // RP2040 writing to the ESP32's network console interface.
            char message[kNetworkConsoleMessageMaxLenBytes + 1] = {'\0'};
            strncpy(message, (char *)buf, buf_len);
            message[kNetworkConsoleMessageMaxLenBytes] = '\0';  // Null terminate for safety.
            // Don't print here to avoid print of print doom loop explosion.
            // CONSOLE_INFO("ObjectDictionary::SetBytes", "Forwarding message to network console: %s",
            // message);
            adsbee_server.network_console.BroadcastMessage(message, buf_len);
            break;
        }
        case kAddrRawModeSPacket: {
            RawModeSPacket tpacket;
            memcpy(&tpacket, buf, sizeof(RawModeSPacket));
            // Warning: printing here will cause a timeout and tests will fail.
            // CONSOLE_INFO("SPICoprocessor::SetBytes", "Received a raw %d-bit transponder packet.",
            //              tpacket.buffer_len_bits);
            adsbee_server.HandleRawModeSPacket(tpacket);
            break;
        }
        case kAddrRawModeSPacketArray: {
            uint8_t num_packets = buf[0];
            RawModeSPacket tpacket;
            for (uint16_t i = 0; i < num_packets && i * sizeof(RawModeSPacket) + sizeof(uint8_t) < buf_len; i++) {
                memcpy(&tpacket, buf + sizeof(uint8_t) + i * sizeof(RawModeSPacket), sizeof(RawModeSPacket));
                adsbee_server.HandleRawModeSPacket(tpacket);
            }
            break;
        }
        case kAddrAircraftDictionaryMetrics: {
            AircraftDictionary::Metrics rp2040_metrics;
            memcpy(&rp2040_metrics, buf + offset, buf_len);
            xQueueSend(adsbee_server.rp2040_aircraft_dictionary_metrics_queue, &rp2040_metrics, 0);
            break;
        }
#elif defined(ON_TI)
#endif
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
            // CONSOLE_INFO("ObjectDictionary::GetBytes", "Getting %d settings Bytes at offset %d.",
            // buf_len, offset);
            memcpy(buf, (uint8_t *)&(settings_manager.settings) + offset, buf_len);
            break;
        case kAddrDeviceStatus: {
            uint16_t num_log_messages = log_message_queue.Length();
#ifdef ON_ESP32
            xSemaphoreTake(object_dictionary.network_console_rx_queue_mutex, portMAX_DELAY);
            uint16_t num_network_console_rx_chars = network_console_rx_queue.Length();
            xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
            ESP32DeviceStatus device_status = {.timestamp_ms = get_time_since_boot_ms(),
                                               .num_queued_log_messages = num_log_messages,
                                               .queued_log_messages_packed_size_bytes =
                                                   static_cast<uint32_t>(num_log_messages * LogMessage::kHeaderSize),
                                               .num_queued_sc_command_requests = sc_command_request_queue.Length(),
                                               .num_queued_network_console_rx_chars = num_network_console_rx_chars};
#elif defined(ON_TI)
            SubGHzDeviceStatus device_status = {
                .timestamp_ms = get_time_since_boot_ms(),
                .num_queued_log_messages = num_log_messages,
                .queued_log_messages_packed_size_bytes =
                    static_cast<uint32_t>(num_log_messages * LogMessage::kHeaderSize),
                .num_queued_sc_command_requests = sc_command_request_queue.Length(),
                .num_queued_decoded_uat_adsb_packets = decoded_uat_adsb_packet_queue.Length()};
#endif
            for (uint16_t i = 0; i < log_message_queue.Length(); i++) {
                LogMessage log_message;
                if (log_message_queue.Peek(log_message, i)) {
                    device_status.queued_log_messages_packed_size_bytes +=
                        log_message.num_chars + 1;  // +1 for null terminator
                }
            }
            memcpy(buf, &device_status + offset, buf_len);
            break;
        }
        case kAddrLogMessages: {
            // RP2040 reading log messages from the ESP32.
            // Pack as many pending log messages as will fit in the buffer.
            PackLogMessages(buf, buf_len, log_message_queue, kLogMessageQueueDepth);
            break;
        }
        case kAddrSCCommandRequests: {
            if (offset != 0) {
                CONSOLE_ERROR("ObjectDictionary::GetBytes",
                              "Offset %d for reading SCCommandRequest not supported, must be 0.", offset);
                return false;
            }
            if (buf_len != sizeof(SCCommandRequest)) {
                CONSOLE_ERROR("ObjectDictionary::GetBytes",
                              "Buffer length %d for reading SCCommandRequest must be exactly %d.", buf_len,
                              sizeof(SCCommandRequest));
                return false;
            }
            SCCommandRequestWithCallback request_with_callback;
            if (!sc_command_request_queue.Peek(request_with_callback)) {
                CONSOLE_ERROR("ObjectDictionary::GetBytes", "No SCCommand requests available to read.");
                return false;
            }
            SCCommandRequest &request = request_with_callback.request;
            memcpy(buf, &request, sizeof(SCCommandRequest));
            break;
        }
#ifdef ON_ESP32
        case kAddrESP32DeviceInfo: {
            ESP32DeviceInfo esp32_device_info = GetESP32DeviceInfo();
            memcpy(buf, &esp32_device_info + offset, buf_len);
            break;
        }
        case kAddrESP32NetworkInfo: {
            ESP32NetworkInfo network_info = comms_manager.GetNetworkInfo();
            memcpy(buf, &network_info + offset, buf_len);
            break;
        }
        case kAddrConsole: {
            xSemaphoreTake(object_dictionary.network_console_rx_queue_mutex, portMAX_DELAY);
            if (network_console_rx_queue.Length() < buf_len) {
                CONSOLE_ERROR("ObjectDictionary::GetBytes",
                              "Buffer length %d of network console message to read is larger than RX queue length %d.",
                              buf_len, network_console_rx_queue.Length());
                xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
                return false;
            }
            for (uint16_t i = 0; i < buf_len; i++) {
                char ch;
                if (!network_console_rx_queue.Peek(ch, i)) {
                    CONSOLE_ERROR("ObjectDictionary::GetBytes",
                                  "Failed to peek character %d from network console RX queue.", i);
                    xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
                    return false;
                }
                buf[i] = static_cast<uint8_t>(ch);
            }
            xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
            break;
        }
#elif defined(ON_TI)
#endif
        default:
            CONSOLE_ERROR("SPICoprocessor::SetBytes", "No behavior implemented for reading from address 0x%x.", addr);
            return false;
    }
    return true;
}

bool ObjectDictionary::RequestSCCommand(const SCCommandRequestWithCallback &request_with_callback) {
    if (sc_command_request_queue.Enqueue(request_with_callback)) {
        return true;
    } else {
        CONSOLE_ERROR("ObjectDictionary::RequestSCCommand", "Failed to push SCCommandRequest to queue, queue is full.");
        return false;
    }
}

bool ObjectDictionary::RequestSCCommandBlocking(const SCCommandRequestWithCallback &request_with_callback) {
#ifdef ON_ESP32
    SemaphoreHandle_t command_complete_semaphore = xSemaphoreCreateBinary();
    if (command_complete_semaphore == NULL) {
        CONSOLE_ERROR("ADSBeeServer::Init", "Failed to create settings read semaphore.");
        return false;
    }
#endif

    bool ret = object_dictionary.RequestSCCommand(ObjectDictionary::SCCommandRequestWithCallback {
        .request = request_with_callback.request,
        .complete_callback =
#ifdef ON_ESP32
            [command_complete_semaphore, request_with_callback]() {
#else
            [request_with_callback]() {
#endif
                if (request_with_callback.complete_callback) {
                    request_with_callback.complete_callback();  // Call the existing callback if it exists.
                }
#ifdef ON_ESP32
                xSemaphoreGive(command_complete_semaphore);
#endif
            },
    });  // Require ack.

#ifdef ON_ESP32
    // Wait for the callback to complete
    xSemaphoreTake(command_complete_semaphore, portMAX_DELAY);
    vSemaphoreDelete(command_complete_semaphore);
#endif
    return ret;
}
#endif

uint16_t ObjectDictionary::PackLogMessages(uint8_t *buf, uint16_t buf_len,
                                           PFBQueue<ObjectDictionary::LogMessage> &log_message_queue,
                                           uint16_t num_messages) {
    uint16_t bytes_written = 0;
    for (uint16_t i = 0; i < num_messages; i++) {
        LogMessage log_message;
        if (!log_message_queue.Peek(log_message)) {
            break;  // No more messages to pack.
        }
        uint16_t buf_bytes_remaining = buf_len - bytes_written;
        uint16_t log_message_packed_size =
            LogMessage::kHeaderSize + log_message.num_chars + 1;  // +1 for null terminator
        if (buf_bytes_remaining < log_message_packed_size) {
            break;  // Not enough space to write the next log message.
        }
        memcpy(buf + bytes_written, &log_message, log_message_packed_size - 1);
        buf[bytes_written + log_message_packed_size - 1] = '\0';  // Null terminate the message.
        bytes_written += log_message_packed_size;
        // Don't pop log messages here, wait for the roll request to do that.
    }
    return bytes_written;
}

uint16_t ObjectDictionary::UnpackLogMessages(uint8_t *buf, uint16_t buf_len,
                                             PFBQueue<ObjectDictionary::LogMessage> &log_message_queue,
                                             uint16_t max_num_messages) {
    uint16_t bytes_read = 0;
    uint16_t num_messages = 0;

    while (bytes_read < buf_len && num_messages < max_num_messages) {
        LogMessage log_message;
        if (buf_len - bytes_read < LogMessage::kHeaderSize) {
            break;  // Not enough data for header.
        }
        // Cast to a Byte array to avoid warnings about memcpy not writing the full LogMessage object.
        memcpy((uint8_t *)(&log_message), buf + bytes_read, LogMessage::kHeaderSize);

        if (log_message.num_chars > kLogMessageMaxNumChars) {
            CONSOLE_ERROR("ObjectDictionary::UnpackLogMessages", "Invalid log message length: %d",
                          log_message.num_chars);
            break;  // Invalid length.
        }

        if (buf_len - bytes_read < LogMessage::kHeaderSize + log_message.num_chars + 1) {
            break;  // Not enough data for the full message.
        }

        memcpy(log_message.message, buf + bytes_read + LogMessage::kHeaderSize, log_message.num_chars);
        log_message.message[log_message.num_chars] = '\0';  // Null terminate the message.

        if (log_message_queue.IsFull()) {
            log_message_queue.Clear();
            CONSOLE_ERROR("ObjectDictionary::UnpackLogMessages", "Log message queue is full, clearing it.");
        }
        log_message_queue.Enqueue(log_message);

        bytes_read += LogMessage::kHeaderSize + log_message.num_chars + 1;  // Move past header and message.
        num_messages++;
    }

    return num_messages;
}