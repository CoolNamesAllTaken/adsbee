#include "mqtt_ota.hh"
#include "mqtt_client.hh"
#include "comms.hh"
#include "object_dictionary.hh"
#include "esp_log.h"
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <inttypes.h>
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"

static const char* TAG = "MQTT_OTA";

MQTTOTAHandler* MQTTOTAHandler::active_instance_ = nullptr;

MQTTOTAHandler::MQTTOTAHandler(const char* device_id, uint16_t feed_index)
    : feed_index_(feed_index) {
    strncpy(device_id_, device_id, sizeof(device_id_) - 1);
    response_sem_ = xSemaphoreCreateBinary();
}

MQTTOTAHandler::~MQTTOTAHandler() {
    if (active_instance_ == this) {
        object_dictionary.console_intercept_callback = nullptr;
        active_instance_ = nullptr;
    }
    if (response_sem_) {
        vSemaphoreDelete(response_sem_);
    }
}

bool MQTTOTAHandler::Initialize(ADSBeeMQTTClient* mqtt_client) {
    mqtt_client_ = mqtt_client;
    CONSOLE_INFO(TAG, "OTA shim initialized for feed %d", feed_index_);
    PublishState("IDLE");
    return true;
}

/**
 * Console intercept callback. Captures Pico responses via ObjectDictionary callback.
 * Called from the SPI receive task context, NOT the MQTT task.
 * @param[in] data Response data from the Pico.
 * @param[in] len Length of the response data.
 */
void MQTTOTAHandler::ConsoleInterceptCb(const char* data, size_t len) {
    if (active_instance_) {
        active_instance_->OnConsoleData(data, len);
    }
}

void MQTTOTAHandler::OnConsoleData(const char* data, size_t len) {
    for (size_t i = 0; i < len; i++) {
        char c = data[i];

        if (c == '\r' || c == '\n') {
            if (line_buf_pos_ > 0) {
                line_buf_[line_buf_pos_] = '\0';

                // --- Non-blocking ERASE completion ---
                // When erase_pending_, detect OK/ERROR from SPI context and
                // publish the state transition directly (esp_mqtt_client_publish
                // is thread-safe). This avoids blocking the MQTT event handler
                // for the full ~36s erase duration.
                if (erase_pending_) {
                    if (strstr(line_buf_, "OK") != nullptr) {
                        erase_pending_ = false;
                        CONSOLE_INFO(TAG, "Erase complete, ready for chunks");
                        PublishState("DOWNLOADING");
                    } else if (strstr(line_buf_, "ERROR") != nullptr) {
                        erase_pending_ = false;
                        active_ = false;
                        CONSOLE_ERROR(TAG, "Erase failed: %s", line_buf_);
                        PublishState("ERROR", "erase_failed");
                    }
                    line_buf_pos_ = 0;
                    continue;
                }

                // --- Blocking WRITE/VERIFY response via semaphore ---
                if (strstr(line_buf_, "OK") != nullptr ||
                    strstr(line_buf_, "READY") != nullptr) {
                    strncpy(response_buf_, line_buf_, kResponseBufSize - 1);
                    response_buf_[kResponseBufSize - 1] = '\0';
                    got_ok_ = true;
                    got_error_ = false;
                    xSemaphoreGive(response_sem_);
                } else if (strstr(line_buf_, "ERROR") != nullptr) {
                    strncpy(response_buf_, line_buf_, kResponseBufSize - 1);
                    response_buf_[kResponseBufSize - 1] = '\0';
                    got_ok_ = false;
                    got_error_ = true;
                    xSemaphoreGive(response_sem_);
                }

                line_buf_pos_ = 0;
            }
        } else {
            if (line_buf_pos_ < kLineBufSize - 1) {
                line_buf_[line_buf_pos_++] = c;
            }
        }
    }
}

bool MQTTOTAHandler::WaitForPicoResponse(const char* expected_str, uint32_t timeout_ms) {
    got_ok_ = false;
    got_error_ = false;
    response_buf_[0] = '\0';
    line_buf_pos_ = 0;

    TickType_t deadline = xTaskGetTickCount() + pdMS_TO_TICKS(timeout_ms);

    while (xTaskGetTickCount() < deadline) {
        TickType_t remaining = deadline - xTaskGetTickCount();
        if (xSemaphoreTake(response_sem_, remaining) == pdTRUE) {
            if (got_ok_ && strstr(response_buf_, expected_str)) {
                return true;
            }
            if (got_error_) {
                CONSOLE_ERROR(TAG, "Pico error: %s", response_buf_);
                return false;
            }
            // Got a response but not the one we wanted, keep waiting
            got_ok_ = false;
            got_error_ = false;
        }
    }

    CONSOLE_ERROR(TAG, "Timeout waiting for '%s' after %" PRIu32 "ms", expected_str, timeout_ms);
    return false;
}

/**
 * Parse a JSON manifest and store OTA metadata.
 * @param[in] data Raw JSON manifest data.
 * @param[in] len Length of the manifest data.
 * @retval True if manifest was parsed successfully, false otherwise.
 */
bool MQTTOTAHandler::HandleManifest(const uint8_t* data, size_t len) {
    const char* json = (const char*)data;

    if (!ParseJsonUint32(json, len, "size", &total_size_) ||
        !ParseJsonUint32(json, len, "chunks", &total_chunks_) ||
        !ParseJsonUint32(json, len, "chunk_size", &chunk_size_)) {
        CONSOLE_ERROR(TAG, "Invalid manifest: missing required fields");
        PublishState("ERROR", "invalid_manifest");
        return false;
    }

    ParseJsonString(json, len, "session_id", session_id_, sizeof(session_id_));

    session_id32_ = 0;
    if (strlen(session_id_) >= 8) {
        char tmp[9];
        memcpy(tmp, session_id_, 8);
        tmp[8] = '\0';
        session_id32_ = (uint32_t)strtoul(tmp, nullptr, 16);
    }

    chunks_received_ = 0;
    active_ = false;
    erase_pending_ = false;

    CONSOLE_INFO(TAG, "Manifest: size=%" PRIu32 " chunks=%" PRIu32 " chunk_size=%" PRIu32,
                 total_size_, total_chunks_, chunk_size_);

    PublishState("MANIFEST_RECEIVED");
    return true;
}

/**
 * Route a control command (START, VERIFY, BOOT, ABORT, REBOOT) to the Pico via AT+OTA.
 * @param[in] data Raw JSON command data.
 * @param[in] len Length of the command data.
 * @retval True if command was handled successfully, false otherwise.
 */
bool MQTTOTAHandler::HandleCommand(const uint8_t* data, size_t len) {
    char command[32] = {};
    if (!ParseJsonString((const char*)data, len, "command", command, sizeof(command))) {
        CONSOLE_ERROR(TAG, "No command field in control message");
        return false;
    }

    CONSOLE_INFO(TAG, "Command: %s", command);

    if (strcmp(command, "START") == 0) {
        // Check that no other handler already owns the console intercept callback.
        if (object_dictionary.console_intercept_callback != nullptr && active_instance_ != this) {
            CONSOLE_ERROR(TAG, "Console intercept callback already in use by another handler.");
            PublishState("ERROR", "intercept_busy");
            return false;
        }

        // Register console intercept to capture Pico responses.
        active_instance_ = this;
        object_dictionary.console_intercept_callback = ConsoleInterceptCb;

        // Send ERASE command — NON-BLOCKING.
        // The erase_pending_ flag tells OnConsoleData to watch for OK/ERROR
        // from the SPI task context and publish the state transition there.
        // This avoids blocking the MQTT event handler for ~36 seconds which
        // would prevent keepalive and cause broker disconnection.
        if (!SendCommandToPico("AT+OTA=ERASE\r\n")) {
            PublishState("ERROR", "erase_send_failed");
            return false;
        }

        active_ = true;
        chunks_received_ = 0;
        erase_pending_ = true;
        PublishState("ERASING");
        return true;  // Returns immediately — OnConsoleData publishes DOWNLOADING

    } else if (strcmp(command, "VERIFY") == 0) {
        if (!SendCommandToPico("AT+OTA=VERIFY\r\n")) {
            PublishState("ERROR", "verify_send_failed");
            return false;
        }
        PublishState("VERIFYING");

        if (!WaitForPicoResponse("OK", 10000)) {
            PublishState("ERROR", "verify_failed");
            return false;
        }

        PublishState("READY_TO_BOOT");
        return true;

    } else if (strcmp(command, "BOOT") == 0) {
        if (!SendCommandToPico("AT+OTA=BOOT\r\n")) {
            PublishState("ERROR", "boot_send_failed");
            return false;
        }
        active_ = false;
        object_dictionary.console_intercept_callback = nullptr;
        active_instance_ = nullptr;
        PublishState("BOOTING");
        return true;

    } else if (strcmp(command, "ABORT") == 0) {
        active_ = false;
        erase_pending_ = false;
        chunks_received_ = 0;
        total_size_ = 0;
        total_chunks_ = 0;
        chunk_size_ = 0;
        session_id_[0] = '\0';
        session_id32_ = 0;
        object_dictionary.console_intercept_callback = nullptr;
        active_instance_ = nullptr;
        PublishState("IDLE");
        return true;

    } else if (strcmp(command, "REBOOT") == 0) {
        active_ = false;
        erase_pending_ = false;
        object_dictionary.console_intercept_callback = nullptr;
        active_instance_ = nullptr;
        SendCommandToPico("AT+REBOOT\r\n");
        PublishState("REBOOTING");
        return true;

    } else if (strcmp(command, "GET_PARTITION") == 0) {
        SendCommandToPico("AT+OTA=GET_PARTITION\r\n");
        return true;
    }

    CONSOLE_WARNING(TAG, "Unknown command: %s", command);
    return false;
}

/**
 * Parse a binary chunk header, forward as AT+OTA=WRITE + data to the Pico,
 * wait for Pico OK before publishing ACK to MQTT.
 * After the last chunk, auto-verifies and publishes READY_TO_BOOT.
 * @param[in] chunk_index Chunk index from the MQTT topic.
 * @param[in] data Raw chunk data (14-byte header + payload).
 * @param[in] len Total length of the chunk data.
 * @retval True if chunk was written successfully, false otherwise.
 */
bool MQTTOTAHandler::HandleChunk(uint32_t chunk_index, const uint8_t* data, size_t len) {
    // Reject chunks while still erasing
    if (erase_pending_) {
        CONSOLE_WARNING(TAG, "Chunk %" PRIu32 " rejected — still erasing", chunk_index);
        PublishChunkAck(chunk_index, false);
        return false;
    }

    // Chunk wire format: 14-byte header + payload
    // Header: session_id32(4) | chunk_index(4) | chunk_size(2) | crc32(4)  [big-endian]
    static constexpr size_t kHeaderSize = 14;

    if (len < kHeaderSize) {
        CONSOLE_ERROR(TAG, "Chunk too small: %zu < %zu", len, kHeaderSize);
        PublishChunkAck(chunk_index, false);
        return false;
    }

    // Parse header (big-endian)
    uint32_t hdr_session = ((uint32_t)data[0] << 24) | ((uint32_t)data[1] << 16) |
                           ((uint32_t)data[2] << 8) | data[3];
    uint32_t hdr_index   = ((uint32_t)data[4] << 24) | ((uint32_t)data[5] << 16) |
                           ((uint32_t)data[6] << 8) | data[7];
    // data[8..9] = chunk_size (unused, we use actual payload length)
    uint32_t hdr_crc     = ((uint32_t)data[10] << 24) | ((uint32_t)data[11] << 16) |
                           ((uint32_t)data[12] << 8) | data[13];

    // Validate session
    if (session_id32_ != 0 && hdr_session != session_id32_) {
        CONSOLE_ERROR(TAG, "Session mismatch: expected 0x%08" PRIX32 " got 0x%08" PRIX32,
                      session_id32_, hdr_session);
        PublishChunkAck(chunk_index, false);
        return false;
    }

    // Validate index
    if (hdr_index != chunk_index) {
        CONSOLE_ERROR(TAG, "Index mismatch: topic=%" PRIu32 " header=%" PRIu32,
                      chunk_index, hdr_index);
        PublishChunkAck(chunk_index, false);
        return false;
    }

    const uint8_t* payload = data + kHeaderSize;
    size_t payload_len = len - kHeaderSize;

    // Calculate flash offset: 4KB app header + chunk position
    constexpr uint32_t kAppOffset = 4 * 1024;
    uint32_t offset = kAppOffset + (chunk_index * chunk_size_);

    // Build AT+OTA=WRITE command: offset(hex), len(decimal), crc(hex)
    char cmd[96];
    snprintf(cmd, sizeof(cmd), "AT+OTA=WRITE,%lX,%zu,%lX\r\n",
             (unsigned long)offset, payload_len, (unsigned long)hdr_crc);

    // Send WRITE command
    if (!SendCommandToPico(cmd)) {
        CONSOLE_ERROR(TAG, "Failed to send WRITE cmd for chunk %" PRIu32, chunk_index);
        PublishChunkAck(chunk_index, false);
        return false;
    }

    // Wait for READY from Pico before sending binary data
    if (!WaitForPicoResponse("READY", 5000)) {
        CONSOLE_ERROR(TAG, "No READY for chunk %" PRIu32, chunk_index);
        PublishChunkAck(chunk_index, false);
        return false;
    }

    // Send binary payload
    if (!SendDataToPico(payload, payload_len)) {
        CONSOLE_ERROR(TAG, "Failed to send data for chunk %" PRIu32, chunk_index);
        PublishChunkAck(chunk_index, false);
        return false;
    }

    // Wait for OK (Pico verifies CRC and writes to flash)
    if (!WaitForPicoResponse("OK", 5000)) {
        CONSOLE_ERROR(TAG, "Write failed for chunk %" PRIu32, chunk_index);
        PublishChunkAck(chunk_index, false);
        return false;
    }

    // Success — Pico confirmed the write
    chunks_received_++;
    PublishChunkAck(chunk_index, true);

    if (chunks_received_ % 50 == 0) {
        CONSOLE_INFO(TAG, "Progress: %" PRIu32 "/%" PRIu32 " chunks",
                     chunks_received_, total_chunks_);
    }

    // After last chunk: auto-verify so the publisher sees READY_TO_BOOT.
    // The publisher expects this (line 777: "device auto-verifies after all chunks").
    if (chunks_received_ == total_chunks_) {
        CONSOLE_INFO(TAG, "All %" PRIu32 " chunks written, auto-verifying...", total_chunks_);
        PublishState("VERIFYING");

        if (!SendCommandToPico("AT+OTA=VERIFY\r\n")) {
            PublishState("ERROR", "verify_send_failed");
            return false;
        }

        if (!WaitForPicoResponse("OK", 10000)) {
            PublishState("ERROR", "verify_failed");
            return false;
        }

        CONSOLE_INFO(TAG, "Verification passed");
        PublishState("READY_TO_BOOT");
    }

    return true;
}

/**
 * Push an AT command string into the network console RX queue.
 * @param[in] cmd Null-terminated command string.
 * @retval True if command was enqueued successfully, false otherwise.
 */
bool MQTTOTAHandler::SendCommandToPico(const char* cmd) {
    size_t cmd_len = strlen(cmd);

    xSemaphoreTake(object_dictionary.network_console_rx_queue_mutex, portMAX_DELAY);

    size_t available = object_dictionary.network_console_rx_queue.MaxNumElements() -
                       object_dictionary.network_console_rx_queue.Length();
    if (available < cmd_len) {
        xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
        CONSOLE_ERROR(TAG, "Queue full: need %zu have %zu", cmd_len, available);
        return false;
    }

    for (size_t i = 0; i < cmd_len; i++) {
        if (!object_dictionary.network_console_rx_queue.Enqueue(cmd[i])) {
            xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
            return false;
        }
    }

    xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
    return true;
}

bool MQTTOTAHandler::SendDataToPico(const uint8_t* data, size_t len) {
    size_t pos = 0;
    while (pos < len) {
        xSemaphoreTake(object_dictionary.network_console_rx_queue_mutex, portMAX_DELAY);

        size_t available = object_dictionary.network_console_rx_queue.MaxNumElements() -
                           object_dictionary.network_console_rx_queue.Length();
        if (available == 0) {
            xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);
            vTaskDelay(pdMS_TO_TICKS(5));
            continue;
        }

        size_t to_push = (len - pos < available) ? (len - pos) : available;
        bool ok = true;
        for (size_t i = 0; i < to_push; i++) {
            if (!object_dictionary.network_console_rx_queue.Enqueue(static_cast<char>(data[pos + i]))) {
                ok = false;
                break;
            }
        }
        xSemaphoreGive(object_dictionary.network_console_rx_queue_mutex);

        if (!ok) {
            vTaskDelay(pdMS_TO_TICKS(1));
            continue;
        }
        pos += to_push;
    }
    return true;
}

/**
 * Publish JSON state to the MQTT OTA status topic.
 * @param[in] state Current OTA state string (e.g., "ERASING", "DOWNLOADING").
 * @param[in] detail Optional detail string for error context.
 */
void MQTTOTAHandler::PublishState(const char* state, const char* detail) {
    if (!mqtt_client_) return;

    char topic[MQTT_MAX_TOPIC_LEN];
    snprintf(topic, sizeof(topic), "%s/ota/status/state", device_id_);

    char payload[256];
    int n;
    if (detail) {
        n = snprintf(payload, sizeof(payload),
                     "{\"session_id\":\"%s\",\"state\":\"%s\",\"detail\":\"%s\","
                     "\"chunks_received\":%" PRIu32 ",\"total_chunks\":%" PRIu32 "}",
                     session_id_, state, detail, chunks_received_, total_chunks_);
    } else {
        n = snprintf(payload, sizeof(payload),
                     "{\"session_id\":\"%s\",\"state\":\"%s\","
                     "\"chunks_received\":%" PRIu32 ",\"total_chunks\":%" PRIu32 "}",
                     session_id_, state, chunks_received_, total_chunks_);
    }

    mqtt_client_->Publish(topic, (const uint8_t*)payload, n, 1, false);
}

void MQTTOTAHandler::PublishChunkAck(uint32_t chunk_index, bool success) {
    if (!mqtt_client_) return;

    char topic[MQTT_MAX_TOPIC_LEN];
    snprintf(topic, sizeof(topic), "%s/ota/status/ack/%" PRIu32, device_id_, chunk_index);

    const char* ack = success ? "1" : "0";
    mqtt_client_->Publish(topic, (const uint8_t*)ack, 1, 1, false);
}

/**
 * Parse a JSON string value by key.
 * @param[in] json JSON string to search.
 * @param[in] json_len Length of the JSON string.
 * @param[in] key Key to search for.
 * @param[out] buf Buffer to write the value into.
 * @param[in] buf_size Size of the output buffer.
 * @retval True if the key was found and value extracted, false otherwise.
 */
bool MQTTOTAHandler::ParseJsonString(const char* json, size_t json_len,
                                     const char* key, char* buf, size_t buf_size) {
    char pattern[64];
    snprintf(pattern, sizeof(pattern), "\"%s\"", key);

    const char* pos = strstr(json, pattern);
    if (!pos || (size_t)(pos - json) >= json_len) return false;

    pos += strlen(pattern);
    while (pos < json + json_len && (*pos == ':' || *pos == ' ')) pos++;
    if (pos >= json + json_len || *pos != '"') return false;
    pos++;  // skip opening quote

    const char* end = pos;
    while (end < json + json_len && *end != '"') end++;
    if (end >= json + json_len) return false;

    size_t val_len = end - pos;
    if (val_len >= buf_size) val_len = buf_size - 1;
    memcpy(buf, pos, val_len);
    buf[val_len] = '\0';
    return true;
}

bool MQTTOTAHandler::ParseJsonUint32(const char* json, size_t json_len,
                                     const char* key, uint32_t* out) {
    char pattern[64];
    snprintf(pattern, sizeof(pattern), "\"%s\"", key);

    const char* pos = strstr(json, pattern);
    if (!pos || (size_t)(pos - json) >= json_len) return false;

    pos += strlen(pattern);
    while (pos < json + json_len && (*pos == ':' || *pos == ' ')) pos++;
    if (pos >= json + json_len) return false;

    *out = (uint32_t)strtoul(pos, nullptr, 10);
    return true;
}
