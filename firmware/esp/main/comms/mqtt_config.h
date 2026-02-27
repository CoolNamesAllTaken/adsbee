#pragma once

/**
 * MQTT Feature Configuration
 *
 * This file controls which MQTT features are compiled into the firmware.
 */

// MQTT OTA (Over-The-Air) update support
#define CONFIG_MQTT_OTA_ENABLED 1

// MQTT topic and payload size limits
#define MQTT_MAX_TOPIC_LEN 96
#define MQTT_MAX_PAYLOAD_LEN 8192
