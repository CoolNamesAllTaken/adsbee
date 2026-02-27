# MQTT OTA (Over-The-Air) Update Guide

## Quick Start

```bash
# 1. On the device - Enable MQTT OTA (one-time setup)
AT+FEED=0,192.168.1.100,1883,1,MQTT
AT+MQTTOTA=0,1    # Enable OTA for feed 0
AT+SETTINGS=SAVE
AT+REBOOT

# 2. On your computer - Send firmware update
python3 mqtt_ota_publisher.py --broker 192.168.1.100 --device bee0003a59b3356e firmware.ota
```

## Overview

The ADSBee MQTT OTA system enables remote firmware updates via MQTT protocol. The implementation uses a **pass-through architecture** where the ESP32 forwards OTA commands and data to the Pico (RP2040) processor, which handles the actual firmware storage and update process.

## Architecture

### Pass-Through Design
```
[MQTT Broker] <--MQTT--> [ESP32] <--SPI/AT Commands--> [Pico/RP2040]
                            |                              |
                         (Forwards)                   (Stores & Flashes)
```

**Benefits:**
- No ESP32 flash storage needed for OTA
- Leverages existing Pico dual-partition OTA system
- Simplified ESP32 code
- More reliable single-point flash management
- Saves ~12MB of ESP32 flash space

### Components

1. **MQTT Broker** - Distributes firmware chunks and commands
2. **ESP32** - Receives MQTT messages, forwards to Pico via AT commands
3. **Pico (RP2040)** - Manages dual-partition OTA, performs actual firmware update
4. **Python Publisher** - Sends firmware to device via MQTT

## Device Configuration

### Enable MQTT OTA

1. **Configure MQTT connection:**
```
AT+FEED=0,192.168.1.100,1883,1,MQTT
AT+MQTTDEVICE=bee0003a59b3356e
```

2. **Enable OTA for the MQTT feed (REQUIRED):**
```
AT+MQTTOTA=0,1
```
**Note:** OTA is disabled by default for security. You must explicitly enable it for each feed that should support OTA updates.

3. **Optional: Configure authentication:**
```
AT+MQTTAUTH=username,password
```

4. **Optional: Enable TLS:**
```
AT+MQTTTLS=VERIFY
```

5. **Save settings and reboot:**
```
AT+SAVE
AT+REBOOT
```
**Note:** A reboot is required after enabling OTA for the settings to take effect.

## Firmware Preparation

The firmware must be in `.ota` format, which includes partition information for the dual-partition system.

### Building OTA Firmware
```bash
cd firmware/esp
idf.py build

cd ../pico
./build.sh --ota
# Creates: build/adsbee_1090.ota
```

## Python OTA Publisher

### Installation
```bash
pip install paho-mqtt
```

### Basic Usage
```bash
python3 mqtt_ota_publisher.py \
    --broker localhost \
    --device bee0003a59b3356e \
    firmware.ota
```

### Advanced Options
```bash
python3 mqtt_ota_publisher.py \
    --broker broker.hivemq.com \
    --port 1883 \
    --device bee0003a59b3356e \
    --username myuser \
    --password mypass \
    --chunk-size 2048 \
    --pre-reboot \
    --auto-boot \
    firmware.ota
```

#### Command-line Arguments:
- `--broker` - MQTT broker hostname (required)
- `--port` - MQTT broker port (default: 1883)
- `--device` - Target device ID (required)
- `--username` - MQTT username for authentication
- `--password` - MQTT password for authentication
- `--tls` - Enable TLS/SSL connection
- `--chunk-size` - Size of firmware chunks in bytes (default: 4096 to match flash sector; multiple of 256)
- `--pre-reboot` - Reboot device before OTA for clean state
- `--auto-boot` - Automatically reboot to new firmware after verification
- `--version` - Firmware version string (default: 0.8.3)

## MQTT Topics

### Control Topics (Publisher → Device)
- `{device_id}/ota/control/manifest` - Firmware manifest with metadata
- `{device_id}/ota/control/command` - Control commands (START, PAUSE, RESUME, ABORT, VERIFY, BOOT, REBOOT, GET_PARTITION)
- `{device_id}/ota/data/chunk/{index}` - Firmware data chunks

### Status Topics (Device → Publisher)
- `{device_id}/ota/status/state` - Current OTA state
- `{device_id}/ota/status/progress` - Download progress
- `{device_id}/ota/status/ack/{index}` - Chunk acknowledgments
- `{device_id}/ota/status/manifest_ack` - Manifest received acknowledgment
- `{device_id}/telemetry` - Device telemetry (used for online detection)

## OTA Process Flow

### 1. Pre-flight Checks
```
Publisher                 Device
    |                        |
    |--Check Connectivity--->|
    |<----Telemetry----------|
    |                        |
    |--Optional: REBOOT----->|
    |      (wait 60s)        |
    |<----Telemetry----------|
```

### 2. Manifest Exchange
```
Publisher                 Device
    |                        |
    |--Publish Manifest----->|
    |<--Manifest ACK---------|
    |                        |
    |--Send START command--->|
    |<--State: DOWNLOADING---|
```

### 3. Firmware Transfer
```
Publisher                 Device                 Pico
    |                        |                     |
    |--Chunk[0]------------->|--AT+OTA=WRITE------>|
    |<--ACK[0]---------------|<----OK--------------|
    |                        |                     |
    |--Chunk[1]------------->|--AT+OTA=WRITE------>|
    |<--ACK[1]---------------|<----OK--------------|
    |        ...             |       ...           |
    |--Chunk[N]------------->|--AT+OTA=WRITE------>|
    |<--ACK[N]---------------|<----OK--------------|
    |                        |                     |
    |<--State: VERIFYING-----|                     |
```

### 4. Verification & Boot
```
Publisher                 Device                 Pico
    |                        |                     |
    |                        |--AT+OTA=VERIFY----->|
    |                        |<--CRC Verify OK-----|
    |<--State: READY_TO_BOOT-|                     |
    |                        |                     |
    |--Send BOOT command---->|--AT+OTA=BOOT------->|
    |                        |    (Device Reboots) |
```

## OTA States

- **IDLE** - No OTA in progress
- **MANIFEST_RECEIVED** - Manifest received and validated
- **ERASING** - Erasing flash partition (Pico side)
- **DOWNLOADING** - Receiving firmware chunks
- **VERIFYING** - Verifying firmware integrity
- **READY_TO_BOOT** - Firmware verified, ready to boot
- **ERROR** - OTA failed

## AT Commands (Pico Side)

The Pico implements these AT commands for OTA:

- `AT+OTA?` - Query OTA status
- `AT+OTA=GET_PARTITION` - Get target partition number
- `AT+OTA=ERASE` - Erase complementary partition
- `AT+OTA=ERASE,offset,length` - Partial erase
- `AT+OTA=WRITE,offset,length,crc` - Write firmware chunk
- `AT+OTA=VERIFY` - Verify firmware integrity (CRC32 via header)
- `AT+OTA=BOOT` - Boot from new partition

## Troubleshooting

### Device Not Responding
1. Check device ID matches exactly (including leading zeros)
2. Verify MQTT connection: `AT+STATUS`
3. Check telemetry is being published
4. Ensure device has network connectivity

### OTA Fails Immediately / "Cannot start OTA - no manifest"
1. **Verify OTA is enabled for the feed:** `AT+MQTTOTA?0` (should return 1 if enabled)
2. If disabled, enable it: `AT+MQTTOTA=0,1` then `AT+SETTINGS=SAVE` and `AT+REBOOT`
3. Check partition configuration on Pico
4. Verify firmware size fits in partition (< 6MB)
5. Check ESP32 console for error messages
6. Ensure MQTT_OTA_ENABLED=1 in firmware
7. Look for "OTA enabled for MQTT feed" message in ESP32 logs after reboot

### Chunks Not Acknowledged
1. Check chunk size (max 4096 bytes)
2. Verify SPI communication between ESP32 and Pico
3. Check network console queue isn't full
4. Monitor Pico serial output for AT command responses
5. Ensure `session_id` matches between manifest, commands, and chunk headers

### Verification Fails
1. Ensure complete firmware file
2. Verify no data corruption during transfer
3. Ensure CRC32 algorithm matches Pico (no final inversion)
4. For the last chunk, ensure CRC is computed on the exact bytes written (no padding)

## Configuration Files

### `/firmware/esp/main/comms/mqtt_config.h`
```c
#define CONFIG_MQTT_OTA_ENABLED 1        // Enable OTA support
#define CONFIG_MQTT_OTA_PASSTHROUGH 1    // Use pass-through mode
#define MQTT_OTA_CHUNK_SIZE 4096         // Default chunk size (matches flash sector)
#define MQTT_OTA_MAX_CHUNK_SIZE 4096     // Maximum chunk size supported
```

### Python Publisher Defaults
```python
chunk_size = 4096        # Default chunk size (matches flash sector)
pre_reboot = False       # Don't reboot before OTA
auto_boot = False        # Don't auto-boot after verification
timeout = 60             # Seconds to wait for device
```

## Technical Implementation Details

### Chunk Transfer Optimization

The OTA system uses optimized timing based on RP2040 flash characteristics:

1. **Flash Architecture:**
   - Page size: 256 bytes (minimum write)
   - Sector size: 4KB (minimum erase)
   - Block size: 64KB (block erase)
   - Chunk size: 2048 bytes (8 pages, 1/2 sector)

2. **Dynamic Delay Strategy:**
   - **First chunk**: 40-second delay for bulk sector erase (~160 sectors)
   - **Subsequent chunks**: 100ms delay (flash writes are fast after erase)
   - **Result**: ~6 chunks/second throughput after initial erase

3. **Last Chunk Handling:**
   - Publisher may pad the last chunk for transmission
   - Device writes only the actual firmware bytes (padding is ignored)
   - ESP32 recalculates CRC on the exact bytes written so Pico verification matches

### Verification Process

1. **ACK-based flow control** - Each chunk must be acknowledged before proceeding
2. **Per-chunk CRC** - Header includes CRC16 (lower 16 bits of CRC32 over transmitted bytes)
3. **Write CRC** - ESP32 sends CRC32 of the exact bytes written; Pico verifies RAM buffer and flash
4. **Final verification** - Pico computes CRC32 over the flashed app and validates header
5. **Version confirmation** - Verifies device telemetry reports expected version after reboot

### MQTT Partial Message Handling

- ESP32 reassembles fragmented MQTT payloads using current offset and total length.
- Chunks are processed only after the full payload is received; ACK is deferred until then.

### Session Consistency

- Manifest contains `session_id` (UUID string). The first 8 hex chars are embedded in chunk headers.
- Commands include `session_id`; the device validates manifest, commands, and chunk headers match.
- Mismatched session IDs are rejected to prevent mixing transfers.

### Chunk Header Format

Big-endian header (16 bytes):

1. `uint32` session_id (first 8 chars of UUID)
2. `uint32` chunk_index
3. `uint16` chunk_size (bytes transmitted for this chunk)
4. `uint16` crc16 (lower 16 bits of CRC32 over transmitted bytes)
5. `uint32` flags (reserved)

## Security Considerations

1. **Use TLS when possible** - Encrypt firmware in transit
2. **Implement authentication** - Use MQTT username/password
3. **Verify firmware signatures** - Implement signing (future enhancement)
4. **Network isolation** - Use separate MQTT topics/broker for OTA
5. **Rate limiting** - Implement chunk rate limiting to prevent DoS

## Example Session

```bash
$ python3 mqtt_ota_publisher.py --broker localhost --device bee0003a59b3356e \
    --pre-reboot --auto-boot --version 0.8.4 firmware.ota

Logging to: ota_bee0003a59b3356e_v0_8_4_20241218_150320.log
=== OTA Update Log ===
Timestamp: 2025-12-18T15:03:20
Device: bee0003a59b3356e
Firmware: firmware.ota
Broker: localhost:1883
Version: 0.8.4
==================================================

Connecting to localhost:1883...
Connected to localhost:1883
Subscribed to bee0003a59b3356e/ota/status/state
Subscribed to bee0003a59b3356e/ota/status/progress
Subscribed to bee0003a59b3356e/ota/status/ack/+
Subscribed to bee0003a59b3356e/telemetry
Checking device connectivity...
✓ Device is online
Rebooting device to clean state...
Waiting for device to come back online (up to 90s)...
✓ Device back online after reboot
Loaded firmware: firmware.ota
  Size: 4,915,580 bytes
  Chunks: 2399 x 2048 bytes
Publishing manifest for version 0.8.4
Waiting for device to process manifest...
Sending command: START
Waiting for device to start download...
Device state: DOWNLOADING
Publishing 2399 chunks with enhanced ACK-based flow control...
Chunk size: 2048 bytes (matching flash sector size)
    Note: Using dynamic delays based on flash erase requirements
    - First chunk: 40s delay for bulk erase
    - After erase completes: 100ms per chunk
    Waiting 40s for device to erase all sectors...
Progress: 100/2399 chunks sent (4.2%) Current: 9.8 chunks/s, ETA: 234.2s
  Last chunk 2398: 1921 actual bytes, padded to 2048 for transmission
    Note: Manifest size is 4915580 bytes (actual firmware)
Progress: 2399/2399 chunks sent (100.0%) Current: 10.0 chunks/s, ETA: 0.0s

🔍 Performing final verification...
✓ All 2399 chunks successfully sent and acknowledged!

Waiting for device to complete transfer and auto-verify...
Waiting for device to verify firmware...
Device state: READY_TO_BOOT
Firmware verified successfully!
Device rebooting with new firmware...

Waiting for device to reboot (device will go offline)...
Waiting for device to come back online after reboot (up to 120s)...
✅ Device successfully rebooted and is back online!
Device firmware version: 0.8.4
✅ Firmware version confirmed: 0.8.4

✓ OTA update completed successfully!

=== End of Log ===
Timestamp: 2025-12-18T15:08:45
```
