# ADSBee MQTT Integration

Stream real-time ADS-B data from both 1090 MHz and 978 MHz (UAT) to any MQTT broker with support for both JSON and binary formats. Now includes device telemetry, GPS position, and enhanced aircraft information.

## Quick Start

### Basic Setup (JSON Format)
```bash
# Configure MQTT feed
AT+FEEDPROTOCOL=0,MQTT
AT+FEEDURI=0,mqtt.broker.com
AT+FEEDPORT=0,1883
AT+FEEDEN=0,1
AT+SETTINGS=SAVE
```

### Cellular/IoT Setup (Binary Format)
```bash
# Same as above, but use binary format for 90% bandwidth savings
AT+FEEDPROTOCOL=0,MQTT
AT+FEEDURI=0,mqtt.broker.com
AT+FEEDPORT=0,1883
AT+MQTTFORMAT=0,BINARY
AT+FEEDEN=0,1
AT+SETTINGS=SAVE
```

### Raw-Only Feed (for external decoders)
```bash
# Only publish raw hex packets, no decoded aircraft status
AT+FEEDPROTOCOL=0,MQTT
AT+FEEDURI=0,mqtt.broker.com
AT+FEEDPORT=0,1883
AT+MQTTCONTENT=0,RAW
AT+FEEDEN=0,1
AT+SETTINGS=SAVE
```

### Decoded-Only Feed (human-readable)
```bash
# Only publish decoded aircraft status, no raw packets
AT+FEEDPROTOCOL=0,MQTT
AT+FEEDURI=0,mqtt.broker.com
AT+FEEDPORT=0,1883
AT+MQTTCONTENT=0,STATUS
AT+FEEDEN=0,1
AT+SETTINGS=SAVE
```

## Message Formats

### JSON Format (Default)
Human-readable, ~250 bytes per message. Best for WiFi/Ethernet. Published at a steady 1 Hz per aircraft with low latency.

**Aircraft Status** (published every 5s, only for aircraft with new decodes):
```json
{
  "t": 123456,       // Timestamp (ms since boot) of last decode
  "icao": "A12345",
  "band": "1090",    // "1090" or "UAT"
  "call": "UAL123",
  "cat": "A3",       // ADS-B category code (see category reference below)
  "lat": 37.7749,
  "lon": -122.4194,
  "alt": 35000,
  "hdg": 270,
  "spd": 485,
  "vr": 0,
  "sqk": "1200",
  "gnd": 0
}
```

**Device Telemetry** (published every 60s):
```json
{
  "uptime": 3600,        // Seconds
  "msgs_adsb_ps": 42,   // ADS-B messages per second
  "msgs_mqtt_tx": 567,  // MQTT messages sent (cumulative)
  "esp_temp": 45,        // ESP32 CPU temperature (Celsius)
  "pico_temp": 40,       // RP2040 CPU temperature (Celsius)
  "pico_cpu": [12, 8],   // RP2040 core 0 and core 1 usage (%)
  "aircraft": 23,        // Number of currently tracked aircraft
  "mem_free": 2048,      // Free memory (KB)
  "noise_floor": -45,    // RF noise floor (dBm)
  "rx_1090": 1,          // 1090 MHz receiver enabled
  "rx_978": 1,           // 978 MHz receiver enabled
  "wifi": 1,             // WiFi connected
  "mqtt": 1,             // MQTT connected
  "fw_ver": "0.9.0",     // Firmware version
  "mps_total": 42,       // Total messages per second (all feeds)
  "mps": [42, 0, 0]      // Per-feed messages per second
}
```

**GPS Position:**
```json
{
  "lat": 37.7749,        // Receiver latitude
  "lon": -122.4194,      // Receiver longitude
  "alt": 100.5,          // Altitude (meters)
  "fix": "3D",           // Fix type: None, 2D, 3D
  "sats": 12,            // Number of satellites
  "hdop": 0.9,           // Horizontal dilution
  "ts": 1234567890       // Timestamp
}
```

Topics (with device ID for multi-device deployments):
- 1090 MHz raw: `{device_id}/adsb/{ICAO}/raw`
- 1090 MHz status: `{device_id}/adsb/{ICAO}/status`
- 978 MHz raw: `{device_id}/uat/{ICAO}/raw`
- 978 MHz status: `{device_id}/uat/{ICAO}/status`
- Telemetry: `{device_id}/system/telemetry`
- GPS: `{device_id}/system/gps`

Example with device ID `a1b2c3d4e5f67890`:
- Raw packet: `a1b2c3d4e5f67890/adsb/A12345/raw`
- Aircraft status: `a1b2c3d4e5f67890/adsb/A12345/status`
- Telemetry: `a1b2c3d4e5f67890/system/telemetry`

### Binary Format
Compact messages for bandwidth-limited connections. Binary status is also published at a steady 1 Hz per aircraft, with the shortest possible end-to-end latency.

- Aircraft: 31 bytes (includes category & callsign)
- Telemetry: 16 bytes
- GPS: 15 bytes
- Same real-time delivery
- Includes band identification
- Ideal for cellular IoT, satellite, LoRaWAN

Topics (shortened for additional savings):
- 1090 MHz: `{device_id}/a/{ICAO}/s` 
- 978 MHz UAT: `{device_id}/u/{ICAO}/s`
- Telemetry: `{device_id}/sys/t`
- GPS: `{device_id}/sys/g`

Example with device ID `a1b2c3d4e5f67890`:
- Aircraft: `a1b2c3d4e5f67890/a/A12345/s`
- Telemetry: `a1b2c3d4e5f67890/sys/t`

## Configuration Commands

### Set Output Format
```bash
AT+MQTTFORMAT=<feed>,<format>

# Examples:
AT+MQTTFORMAT=0,JSON     # Human-readable (~250 bytes/msg)
AT+MQTTFORMAT=0,BINARY   # Bandwidth-optimized (~20 bytes/msg)
```

### Set Content Mode
Controls which message types are published on each feed:
```bash
AT+MQTTCONTENT=<feed>,<mode>

# Examples:
AT+MQTTCONTENT=0,ALL      # Both raw packets and decoded status (default)
AT+MQTTCONTENT=0,RAW      # Raw hex packets only (for external decoders)
AT+MQTTCONTENT=0,STATUS   # Decoded aircraft status only (human-readable)
```

Telemetry is always published regardless of content mode.

### Enable OTA via MQTT
```bash
AT+MQTTOTA=<feed>,<0|1>

# Examples:
AT+MQTTOTA=0,1    # Enable OTA updates on feed 0
AT+MQTTOTA=0,0    # Disable OTA on feed 0 (default)
```

### Query Settings
```bash
AT+MQTTFORMAT?    # Show format for all feeds
AT+MQTTCONTENT?   # Show content mode for all feeds
AT+FEEDPROTOCOL?  # Show protocol settings
AT+FEEDURI?       # Show broker address
```

## Dual-Band Support

ADSBee supports both frequency bands used for ADS-B:

### 1090 MHz (Mode S / ADS-B)
- International standard
- Commercial aviation
- All aircraft above 18,000 ft
- Topics prefix: `adsb/` (JSON) or `a/` (binary)

### 978 MHz (UAT)  
- US-specific below 18,000 ft
- General aviation
- Weather (FIS-B) and traffic (TIS-B) uplinks
- Topics prefix: `uat/` (JSON) or `u/` (binary)

Messages automatically include band identification so you can:
- Filter by frequency band
- Track coverage gaps
- Identify aircraft type (commercial vs GA)
- Separate traffic for different applications

## ADS-B Category Codes

Aircraft transmit standardized category codes in format `XN` where X is a letter (A-D) and N is a number (0-7). These codes help identify aircraft size, type, and wake turbulence category.

### Category A - Airborne
- **A0** - No ADS-B emitter category information
- **A1** - Light (< 15,500 lbs / 7,000 kg) - *Cessna 172, Piper Cherokee*
- **A2** - Small (15,500 - 75,000 lbs) - *Regional jets, business jets*
- **A3** - Large (75,000 - 300,000 lbs) - *Boeing 737, Airbus A320*
- **A4** - High vortex large - *Boeing 757*
- **A5** - Heavy (> 300,000 lbs / 136,000 kg) - *Boeing 777/787, Airbus A350*
- **A6** - High performance (> 5g & > 400 kts) - *Military fighters*
- **A7** - Rotorcraft - *Helicopters*

### Category B - Airborne/Surface
- **B0** - No ADS-B emitter category information
- **B1** - Glider/sailplane
- **B2** - Lighter-than-air - *Balloons, airships*
- **B3** - Parachutist/skydiver
- **B4** - Ultralight/hang-glider/paraglider
- **B5** - Reserved
- **B6** - Unmanned aerial vehicle (UAV/drone)
- **B7** - Space/trans-atmospheric vehicle

### Category C - Surface Vehicles
- **C0** - No ADS-B emitter category information
- **C1** - Surface vehicle - emergency - *Fire trucks, ambulances*
- **C2** - Surface vehicle - service - *Ground support, tugs*
- **C3** - Point obstacle (includes tethered balloons)
- **C4** - Cluster obstacle
- **C5** - Line obstacle
- **C6** - Reserved
- **C7** - Reserved

### Category D - Reserved
- **D0-D7** - Reserved for future use

### Interpreting Category Codes
The category code provides critical safety information:
- **Wake turbulence** - A4/A5 aircraft generate significant wake
- **Runway requirements** - A1 can use short runways, A5 needs long runways
- **Approach speeds** - A1 ~70 kts, A3 ~140 kts, A5 ~150 kts
- **Ground operations** - C1/C2 vehicles on taxiways/runways


## MQTT Broker Setup

### Mosquitto (Testing)
```bash
# Install
sudo apt install mosquitto mosquitto-clients

# Subscribe to all aircraft status from all devices
mosquitto_sub -h localhost -t "+/adsb/+/status" -v

# Subscribe to all raw packets from all devices
mosquitto_sub -h localhost -t "+/adsb/+/raw" -v

# Subscribe to everything from a specific device
mosquitto_sub -h localhost -t "a1b2c3d4e5f67890/#" -v

# Subscribe to all telemetry
mosquitto_sub -h localhost -t "+/system/telemetry" -v

# Binary format (if using short topics)
mosquitto_sub -h localhost -t "+/a/+/s" -v
mosquitto_sub -h localhost -t "+/a/+/r" -v
```

### Python Client
```python
import paho.mqtt.client as mqtt
import json
import struct

def on_message(client, userdata, message):
    # Handle aircraft messages
    if message.topic.startswith(("adsb/", "uat/")):
        # JSON format
        data = json.loads(message.payload)
        band = data.get('band', '1090')
        cat_code = data.get('cat', 'A0')
        
        # Interpret category code
        cat_desc = {
            'A1': 'Light', 'A2': 'Small', 'A3': 'Large', 
            'A4': 'High Vortex', 'A5': 'Heavy', 'A6': 'High Perf',
            'A7': 'Rotorcraft', 'B1': 'Glider', 'B2': 'Balloon',
            'B6': 'UAV', 'C1': 'Emergency', 'C2': 'Service'
        }.get(cat_code, 'Unknown')
        
        print(f"[{band}] {cat_code}/{cat_desc} {data['icao']} ({data['call']}) at {data['alt']} ft")
        
    elif message.topic.startswith(("a/", "u/")):
        # Binary format
        msg_type = message.payload[0]
        if msg_type == 0x02:  # Aircraft message
            band_bits = message.payload[1] >> 6  # Band in upper 2 bits
            band = "UAT" if band_bits == 1 else "1090"
            icao = int.from_bytes(message.payload[1:4], 'big') & 0xFFFFFF
            cat_raw = message.payload[21]  # Category byte
            
            # Decode category code from raw byte
            ca = (cat_raw >> 5) & 0x07  # Upper 3 bits
            typ = cat_raw & 0x1F         # Lower 5 bits
            letter = chr(ord('A') + (ca & 0x03))  # Map to A-D
            cat_code = f"{letter}{typ}"
            
            callsign = message.payload[22:30].decode('utf-8').strip('\x00')
            print(f"[{band}] {cat_code} {icao:06X} ({callsign})")
            
    # Handle telemetry
    elif "system/telemetry" in message.topic:
        data = json.loads(message.payload)
        print(f"Device: uptime={data['uptime']}s, aircraft={data.get('aircraft',0)}, "
              f"esp={data['esp_temp']}C, pico={data.get('pico_temp',0)}C, "
              f"fw={data.get('fw_ver','?')}")
        
    # Handle GPS
    elif message.topic == "system/gps":
        data = json.loads(message.payload)
        print(f"GPS: {data['lat']}, {data['lon']} ({data['sats']} sats, {data['fix']} fix)")

client = mqtt.Client()
client.on_message = on_message
client.connect("localhost", 1883)

# Subscribe to all topics from all devices
client.subscribe("+/adsb/+/status")     # 1090 MHz JSON from any device
client.subscribe("+/uat/+/status")      # UAT JSON from any device
client.subscribe("+/system/telemetry")  # Device telemetry from any device
client.subscribe("+/system/gps")        # GPS position from any device

# Or subscribe to specific device
device_id = "a1b2c3d4e5f67890"
client.subscribe(f"{device_id}/adsb/+/status")     # 1090 MHz JSON
client.subscribe(f"{device_id}/system/telemetry")  # Telemetry
client.subscribe(f"{device_id}/system/gps")        # GPS

client.loop_forever()
```

## Multiple Feeds

Configure up to 10 simultaneous feeds (shared with non-MQTT protocols):

```bash
# Feed 0: Local broker - full JSON (raw + status)
AT+FEEDPROTOCOL=0,MQTT
AT+FEEDURI=0,192.168.1.100
AT+MQTTFORMAT=0,JSON
AT+MQTTCONTENT=0,ALL

# Feed 1: Cloud broker - binary decoded status only (low bandwidth)
AT+FEEDPROTOCOL=1,MQTT
AT+FEEDURI=1,cloud.mqtt.com
AT+MQTTFORMAT=1,BINARY
AT+MQTTCONTENT=1,STATUS

# Feed 2: Raw feed for external decoder
AT+FEEDPROTOCOL=2,MQTT
AT+FEEDURI=2,decoder.local
AT+MQTTCONTENT=2,RAW

# Enable all three
AT+FEEDEN=0,1
AT+FEEDEN=1,1
AT+FEEDEN=2,1
AT+SETTINGS=SAVE
```

## Authentication

Include credentials in the URI:
```bash
AT+FEEDURI=0,username:password@mqtt.broker.com
```

## TLS/SSL

Use port 8883 for secure connections:
```bash
AT+FEEDPORT=0,8883
```

## Troubleshooting

**No messages received:**
- Check WiFi connection: `AT+WIFISTATUS`
- Verify feed enabled: `AT+FEEDEN?`
- Verify protocol is MQTT: `AT+FEEDPROTOCOL?`
- Check content mode: `AT+MQTTCONTENT?` (default `ALL` publishes both raw and status)
- Check broker logs for connection attempts

**Only raw or only status messages:**
- Check content mode: `AT+MQTTCONTENT?`
- Set to ALL for both: `AT+MQTTCONTENT=0,ALL`

**High bandwidth usage:**
- Switch to binary format: `AT+MQTTFORMAT=0,BINARY`
- Use STATUS-only mode: `AT+MQTTCONTENT=0,STATUS` (skips high-volume raw packets)
- Verify with: `AT+MQTTFORMAT?` and `AT+MQTTCONTENT?`

## Multi-Device Management

Each ADSBee device has a unique 16-character hex ID (derived from the receiver ID) that appears in all topic paths. This enables:

- **Device Filtering**: Subscribe to specific devices or all devices
- **Coverage Mapping**: Know which device saw which aircraft
- **Health Monitoring**: Track per-device telemetry and status
- **Fault Isolation**: Identify problematic devices

### Device ID Format
The device ID is the 8-byte receiver ID converted to hex (16 characters):
- Example: `a1b2c3d4e5f67890`
- Set via AT command or automatically generated
- Consistent across all messages from that device

## Telemetry Monitoring

Monitor your ADSBee health and performance:

```bash
# Subscribe to telemetry from all devices
mosquitto_sub -h localhost -t "+/system/telemetry" -v

# Subscribe to specific device
mosquitto_sub -h localhost -t "a1b2c3d4e5f67890/system/telemetry" -v

# Subscribe to GPS from all devices
mosquitto_sub -h localhost -t "+/system/gps" -v
```

## Support

- GitHub: https://github.com/CoolNamesAllTaken/adsbee
- Website: https://pantsforbirds.com/adsbee-1090