import serial
import time
import re
import asyncio
import websocket
import zlib # For CRC32 calculation.

class ADSBeeAT:
    MS_PER_SEC = 1000

    def __init__(self, serial_port_or_ip, serial_timeout_sec=1):
        self.ws_ip = None
        self.ws = None
        self.ser = None
        self.serial_timeout_sec = serial_timeout_sec
        self.last_cmd_timestamp = time.time()
        # Check whether an IP address was provided.
        if re.match(r"^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$", serial_port_or_ip):
            self.ws_ip = serial_port_or_ip
        else:
            self.ser = serial.Serial(serial_port_or_ip, baudrate = 115200, timeout=self.serial_timeout_sec)

    def __enter__(self):
        self.enter_timestamp = time.time()
        if self.ws_ip:
            self.ws = websocket.create_connection(
                f"ws://{self.ws_ip}/console",
                timeout=self.serial_timeout_sec
            )
        else:
            self.ser.close()
            self.ser.open()
        time.sleep(0.1)
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        if self.ws:
            self.ws.close()
        else:
            self.ser.close()
    
    def get_ms_timestamp(self):
        """
        Gets the current timestamp in milliseconds since the object was created. Used for logging during file uploads.
        @retval The timestamp in milliseconds.
        """
        return int((time.time() - self.enter_timestamp) * self.MS_PER_SEC)
    
    def flush_input_buffer(self):
        """
        Gets rid of any pending input in the serial port or WebSocket input buffer. Used to avoid triggering on stale
        responses from the ADSBee.
        """
        WS_FLUSH_TIMEOUT = 0.01
        if self.ser:
            self.ser.reset_input_buffer()
        else:
            while True:
                # Keep receiving with a very short timeout until we get a timeout
                self.ws.settimeout(WS_FLUSH_TIMEOUT)
                try:
                    _ = self.ws.recv_data()
                except websocket.WebSocketTimeoutException:
                    break

    def receive_response(self, print_response=False, wait_for_ok_or_error=False):
        """
        Blocking function that records responses from the ADSBee until an "OK" or "ERROR" is received, or until the
        input buffer is empty.
        @param[in] print_response: Whether to print the response strings.
        @param[in] wait_for_ok_or_error: Whether to wait for an "OK" or "ERROR" response before returning.
        @retval A list of decoded response strings.
        """
        decoded_response = []
        while True:
            raw = None
            if self.ws:
                # In WebSocket mode.
                self.ws.settimeout(0.1)
                try:
                    opcode, payload = self.ws.recv_data() # Opcode is discarded.
                    raw = payload
                except websocket.WebSocketTimeoutException:
                    if wait_for_ok_or_error:
                        # Didn't receive anything, but still waiting for OK or ERROR.
                        continue
                    else:
                        # No pending input on the WebSocket, and not blocking for OK or ERROR.
                        break
            else:
                # In serial port mode.
                if self.ser.in_waiting or wait_for_ok_or_error:
                    raw = self.ser.readline()
                else:
                    # No pending input on the serial port, and not blocking for OK or ERROR.
                    break
            if wait_for_ok_or_error:
                if b"OK" in raw:
                    # Release from blocking wait if OK or ERROR is received.
                    # print("OK or ERROR received.")
                    wait_for_ok_or_error = False
                elif b"ERROR" in raw:
                    raise Exception(f"ERROR response: \t\t{raw}")
            log_str = ""
            try:
                decoded_response.append(raw.decode('utf-8').strip())
                log_str = f"Response (+{self.get_ms_timestamp() - self.last_cmd_timestamp} ms): \t\t{decoded_response[-1]}"
            except:
                log_str = f"Non-ASCII response: \t{raw}"
            if (print_response):
                print(log_str)
        return decoded_response

    def send_cmd(self, cmd_str, delay=0.01, print_response=False, wait_for_ok_or_error=False):
        """
        Sends a command to the ADSBee and returns the response as a list of ASCII strings. All strings that fail to decode to ASCII are ignored.
        @param[in] cmd_str: The command string to send.
        @param[in] delay: The delay in seconds to wait after sending the command.
        @param[in] print_response: Whether to print the response strings.
        @param[in] wait_for_ok_or_error: Whether to wait for an "OK" or "ERROR" response before returning.
        @return A list of decoded response strings.
        """
        self.flush_input_buffer() # Dump all pending incoming messages to avoid triggering on stale OK or ERROR.
        self.last_cmd_timestamp = self.get_ms_timestamp()
        if (print_response):
            print(f"Command ({self.get_ms_timestamp()} ms): \t{cmd_str.strip()}") # Remove line ending to avoid double newline.
        if self.ser:
            self.ser.write(cmd_str.encode('ascii'))
        else:
            self.ws.send_binary(cmd_str)
        time.sleep(delay)
        return self.receive_response(print_response=print_response, wait_for_ok_or_error=wait_for_ok_or_error)
    
    def send_bytes(self, data, print_response=False, wait_for_ok_or_error=False):
        """
        Sends raw bytes to the ADSBee and returns the response as a list of ASCII strings. All strings that fail to decode to ASCII are ignored.
        @param[in] print_response: Whether to print the response strings.
        @param[in] wait_for_ok_or_error: Whether to wait for an "OK" or "ERROR" response before returning.
        @return A list of decoded response strings.
        """
        self.flush_input_buffer()
        if self.ser:
            self.ser.write(data)
        else:
            self.ws.send_binary(data)
        return self.receive_response(print_response=print_response, wait_for_ok_or_error=wait_for_ok_or_error)
    
    def silence_console(self):
        """
        Silences the console output of the ADSBee to allow interaction without extra prints due to informational, 
        warning, or error logs.
        """
        # Silence the console to allow programming.
        self.send_cmd(f"AT+LOG_LEVEL=SILENT\r\n")
        self.send_cmd(f"AT+PROTOCOL=CONSOLE,NONE\r\n")

    def get_mac_address(self):
        """
        Returns the MAC address of the ADSBee's ESP32 as a string.
        @retval The MAC address as a string.
        """
        self.silence_console()
        decoded_response = self.send_cmd(f"AT+DEVICE_INFO?\r\n")
        for line in decoded_response:
            match = re.search(r"ESP32 Base MAC Address: ([0-9A-Fa-f:]+)", line)
            if match:
                mac_address = match.group(1)
                # print(f"ESP32 Base MAC Address: {mac_address}")
                self.ser.flush() # Dump the rest of the device info data that we don't need.
                return mac_address
        return None

    def write_device_info(self, device_info_passcode, device_info_version, serial_label_str, ota_keys):
        """
        Writes the device info for an ADSBee. Used for manufacturing.
        @param[in] device_info_passcode: The device info passcode.
        @param[in] device_info_version: The device info version.
        @param[in] serial_label_str: The serial label string.
        @param[in] ota_keys: A list of OTA keys.
        """
        self.silence_console()
        ota_keys_str = ','.join([key for key in ota_keys])
        self.send_cmd(f"AT+DEVICE_INFO={device_info_passcode},{device_info_version},{serial_label_str},{ota_keys_str}\r\n")
        # Reset and save settings to generate default WiFi AP names, receiver UID, etc.
        self.send_cmd(f"AT+SETTINGS=RESET\r\n")
        self.send_cmd(f"AT+SETTINGS=SAVE\r\n")
        time.sleep(1) # Saving settings takes a while due to EEPROM write.
        # Reboot ESP32 to allow it to load new settings.
        self.send_cmd(f"AT+ESP32_ENABLE=0\r\n", delay=0.2)
        self.send_cmd(f"AT+ESP32_ENABLE=1\r\n", delay=0.5) # Let ESP32 boot up.
        self.silence_console()
        self.send_cmd(f"AT+DEVICE_INFO?\r\n", delay=0.5)

    def read_device_info(self, print_info=False):
        """
        Reads back the device information from an ADSBee, and returns it as a dictionary.
        @param[in] print_info: Whether to print the device information.
        @retval A dictionary with the device information.
        """
        device_info = {
            'ota_keys': [],
            'part_code': "",
            'rp2040_firmware_version': "", 
            'esp32_firmware_version': "",
            'mac_address': ""
        }
        self.silence_console()
        decoded_response = self.send_cmd(f"AT+DEVICE_INFO?\r\n")
        for line in decoded_response:
            part_code_match = re.search(r"Part Code: (.+)", line)
            rp2040_firmware_version_match = re.search(r"RP2040 Firmware Version: (.+)", line)
            ota_key_match = re.search(r"OTA Key \d+: (.+)", line)
            esp32_firmware_version_match = re.search(r"ESP32 Firmware Version: (.+)", line)
            mac_address_match = re.search(r"ESP32 Base MAC Address: (.+)", line)

            if part_code_match:
                device_info['part_code'] = part_code_match.group(1)
                if print_info:
                    print(f"\tPart Code: {device_info['part_code']}")
            elif rp2040_firmware_version_match:
                device_info['rp2040_firmware_version'] = rp2040_firmware_version_match.group(1)
                if print_info:
                    print(f"\tRP2040 Firmware Version: {device_info['rp2040_firmware_version']}")
            elif ota_key_match:
                device_info['ota_keys'].append(ota_key_match.group(1))
                if print_info:
                    print(f"\tOTA Key {len(device_info['ota_keys'])-1}: {device_info['ota_keys'][-1]}")
            elif esp32_firmware_version_match:
                device_info['esp32_firmware_version'] = esp32_firmware_version_match.group(1)
                if print_info:
                    print(f"\tESP32 Firmware Version: {device_info['esp32_firmware_version']}")
            elif mac_address_match:
                device_info['mac_address'] = mac_address_match.group(1)
                if print_info:
                    print(f"\tESP32 Base MAC Address: {device_info['mac_address']}")
            else:
                pass # Not interested in other fields.
        return device_info

    def ota_get_flash_partition(self) -> int | None:
        """
        Query the ADSBee for the OTA flash partition that can be written to.
        @retval The partition index that can be written to (0 or 1), or None if no partition is available.
        """
        self.silence_console()
        decoded_response = self.send_cmd(f"AT+OTA=GET_PARTITION\r\n", print_response=True, wait_for_ok_or_error=True)
        for line in decoded_response:
            match = re.search(r"Partition: (\d+)", line)
            if match:
                partition = int(match.group(1))
                # print(f"Partition: {partition}")
                return partition
        return None
    
    def ota_write_bytes(self, offset, data):
        """
        Writes a chunk of data to the ADSBee's OTA partition.
        @param[in] offset: The offset in bytes to write the data to.
        @param[in] data: The data to write, as a bytearray.
        """
        crc32 = zlib.crc32(data) & 0xFFFFFFFF
        self.send_cmd(f"AT+OTA=WRITE,{offset:x},{len(data)},{crc32:x}\r\n", print_response=True)
        self.send_bytes(data, print_response=True, wait_for_ok_or_error=True)

    def ota_erase(self):
        """
        Erases the writable OTA partition on the ADSBee.
        """
        self.silence_console()
        self.send_cmd(f"AT+OTA=ERASE\r\n", print_response=True, wait_for_ok_or_error=True)
    
    def ota_write_file(self, ota_filename):
        """
        Update an ADSBee over the air with a new firmware image. The firmware image must be baked into the .ota file
        format used by the ADSBee.
        @param[in] ota_filename: The filename of the .ota file to write.
        """
        HEADER_SIZE_BYTES = 5*4
        APP_OFFSET_BYTES = 4 * 1024
        FLASH_PAGE_SIZE_BYTES = 256
        WRITE_CHUNK_BYTES = 3840*4 # Needs to be multiple of sector size 256 Bytes.

        self.silence_console()
        partition = self.ota_get_flash_partition()
        if partition is None:
            raise Exception("Failed to get OTA partition from ADSBee.")
        with open(ota_filename, 'rb') as f:
            contents = f.read()
            num_partitions = int.from_bytes(contents[0:4], byteorder='little')
            if partition > num_partitions:
                raise Exception(f"Partition {partition} is out of range. Only {num_partitions} partitions available.")
            offset = int.from_bytes(contents[4 + 4*partition:4 + 4*(partition+1)], byteorder='little')

            contents = contents[offset:]
            header_contents = contents[:HEADER_SIZE_BYTES]

            # Write the header.
            self.ota_write_bytes(0, header_contents)

            # Write the application in chunks.
            app_len_bytes = int.from_bytes(header_contents[8:12], byteorder='little')
            for i in range(HEADER_SIZE_BYTES, app_len_bytes, WRITE_CHUNK_BYTES):
                offset_bytes = (i - HEADER_SIZE_BYTES) + APP_OFFSET_BYTES
                self.ota_write_bytes(offset_bytes, contents[i:i+WRITE_CHUNK_BYTES])
            # self.ota_write_bytes(HEADER_SIZE_BYTES, contents[HEADER_SIZE_BYTES:])

            # Verify and boot the new partition.
            self.send_cmd(f"AT+OTA=VERIFY\r\n", print_response=True, wait_for_ok_or_error=True)
    
    def ota_boot(self):
        self.send_cmd(f"AT+OTA=BOOT\r\n", print_response=True)

