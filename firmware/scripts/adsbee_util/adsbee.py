import serial
import re
import time

RE_PATTERN_FLOAT = r"-?\d+\.\d+"

def print_line_or_dot(line: str):
    if len(line) == 0:
        print(".", end="", flush=True)
    else:
        print(line, flush=True)

class ADSBee:
    def __init__(self, serial_port: str, baud_rate: int = 115200, timeout: int = 1):
        self.serial_port = serial_port
        self.baud_rate = baud_rate
        self.timeout = timeout

    def __enter__(self):
        print(f"Opening serial port {self.serial_port} with baudrate {self.baud_rate}.")
        self.ser = serial.Serial(self.serial_port, self.baud_rate, timeout=self.timeout)
        self.flush()
        return self

    def __exit__(self, exception_type, exception_value, traceback):
        self.ser.close()

    def write(self, string: str):
        print(string)
        self.ser.write(string.encode("ascii"))

    def flush(self):
        self.ser.reset_input_buffer()

    def wait_for_match(self, pattern: str, timeout_sec: int = 10) -> re.match:
        """
        Read lines from the serial port until we get something that matches, or we timeout.
        :param pattern: Regex pattern to match on.
        :param timeout_sec: Timeout in seconds.
        :return: Matched regex pattern. Extract groups with match.group(n), where n is the group number.
        """
        start_timestamp_sec = time.time()
        line: str = self.ser.readline().decode("utf-8")
        print_line_or_dot(line)
        match = re.match(pattern, line)
        while not match and time.time() - start_timestamp_sec < timeout_sec:
            line: str = self.ser.readline().decode("utf-8")
            print_line_or_dot(line)
            match = re.match(pattern, line)
        return match

    def wait_for_ok(self):
        """
        Helper function that waits for an OK over the AT interface.
        :return:
        """
        self.wait_for_match(r"^OK\r\n$")