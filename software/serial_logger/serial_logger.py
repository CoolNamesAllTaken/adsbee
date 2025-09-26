#!/usr/bin/env python3
"""
Serial Port Logger with Auto-Reconnect
Connects to a serial port, logs output to timestamped files,
and automatically reconnects if the connection drops.
"""

import serial
import time
import datetime
import os
import sys
import signal
import argparse
from pathlib import Path

class SerialLogger:
    def __init__(self, port, baudrate=9600, timeout=1, log_dir="serial_logs", reconnect_delay=5):
        self.port = port
        self.baudrate = baudrate
        self.timeout = timeout
        self.log_dir = Path(log_dir)
        self.reconnect_delay = reconnect_delay
        self.serial_conn = None
        self.log_file = None
        self.running = True
        
        # Create log directory if it doesn't exist
        self.log_dir.mkdir(exist_ok=True)
        
        # Set up signal handler for graceful shutdown
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)
    
    def _signal_handler(self, signum, frame):
        """Handle shutdown signals gracefully"""
        print(f"\nReceived signal {signum}, shutting down...")
        self.running = False
    
    def _get_log_filename(self):
        """Generate a timestamped log filename"""
        timestamp = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
        return self.log_dir / f"serial_log_{timestamp}.txt"
    
    def _open_log_file(self):
        """Open a new log file with current timestamp"""
        if self.log_file:
            self.log_file.close()
        
        log_filename = self._get_log_filename()
        self.log_file = open(log_filename, 'w', buffering=1)  # Line buffered
        
        # Write header to log file
        header = f"Serial Port Logger - Started at {datetime.datetime.now()}\n"
        header += f"Port: {self.port}, Baudrate: {self.baudrate}\n"
        header += "-" * 50 + "\n"
        self.log_file.write(header)
        
        print(f"Logging to: {log_filename}")
        return log_filename
    
    def _connect_serial(self):
        """Attempt to connect to the serial port"""
        try:
            if self.serial_conn and self.serial_conn.is_open:
                self.serial_conn.close()
            
            self.serial_conn = serial.Serial(
                port=self.port,
                baudrate=self.baudrate,
                timeout=self.timeout,
                bytesize=serial.EIGHTBITS,
                parity=serial.PARITY_NONE,
                stopbits=serial.STOPBITS_ONE
            )
            
            print(f"Connected to {self.port} at {self.baudrate} baud")
            return True
            
        except serial.SerialException as e:
            print(f"Failed to connect to {self.port}: {e}")
            return False
        except Exception as e:
            print(f"Unexpected error connecting to serial port: {e}")
            return False
    
    def _log_message(self, message):
        """Write message to log file with timestamp"""
        timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
        log_entry = f"[{timestamp}] {message}\n"
        
        if self.log_file:
            self.log_file.write(log_entry)
        
        # Also print to console
        print(f"{timestamp}: {message.strip()}")
    
    def _read_serial_data(self):
        """Read data from serial port"""
        try:
            if self.serial_conn.in_waiting > 0:
                data = self.serial_conn.readline()
                if data:
                    # Decode bytes to string, handling encoding errors gracefully
                    try:
                        decoded_data = data.decode('utf-8', errors='replace').strip()
                    except UnicodeDecodeError:
                        decoded_data = data.decode('ascii', errors='replace').strip()
                    
                    if decoded_data:  # Only log non-empty lines
                        self._log_message(decoded_data)
                        return True
            return True
            
        except serial.SerialException:
            print("Serial connection lost")
            return False
        except Exception as e:
            print(f"Error reading serial data: {e}")
            return False
    
    def run(self):
        """Main logging loop"""
        print(f"Starting serial logger for port {self.port}")
        
        while self.running:
            # Attempt to connect to serial port
            if not self._connect_serial():
                print(f"Retrying connection in {self.reconnect_delay} seconds...")
                time.sleep(self.reconnect_delay)
                continue
            
            # Open new log file for this connection session
            log_filename = self._open_log_file()
            self._log_message("=== Connection established ===")
            
            # Main data reading loop
            connection_active = True
            while self.running and connection_active:
                try:
                    connection_active = self._read_serial_data()
                    
                    if connection_active:
                        time.sleep(0.01)  # Small delay to prevent excessive CPU usage
                    
                except KeyboardInterrupt:
                    print("\nInterrupted by user")
                    self.running = False
                    break
            
            # Connection lost or interrupted
            if self.running:  # Only log disconnection if we're not shutting down
                self._log_message("=== Connection lost ===")
                print(f"Connection lost. Reconnecting in {self.reconnect_delay} seconds...")
                time.sleep(self.reconnect_delay)
        
        # Cleanup
        self._cleanup()
    
    def _cleanup(self):
        """Clean up resources"""
        if self.log_file:
            self._log_message("=== Logging stopped ===")
            self.log_file.close()
            self.log_file = None
        
        if self.serial_conn and self.serial_conn.is_open:
            self.serial_conn.close()
            self.serial_conn = None
        
        print("Serial logger stopped")

def main():
    parser = argparse.ArgumentParser(description="Serial Port Logger with Auto-Reconnect")
    parser.add_argument("port", help="Serial port (e.g., /dev/ttyUSB0, /dev/ttyACM0)")
    parser.add_argument("-b", "--baudrate", type=int, default=9600, 
                       help="Baud rate (default: 9600)")
    parser.add_argument("-t", "--timeout", type=float, default=1.0,
                       help="Serial timeout in seconds (default: 1.0)")
    parser.add_argument("-d", "--log-dir", default="serial_logs",
                       help="Log directory (default: serial_logs)")
    parser.add_argument("-r", "--reconnect-delay", type=int, default=5,
                       help="Delay between reconnection attempts in seconds (default: 5)")
    
    args = parser.parse_args()
    
    # Validate serial port
    if not os.path.exists(args.port):
        print(f"Error: Serial port {args.port} does not exist")
        sys.exit(1)
    
    # Create and run the logger
    logger = SerialLogger(
        port=args.port,
        baudrate=args.baudrate,
        timeout=args.timeout,
        log_dir=args.log_dir,
        reconnect_delay=args.reconnect_delay
    )
    
    try:
        logger.run()
    except Exception as e:
        print(f"Unexpected error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()
