import argparse
from at import *
import serial.tools.list_ports
import time

OTA_FILENAME = "../../../firmware/pico/build/application/adsbee_1090.ota"
SERIAL_TIMEOUT_SEC = 10 # Long timeout since some flash operations take a while.

def wait_for_new_com_ports():
    """Get newly connected COM ports."""
    known_ports = {port.device for port in serial.tools.list_ports.comports()}

    while True:
        # Keep checking until a new port is detected.
        current_ports = {port.device for port in serial.tools.list_ports.comports()}
        new_ports = current_ports - known_ports
        
        if len(new_ports) > 0:
            time.sleep(1) # Wait a moment for the port to be ready.
            return new_ports
        
        known_ports = current_ports
        time.sleep(0.1)

def ota_flash(com_port_or_ip, erase=False, flash=False, boot=False):
    port = None
    if com_port_or_ip == "auto":
        print("Waiting for new COM port...")
        port = wait_for_new_com_ports().pop()
        print(f"New COM port detected: {port}")
    else:
        port = com_port_or_ip
        print("Using port or IP: " + port)
    
    with ADSBeeAT(port, serial_timeout_sec=SERIAL_TIMEOUT_SEC) as adsbee:
        # Assumes that we only connected a single new serial device, and that it's an ADSBee.
        if erase:
            adsbee.ota_erase()
        if flash:
            adsbee.ota_write_file(OTA_FILENAME)
        if boot:
            adsbee.ota_boot()

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Flash OTA file to ADSBee device.")
    parser.add_argument("com_port_or_ip", help="COM port or IP address of the device.")
    parser.add_argument("--erase", default=False, action="store_true", help="Erase chip.")
    parser.add_argument("--flash", default=False, action="store_true", help="Flash chip.")
    parser.add_argument("--boot", default=False, action="store_true", help="Jump to the complementary boot partition.")
    args = parser.parse_args()
    
    ota_flash(args.com_port_or_ip, args.erase, args.flash, args.boot)