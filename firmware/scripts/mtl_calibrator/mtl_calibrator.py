# NOTE: This software has been mothballed, since MTL values are pretty close to their setpoints and no calibration is required.

import serial
import argparse
import numpy as np
import matplotlib.pyplot as plt
import time
import re

MTL_MIN_MV = 0
MTL_MAX_MV = 225
MTL_RESOLUTION_MV = 10

def open_serial_port(port_name, baud_rate):
    try:
        serial_port = serial.Serial(port_name, baud_rate)
        return serial_port
    except serial.SerialException as e:
        print(f"Error: {e}")
        return None
    
def calibrate_mtl(serial_port: serial.Serial):
    serial_port.write("AT+CONFIG=1\r\n".encode('utf-8'))
    print(f"Entering CONFIG mode: {serial_port.readline()}")

    mtl_set_values = np.arange(MTL_MIN_MV, MTL_MAX_MV, 10)
    mtl_read_values = np.empty((mtl_set_values.shape[0], 2))
    for i, set_value in enumerate(mtl_set_values):
        serial_port.write(f"AT+MTLSET={set_value},{set_value}\r\n".encode('utf-8'))
        time.sleep(0.1)

        # Set a Minimum Trigger Level for both lo and hi thresholds, then confirm that it took.
        print(f"Setting MTL={set_value}mV...", end="")
        mtl_lo_mv_ = int(re.findall(r'\b\d+\b', serial_port.readline().decode())[0])
        mtl_hi_mv_ = int(re.findall(r'\b\d+\b', serial_port.readline().decode())[0])
        if mtl_lo_mv_ == set_value and mtl_hi_mv_ == set_value:
            print("OK")
        else:
            print(f"ERROR: set_value={set_value} but mtl_lo_mv_={mtl_lo_mv_} and mtl_hi_mv_={mtl_hi_mv_}")
            return

        # Read the actual MTL voltage with the ADC.
        serial_port.write(f"AT+MTLREAD?\r\n".encode('utf-8'))
        mtl_adc_counts_list = re.findall(r'\b\d+\b', serial_port.readline().decode())
        mtl_lo_adc_counts_ = int(mtl_adc_counts_list[0])
        mtl_hi_adc_counts_ = int(mtl_adc_counts_list[1])
        print(f"\tmtl_lo_adc_counts_={mtl_lo_adc_counts_} mtl_hi_adc_counts_={mtl_hi_adc_counts_}")
        mtl_read_values[i] = [mtl_lo_adc_counts_, mtl_hi_adc_counts_]
    
    mtl_data = np.hstack([mtl_set_values[:, np.newaxis], mtl_read_values])
    fig, (ax1, ax2) = plt.subplots(2, 1)
    ax1.plot(mtl_data[:, 0], mtl_data[:, 0], label="MTL Set Value [mV]")
    ax1.plot(mtl_data[:, 0], mtl_data[:, 1], label="MTL LO Read Value [mV]")
    ax1.plot(mtl_data[:, 0], mtl_data[:, 2], label="MTL HI Read Value [mV]")
    ax1.legend()
    ax1.xlabel("MTL Set Value [mV]")
    ax1.ylabel("MTL Read Value [mV]")
    plt.show()

    print(mtl_data)

def main():
    parser = argparse.ArgumentParser(description="Open a serial port")
    parser.add_argument("port", help="Name of the serial port (e.g., COM1, /dev/ttyUSB0)")
    parser.add_argument("baudrate", type=int, help="Baud rate of the serial port")
    args = parser.parse_args()

    port_name = args.port
    baud_rate = args.baudrate
    
    serial_port = open_serial_port(port_name, baud_rate)
    if serial_port is not None:
        print(f"Serial port {port_name} opened successfully!")
        # You can perform further operations with the serial port here
        # For example, you can read or write data to the serial port

        calibrate_mtl(serial_port)
        serial_port.close()
    else:
        print("Failed to open serial port.")

if __name__ == "__main__":
    main()
