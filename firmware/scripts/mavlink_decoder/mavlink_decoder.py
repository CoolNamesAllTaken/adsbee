from pymavlink import mavutil
import serial
import os
import time # for timestamping

SERIAL_PORT = "COM3"
BAUD_RATE = 115200
REFRESH_RATE_HZ = 1

mavlink_connection = mavutil.mavlink_connection(SERIAL_PORT, baud=BAUD_RATE)

while (True):
    next_update_timestamp_s = time.time() + 1 / REFRESH_RATE_HZ
    os.system('cls') # Clear the screen.
    print("ICAO Addr |Latitude  |Longitude |Alt Type  |Alt (m)   |Hdg (deg) |Hvel (m/s)|Vvel (m/s)|Callsign  |Type      |Squawk")
    print("----------|----------|----------|----------|----------|----------|----------|----------|----------|----------|----------")
    msg = mavlink_connection.recv_match(type='ADSB_VEHICLE', blocking=False)
    while (msg):
        print(f"{msg.ICAO_address:10x}|{msg.lat / 1e7:+10.4f}|{msg.lon / 1e7:+10.4f}|{msg.altitude_type:10x}|"\
              f"{msg.altitude / 1e3:10.2f}|{msg.heading / 100:10.4f}")
        msg = mavlink_connection.recv_match(type='ADSB_VEHICLE', blocking=False)
    time.sleep(next_update_timestamp_s - time.time())
