from pymavlink import mavutil
import serial
import os
import time # for timestamping
import sys # for arguments

SERIAL_PORT = sys.argv[1]
BAUD_RATE = sys.argv[2]
REFRESH_RATE_HZ = 1
MAVLINK_PACKET_TYPE_LIST = ['ADSB_VEHICLE', 'MESSAGE_INTERVAL', 'REQUEST_DATA_STREAM']

print(f"Connecting to MAVLINK device on {SERIAL_PORT} at {BAUD_RATE} baud.")
mavlink_connection = mavutil.mavlink_connection(SERIAL_PORT, baud=BAUD_RATE)

while (True):
    msg = mavlink_connection.recv_match(type=MAVLINK_PACKET_TYPE_LIST, blocking=True)
    os.system('cls') # Clear the screen.
    print("ICAO Addr |Latitude  |Longitude |Alt Type  |Alt (m)   |Hdg (deg) |Hvel (m/s)|Vvel (m/s)|Callsign  |Type      |TSLC (sec)|Flags     |Squawk")
    print("----------|----------|----------|----------|----------|----------|----------|----------|----------|----------|----------|----------|----------")
    
    while (msg.get_type() == 'ADSB_VEHICLE'):
        print(f"{msg.ICAO_address:10x}|{msg.lat / 1e7:+10.4f}|{msg.lon / 1e7:+10.4f}|{msg.altitude_type:10x}|"\
                f"{msg.altitude / 1e3:10.2f}|{msg.heading / 100:10.4f}|{msg.hor_velocity / 100:10}|"\
                f"{msg.ver_velocity / 100:10}|{msg.callsign:10}|{msg.emitter_type:10}|{msg.tslc:10}|{msg.flags:10b}|"\
                f"{msg.squawk:10o}")
        msg = mavlink_connection.recv_match(type=MAVLINK_PACKET_TYPE_LIST, blocking=True)
