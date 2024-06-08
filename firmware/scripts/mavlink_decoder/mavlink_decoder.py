from pymavlink import mavutil

SERIAL_PORT = "COM3"
BAUD_RATE = 115200

mavlink_connection = mavutil.mavlink_connection(SERIAL_PORT, baud=BAUD_RATE)

while (True):
      
    msg = self.mavlink_connection.recv_match(type='ADSB_VEHICLE', blocking=False)
    if msg:
        print(msg)
