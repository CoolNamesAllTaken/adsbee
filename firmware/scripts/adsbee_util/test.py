from adsbee import ADSBee

SERIAL_COM_PORT = 'COM4'

with ADSBee(SERIAL_COM_PORT) as bee:
    while (True):
        print(bee.ser.readline().decode('utf-8'), end="")