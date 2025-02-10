CC=gcc
CFLAGS=-Wall

all: airborne check

airborne:
	$(CC) -o encode encode.c -L../.. -lairborne $(FLAGS)

check:
	$(CC) -o check-encoding check-encoding.c $(FLAGS)

clean:
	$(RM) encode check-encoding