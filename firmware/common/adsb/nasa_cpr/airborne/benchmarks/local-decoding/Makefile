CC=gcc
CFLAGS=-Wall

all: airborne check

airborne:
	$(CC) -o decode decode.c -L../.. -lairborne $(FLAGS)

check:
	$(CC) -o check-decoding check-decoding.c ../../nl_int.o ../../cpr_int.o $(FLAGS)

clean:
	$(RM) decode check-decoding