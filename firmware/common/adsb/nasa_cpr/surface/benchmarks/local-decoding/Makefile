CC=gcc
CFLAGS=-Wall

all: surface check

surface:
	$(CC) -o decode decode.c -L../.. -lsurface $(FLAGS)

check:
	$(CC) -o check-decoding check-decoding.c ../../nl_int.o ../../cpr_int.o $(FLAGS)

clean:
	$(RM) decode check-decoding