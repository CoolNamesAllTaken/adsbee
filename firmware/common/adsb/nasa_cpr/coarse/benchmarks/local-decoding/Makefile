CC=gcc
CFLAGS=-Wall

all: coarse check

coarse:
	$(CC) -o decode decode.c -L../.. -lcoarse $(FLAGS)

check:
	$(CC) -o check-decoding check-decoding.c ../../nl_int.o ../../cpr_int.o $(FLAGS)

clean:
	$(RM) decode check-decoding