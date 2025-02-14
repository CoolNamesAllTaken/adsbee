CC=gcc
CFLAGS=-Wall

all: intent check

intent:
	$(CC) -o decode decode.c -L../.. -lintent $(FLAGS)

check:
	$(CC) -o check-decoding check-decoding.c ../../nl_int.o ../../cpr_int.o $(FLAGS)

clean:
	$(RM) decode check-decoding