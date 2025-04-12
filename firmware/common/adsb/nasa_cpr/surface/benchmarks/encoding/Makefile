CC=gcc
CFLAGS=-Wall

all: surface check verify

surface:
	$(CC) -o encode encode.c -L../.. -lsurface $(FLAGS)

check:
	$(CC) -o check-encoding check-encoding.c $(FLAGS)

verify:
	$(CC) -o verify-lat-trans-points verify-lat-trans-points.c -L../.. -lsurface $(FLAGS)

clean:
	$(RM) encode check-encoding verify-lat-trans-points