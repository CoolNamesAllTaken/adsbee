CC=gcc
CFLAGS=-Wall

surface:
	$(CC) -c -o nl_int.o nl_int.c $(CFLAGS)
	$(CC) -c -o cpr_int.o cpr_int.c $(CFLAGS)
	$(CC) -c -o surface.o cpr.c $(CFLAGS)
	ar -cr libsurface.a surface.o cpr_int.o nl_int.o

clean: 
	$(RM) *.o *.a
	
clean-all: clean
	$(MAKE) clean -C benchmarks/encoding
	$(MAKE) clean -C benchmarks/local-decoding
	$(MAKE) clean -C benchmarks/global-decoding
