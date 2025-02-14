CC=gcc
CFLAGS=-Wall

airborne:
	$(CC) -c -o nl_int.o nl_int.c $(CFLAGS)
	$(CC) -c -o cpr_int.o cpr_int.c $(CFLAGS)
	$(CC) -c -o airborne.o cpr.c $(CFLAGS)
	ar -cr libairborne.a airborne.o cpr_int.o nl_int.o

clean: 
	$(RM) *.o *.a

clean-all: clean
	$(MAKE) clean -C benchmarks/encoding
	$(MAKE) clean -C benchmarks/local-decoding
	$(MAKE) clean -C benchmarks/global-decoding
