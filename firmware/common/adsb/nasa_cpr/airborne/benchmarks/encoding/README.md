# Example of use of the encode functionality of CPR.

The program in `encode.c` reads the information needed to encode a CPR message and prints the encoding.
It is expected for the information to be provided in a CSV file in
which every line starts with the following fields:

 1) message format [i] (int), (0 for even encoding, 1 for odd encoding)
 2) current latitude as AWB (unsigned int),
 3) current longitude as AWB (unsigned int).

The program expects as argument the name of the input CSV file. 
It prints on the standard output the following data:

 1) message format [i] (int),
 2) current latitude as AWB (unsigned int),
 3) current longitude as AWB (unsigned int),
 4) message latitude [YZ] (unsigned int),
 5) message longitude [XZ] (unsigned int).
 
All the integer values (AWB and encodings) are expected and output in hexadecimal with no prefixes (ie, "FF02" instead of "0xFF02", for example).

## Building

For convenience, a `Makefile` is provided to build the program.
```shell
$ make
gcc -o encode encode.c -L../.. -lairborne 
```

This program uses the airborne library (`libairborne.a`). 
To build the library, the user may invoke `make` in the [`airborne`](`../../`) directory (see [`airborne/README.md`](`../../README.md`) for details).

## Running

A bash script ([`run.sh`](run.sh)) aimed to automate the execution of the program on multiple files is also provided. 
It assumes that the CSV file contains not only the required input data (in the order explained above) but also the expected result of the encoding.
The script iterates over all the CSV files in the directory and executes `encode` on them.
Every result is stored in an `.out` file and compared with the input.
The standard output is used to report discrepancies of the results w.r.t. the given input.