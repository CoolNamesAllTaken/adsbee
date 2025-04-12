# Example of use of the decoding functionality of CPR.

The program in `decode.c` reads the information needed to (globally) decode a CPR message and prints the recovered position.
It is expected for the information to be provided in a CSV file in which every line starts with the following fields:

1) even latitude as AWB (unsigned int, hexadecimal),
2) even longitude as AWB (unsigned int, hexadecimal),
3) encoded even latitude [YZ] (unsigned int, hexadecimal),
4) encoded even longitude [XZ] (unsigned int, hexadecimal),
5) odd latitude as AWB (unsigned int, hexadecimal),
6) odd longitude as AWB (unsigned int, hexadecimal),
7) encoded odd latitude [YZ] (unsigned int, hexadecimal),
8) encoded odd longitude [XZ] (unsigned int, hexadecimal),


The program expects as argument the name of the input CSV file. 
It prints on the standard output the following data:

1) even latitude as AWB (unsigned int, hexadecimal),
2) even longitude as AWB (unsigned int, hexadecimal),
3) encoded even latitude [YZ] (unsigned int, hexadecimal),
4) encoded even longitude [XZ] (unsigned int, hexadecimal),
5) odd latitude as AWB (unsigned int, hexadecimal),
6) odd longitude as AWB (unsigned int, hexadecimal),
7) encoded odd latitude [YZ] (unsigned int, hexadecimal),
8) encoded odd longitude [XZ] (unsigned int, hexadecimal),
9) validity flag for recovered NL values (1 for valid, 0 for invalid),
10) recovered latitude as AWB (unsigned int, hexadecimal) decoding with i=0,
11) recovered longitude as AWB (unsigned int, hexadecimal) decoding with i=0,
12) recovered latitude as AWB (unsigned int, hexadecimal) decoding with i=1,
13) recovered longitude as AWB (unsigned int, hexadecimal) decoding with i=1

## Building

For convenience, a `Makefile` is provided to build the program.
```shell
$ make
gcc -o decode decode.c -L../.. -lsurface 
```

This program uses the surface library (`libsurface.a`). 
To build the library, the user may invoke `make` in the [`surface`](`../../`) directory (see [`surface/README.md`](`../../README.md`) for details).

A bash script ([`decode-all.sh`](decode-all.sh)) aimed to automate the execution of the program on multiple files is also provided. 
It executes `decode` on every `.csv` file in the current directory and prints the results in corresponding `.out` files.

## Checking the results

Two scripts aimed to check the produced decodings are provided. These
scripts assume that `decode-all.sh` has already been run, and so every
.csv file has a corresponding .csv.out file associated to it.  

* `check-decoding.sh` checks that every position in an `.csv.out` file with the format explained above fulfills the condition on the correctness theorem for the decoding. For that purpose, it executes the program `check-decoding` which can be built by the target `check` of the Makefile.

* `check-against.sh` assumes that every `.csv` file contains not only the required input data (in the order explained above) but also the expected decoding result. The script simply compares every `.csv` file with its corresponding `.csv.out` file. The standard output is used to report discrepancies.
