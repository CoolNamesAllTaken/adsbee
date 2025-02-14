# Example of use of the local decoding functionality of CPR

The program in `decode.c` reads the information needed to (locally) decode a CPR message and prints the recovered position.
It is expected for the information to be provided in a CSV file in which every line starts with the following fields: 
 1) reference latitude as AWB (unsigned int),
 2) reference longitude as AWB (unsigned int),
 3) current latitude as AWB (unsigned int),
 4) current longitude as AWB (unsigned int),
 5) message format [i] (int)
 6) message latitude [YZ] (unsigned int),
 7) message longitude [XZ] (unsigned int).

The program expects as argument the name of the input CSV file. 
It prints on the standard output the following data:

 1) reference latitude as AWB (unsigned int),
 2) reference longitude as AWB (unsigned int),
 3) current latitude as AWB (unsigned int),
 4) current longitude as AWB (unsigned int), 
 5) message format [i] (int)
 6) message latitude [YZ] (unsigned int),
 7) message longitude [XZ] (unsigned int),
 8) recovered latitude as AWB (unsigned int),
 9) recovered longitude as AWB (unsigned int).

All the integer values (AWB and encodings) are expected and output in hexadecimal with no prefixes (ie, "FF02" instead of "0xFF02", for example).

## Building

For convenience, a `Makefile` is provided. The `coarse` target can be used to build the program.
```shell
$ make coarse
gcc -o decode decode.c -L../.. -lcoarse 
```

This program uses the coarse library (`libcoarse.a`). 
To build the library, the user may invoke `make` in the [`coarse`](`../../`) directory (see [`coarse/README.md`](`../../README.md`) for details).

A bash script ([`decode-all.sh`](decode-all.sh)) aimed to automate the execution of the program on multiple files is also provided. 
It executes `decode` on every `.csv` file in the current directory and prints the results in corresponding `.out` files.

## Checking the results

Two scripts aimed to check the produced decodings are provided. These
scripts assume that `decode-all.sh` has already been run, and so every
.csv file has a corresponding .csv.out file associated to it. 

* `check-decoding.sh` checks that every position in an `.csv.out` file with the format explained above fulfills the condition on the correctness theorem for the decoding. For that purpose, it executes the program `check-decoding` which can be built by the target `check` of the Makefile.

* `check-against.sh` assumes that every `.csv` file contains not only the required input data (in the order explained above) but also the expected decoding result. The script simply compares every `.csv` file with its corresponding `.csv.out` file. The standard output is used to report discrepancies.
