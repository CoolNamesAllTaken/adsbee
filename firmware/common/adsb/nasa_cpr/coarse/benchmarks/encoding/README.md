#Example of use of the encode functionality of CPR.

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
gcc -o encode encode.c -L../.. -lcoarse 
```

This program uses the coarse library (`libcoarse.a`). 
To build the library, the user may invoke `make` in the [`coarse`](`../../`) directory (see [`coarse/README.md`](`../../README.md`) for details).

A bash script ([`encode-all.sh`](encode-all.sh)) aimed to automate the
execution of the program on multiple files is also provided.
It executes `encode` on every `.csv` file in the current directory and prints the results in corresponding `.out` files.

## Checking the results

A script aimed to check the produced encodings is provided. This
script assumes that `encode-all.sh` has already been run, and so every
.csv file has a corresponding .csv.out file associated to it. 

* `check-against.sh` assumes that every `.csv` file contains not only the required input data (in the order explained above) but also the expected encoding result. The script simply compares every `.csv` file with its corresponding `.csv.out` file. The standard output is used to report discrepancies.
