This directory contains a formally verified fixed-point implementation of the CPR encoding/decoding functions for the **airborne** format (Nb=17).

* `cpr`: entry-point for encoding/decoding features.
* `cpr_int`: (formally verified) core encoding/decoding functions.
* `nl_int`: (formally verified) precomputed NL table.

For examples of use, please see the directory [`benchmarks`](benchmarks).

The included `Makefile` can be used to generate the static library `libairborne.a`.

```shell
$ make
gcc -c -o nl_int.o nl_int.c -Wall
gcc -c -o cpr_int.o cpr_int.c -Wall
gcc -c -o airborne.o cpr.c -Wall
ar -cr libairborne.a airborne.o cpr_int.o nl_int.o
```
