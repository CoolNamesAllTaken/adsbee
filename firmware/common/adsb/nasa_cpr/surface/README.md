This directory contains a formally verified fixed-point implementation of the CPR encoding/decoding functions for the **surface** format (Nb=19).

* `cpr`: entry-point for encoding/decoding features.
* `cpr_int`: (formally verified) core encoding/decoding functions.
* `nl_int`: (formally verified) precomputed NL table.

For examples of use, please see the directory [`benchmarks`](benchmarks).

The included `Makefile` can be used to generate the static library `libsurface.a`.

```shell
$ make
gcc -c -o nl_int.o nl_int.c -Wall
gcc -c -o cpr_int.o cpr_int.c -Wall
gcc -c -o surface.o cpr.c -Wall
ar -cr libsurface.a surface.o cpr_int.o nl_int.o
```
