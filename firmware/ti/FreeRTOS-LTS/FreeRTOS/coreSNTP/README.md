## coreSNTP Library

**[API Documentation Pages for current and previous releases of this library can be found here](https://freertos.github.io/coreSNTP/)**

This repository contains the coreSNTP library, a client library to use Simple
Network Time Protocol (SNTP) to synchronize device clocks with internet time.
This library implements the SNTPv4 specification defined in
[RFC 4330](https://tools.ietf.org/html/rfc4330).

An SNTP client can request time from both NTP and SNTP servers. According to the
SNTPv4 specification, "_To an NTP or SNTP server, NTP and SNTP clients are
indistinguishable; to an NTP or SNTP client, NTP and SNTP servers are
indistinguishable._", thereby, allowing SNTP clients to request time from NTP
servers.

This library has gone through code quality checks including verification that no
function has a
[GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html)
score over 10, and checks against deviations from mandatory rules in the
[MISRA coding standard](https://www.misra.org.uk). Deviations from the MISRA
C:2012 guidelines are documented under [MISRA Deviations](MISRA.md). This
library has also undergone both static code analysis from
[Coverity static analysis](https://scan.coverity.com/), and validation of memory
safety through the
[CBMC automated reasoning tool](https://www.cprover.org/cbmc/).

See memory requirements for this library
[here](./docs/doxygen/include/size_table.md).

**coreSNTP v1.2.0
[source code](https://github.com/FreeRTOS/coreSNTP/tree/v1.2.0/source) is part
of the
[FreeRTOS 202210.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202210.00-LTS)
release.**

### Documentation

The API reference documentation for the coreSNTP library version released in
[FreeRTOS/FreeRTOS](https://github.com/FreeRTOS/FreeRTOS) can be viewed from the
[freertos.org website](https://freertos.org/coresntp/index.html).

## Cloning this repository

This repo uses
[Git Submodules](https://git-scm.com/book/en/v2/Git-Tools-Submodules) to bring
in dependent components.

To clone using HTTPS:

```sh
git clone https://github.com/FreeRTOS/coreSNTP.git --recurse-submodules
```

Using SSH:

```sh
git clone git@github.com:FreeRTOS/coreSNTP.git --recurse-submodules
```

If you have downloaded the repo without using the `--recurse-submodules`
argument, you need to run:

```sh
git submodule update --init --recursive
```

## Building the library

You can build the coreSNTP source files that are in the [source](source/)
directory, and add [source/include](source/include) to your compiler's include
path.

If using CMake, the [coreSntpFilePaths.cmake](coreSntpFilePaths.cmake) file
contains the above information of the source files and the header include path
from this repository.

## Reference Example

A reference example of using the coreSNTP library can be viewed in the
`FreeRTOS/FreeRTOS` repository
[here](https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS-Plus/Demo/coreSNTP_Windows_Simulator).
The demo application showcases use of the library in order to create an SNTP
client for periodic time synchronization of the system clock.

## Building Unit Tests

The unit tests for the library use CMock/Unity unit testing framework.

### Checkout CMock Submodule

To build unit tests, the submodule dependency of CMock is required. Use the
following command to clone the submodule:

```
git submodule update --checkout --init --recursive test/unit-test/CMock
```

### Unit Test Platform Prerequisites

- For running unit tests
  - **C90 compiler** like gcc
  - **CMake 3.13.0 or later**
  - **Ruby 2.0.0 or later** is additionally required for the CMock test
    framework (that we use).
- For running the coverage target, **gcov** and **lcov** are additionally
  required.

### Steps to build **Unit Tests**

1. Go to the root directory of this repository. (Make sure that the **CMock**
   submodule is cloned as described [above](#checkout-cmock-submodule))

1. Run the _cmake_ command: `cmake -S test -B build -DUNITTEST=ON`

1. Run this command to build the library and unit tests: `make -C build all`

1. The generated test executables will be present in `build/bin/tests` folder.

1. Run `cd build && ctest` to execute all tests and view the test run summary.

## CBMC proofs

To learn more about CBMC and proofs specifically, review the training material
[here](https://model-checking.github.io/cbmc-training).

The `test/cbmc/proofs` directory contains CBMC proofs.

In order to run these proofs you will need to install CBMC and other tools by
following the instructions
[here](https://model-checking.github.io/cbmc-training/installation.html).

## Generating documentation

The Doxygen references were created using Doxygen version 1.9.6. To generate the
Doxygen pages, please run the following command from the root of this
repository:

```sh
doxygen docs/doxygen/config.doxyfile
```

## Contributing

See [CONTRIBUTING.md](./.github/CONTRIBUTING.md) for information on
contributing.

## License

This library is licensed under the MIT License. See the [LICENSE](LICENSE) file.
