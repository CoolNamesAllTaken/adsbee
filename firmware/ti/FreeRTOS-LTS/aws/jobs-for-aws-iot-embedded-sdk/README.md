## AWS IoT Jobs library

**[API Documentation Pages for current and previous releases of this library can be found here](https://aws.github.io/Jobs-for-AWS-IoT-embedded-sdk/)**

The AWS IoT Jobs library helps you notify connected IoT devices of a pending
[Job](https://freertos.org/jobs/jobs-terminology.html). A Job can be used to
manage your fleet of devices, update firmware and security certificates on your
devices, or perform administrative tasks such as restarting devices and
performing diagnostics. It interacts with the
[AWS IoT Jobs service](https://docs.aws.amazon.com/iot/latest/developerguide/iot-jobs.html)
using MQTT, a lightweight publish-subscribe protocol. This library provides a
convenience API to compose and recognize the MQTT topic strings used by the Jobs
service. The library is written in C compliant with ISO C90 and MISRA C:2012,
and is distributed under the [MIT Open Source License](LICENSE).

This library has gone through code quality checks including verification that no
function has a
[GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html)
score over 10, and checks against deviations from mandatory rules in the
[MISRA coding standard](https://www.misra.org.uk). Deviations from the MISRA
C:2012 guidelines are documented under [MISRA Deviations](MISRA.md). This
library has also undergone both static code analysis from
[Coverity](https://scan.coverity.com/), and validation of memory safety with the
[CBMC bounded model checker](https://www.cprover.org/cbmc/).

See memory requirements for this library
[here](./docs/doxygen/include/size_table.md).

**AWS IoT Jobs v1.3.0
[source code](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/tree/v1.3.0/source)
is part of the
[FreeRTOS 202210.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202210.00-LTS)
release.**

**AWS IoT Jobs v1.1.0
[source code](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/tree/v1.1.0/source)
is part of the
[FreeRTOS 202012.01 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202012.01-LTS)
release.**

## Building the Jobs library

A compiler that supports **C99 or later** such as _gcc_ is required to build the
library.

Additionally, coreJSON is required for parsing. To build the library, first run:
```bash
git clone https://github.com/FreeRTOS/coreJSON.git --depth 1 --branch v3.2.0
```

Given an application in a file named `example.c`, _gcc_ can be used like so:

```bash
gcc -I source/include -I coreJSON/source/include example.c coreJSON/source/core_json.c source/jobs.c -o example
```

_gcc_ can also produce an object file to be linked later:

```bash
gcc -I source/include -I coreJSON/source/include -c source/jobs.c
```

## CBMC

To learn more about CBMC and proofs specifically, review the training material
[here](https://model-checking.github.io/cbmc-training).

The `test/cbmc` directory contains CBMC proofs.

In order to run these proofs you will need to install CBMC and other tools by
following the instructions
[here](https://model-checking.github.io/cbmc-training/installation.html).

## Reference example

The AWS IoT Device SDK for Embedded C repository contains a demo using the jobs
library on a POSIX platform.
https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main/demos/jobs/jobs_demo_mosquitto

## Documentation

### Existing Documentation

For pre-generated documentation, please see the documentation linked in the
locations below:

|                                                           Location                                                           |
| :--------------------------------------------------------------------------------------------------------------------------: |
|     [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C#releases-and-documentation)     |
| [FreeRTOS.org](https://freertos.org/Documentation/api-ref/jobs-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html) |

Note that the latest included version of the AWS IoT Jobs library may differ
across repositories.

### Generating Documentation

The Doxygen references were created using Doxygen version 1.9.2. To generate the
Doxygen pages, please run the following command from the root of this
repository:

```shell
doxygen docs/doxygen/config.doxyfile
```

## Building unit tests

### Platform Prerequisites

- For running unit tests
  - C99 compiler like gcc
  - CMake 3.13.0 or later
  - Ruby 2.0.0 or later is additionally required for the Unity test framework
    (that we use).
- For running the coverage target, lcov is additionally required.

### Steps to build Unit Tests

1. Create build directory: `mkdir build && cd build`

1. Run _cmake_ while inside build directory: `cmake -S ../test`

1. Run this command to build the library and unit tests: `make all`

1. The generated test executables will be present in `build/bin/tests` folder.

1. Run `ctest` to execute all tests and view the test run summary.

## Contributing

See [CONTRIBUTING.md](./.github/CONTRIBUTING.md) for information on
contributing.
