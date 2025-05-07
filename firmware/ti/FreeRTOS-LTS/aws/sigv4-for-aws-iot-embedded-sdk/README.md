# AWS SigV4 Library

**[API Documentation Pages for current and previous releases of this library can be found here](https://aws.github.io/SigV4-for-AWS-IoT-embedded-sdk/)**

The AWS SigV4 Library is a standalone library for generating authorization
headers and signatures according to the specifications of the
[Signature Version 4](https://docs.aws.amazon.com/general/latest/gr/signature-version-4.html)
signing process. Authorization headers are required for authentication when
sending HTTP requests to AWS. This library can optionally be used by
applications sending direct HTTP requests to AWS services requiring SigV4
authentication. This library has no dependencies on any additional libraries
other than the standard C library. This library is distributed under the MIT
Open Source License.

This library has gone through code quality checks including verification that no
function has a GNU Complexity score over 8, and checks against deviations from
mandatory rules in the MISRA coding standard. Deviations from the MISRA C:2012
guidelines are documented under MISRA Deviations. This library has also
undergone static code analysis using Coverity static analysis, and validation of
memory safety through the CBMC automated reasoning tool.

See memory requirements for this library [here][memory_table].

[memory_table]: ./docs/doxygen/include/size_table.md

**AWS SigV4 v1.2.0
[source code](https://github.com/aws/Sigv4-for-AWS-IoT-embedded-sdk/tree/v1.2.0/source)
is part of the
[FreeRTOS 202210.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202210.00-LTS)
release.**

## AWS SigV4 Library Config File

The AWS SigV4 library exposes build configuration macros that are required for
building the library. A list of all the configurations and their default values
are defined in [sigv4_config_defaults.h][default_config]. To provide custom
values for the configuration macros, a config file named `sigv4_config.h` can be
provided by the application to the library.

[default_config]: source/include/sigv4_config_defaults.h

By default, a `sigv4_config.h` config file is required to build the library. To
disable this requirement and build the library with default configuration
values, provide `SIGV4_DO_NOT_USE_CUSTOM_CONFIG` as a compile time preprocessor
macro.

**Thus, the SigV4 library can be built by either**:

- Defining a `sigv4_config.h` file in the application, and adding it to the
  include directories list of the library.

**OR**

- Defining the `SIGV4_DO_NOT_USE_CUSTOM_CONFIG` preprocessor macro for the
  library build.

## Building the SigV4 Library

The [sigv4FilePaths.cmake](sigv4FilePaths.cmake) file contains information of
all the source files and header include paths required to build the SigV4
library.

As mentioned in the previous section, either a custom config file (i.e.
`sigv4_config.h`) or `SIGV4_DO_NOT_USE_CUSTOM_CONFIG` macro needs to be provided
to build the SigV4 library.

To use CMake, please refer to the
[sigV4FilePaths.cmake](https://github.com/aws/SigV4-for-AWS-IoT-embedded-sdk/blob/main/sigv4FilePaths.cmake)
file, which contains the relevant information regarding source files and header
include paths required to build this library.

## Building Unit Tests

### Platform Prerequisites

- For running unit tests:
  - **C90 compiler** like gcc.
  - **CMake 3.13.0 or later**.
  - **Ruby 2.0.0 or later** is additionally required for the CMock test
    framework (that we use).
- For running the coverage target, **gcov** and **lcov** are additionally
  required.

### Steps to build **Unit Tests**

1. Go to the root directory of this repository.

1. Run the _cmake_ command: `cmake -S test -B build -DUNITTEST=ON`.

1. Run this command to build the library and unit tests: `make -C build all`.

1. The generated test executables will be present in `build/bin/tests` folder.

1. Run `cd build && ctest` to execute all tests and view the test run summary.

## CBMC

To learn more about CBMC and proofs specifically, review the training material
[here](https://model-checking.github.io/cbmc-training).

The `test/cbmc/proofs` directory contains CBMC proofs.

In order to run these proofs you will need to install CBMC and other tools by
following the instructions
[here](https://model-checking.github.io/cbmc-training/installation.html).

## Reference examples

The AWS IoT Embedded C-SDK repository contains
[HTTP demos](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main/demos/http)
showing the use of the AWS SigV4 Library on a POSIX platform to authenticate
HTTP requests to AWS S3 service.

## Generating documentation

The Doxygen references found in this repository were created using Doxygen
version 1.9.6. To generate these Doxygen pages, please run the following command
from the root of this repository:

```shell
doxygen docs/doxygen/config.doxyfile
```

## Contributing

See [CONTRIBUTING.md](.github/CONTRIBUTING.md) for information on contributing.
