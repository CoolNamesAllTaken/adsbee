# AWS IoT Device Shadow library

**[API Documentation Pages for current and previous releases of this library can be found here](https://aws.github.io/Device-Shadow-for-AWS-IoT-embedded-sdk/)**

The AWS IoT Device Shadow library enables you to store and retrieve the current
state (the “shadow”) of every registered device. The device’s shadow is a
persistent, virtual representation of your device that you can interact with
from AWS IoT Core even if the device is offline. The device state is captured as
its “shadow” within a [JSON](https://www.json.org/) document. The device can
send commands over MQTT to get, update and delete its latest state as well as
receive notifications over MQTT about changes in its state. Each device’s shadow
is uniquely identified by the name of the corresponding “thing”, a
representation of a specific device or logical entity on the AWS Cloud. See
[Managing Devices with AWS IoT](https://docs.aws.amazon.com/iot/latest/developerguide/iot-thing-management.html)
for more information on IoT "thing". More details about AWS IoT Device Shadow
can be found in
[AWS IoT documentation](https://docs.aws.amazon.com/iot/latest/developerguide/iot-device-shadows.html).
This library is distributed under the [MIT Open Source License](LICENSE).

**Note**: From
[v1.1.0](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/tree/v1.1.0)
release onwards, you can used named shadow, a feature of the AWS IoT Device
Shadow service that allows you to create multiple shadows for a single IoT
device.

This library has gone through code quality checks including verification that no
function has a
[GNU Complexity](https://www.gnu.org/software/complexity/manual/complexity.html)
score over 8, and checks against deviations from mandatory rules in the
[MISRA coding standard](https://www.misra.org.uk). Deviations from the MISRA
C:2012 guidelines are documented under [MISRA Deviations](MISRA.md). This
library has also undergone both static code analysis from
[Coverity static analysis](https://scan.coverity.com/), and validation of memory
safety through the
[CBMC automated reasoning tool](https://www.cprover.org/cbmc/).

See memory requirements for this library
[here](https://docs.aws.amazon.com/embedded-csdk/202103.00/lib-ref/libraries/aws/device-shadow-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html#shadow_memory_requirements).

**AWS IoT Device Shadow v1.3.0
[source code](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/tree/v1.3.0)
is part of the
[FreeRTOS 202210.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202210.00-LTS)
release.**

**AWS IoT Device Shadow v1.0.2
[source code](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/tree/v1.0.2)
is part of the
[FreeRTOS 202012.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202012.00-LTS)
release.**

### AWS IoT Device Shadow Config File

The AWS IoT Device Shadow library exposes configuration macros that are required
for building the library. A list of all the configurations and their default
values are defined in
[shadow_config_defaults.h](source/include/shadow_config_defaults.h). To provide
custom values for the configuration macros, a custom config file named
`shadow_config.h` can be provided by the user application to the library.

By default, a `shadow_config.h` custom config is required to build the library.
To disable this requirement and build the library with default configuration
values, provide `SHADOW_DO_NOT_USE_CUSTOM_CONFIG` as a compile time preprocessor
macro.

## Building the Library

The [shadowFilePaths.cmake](shadowFilePaths.cmake) file contains the information
of all source files and the header include path required to build the AWS IoT
Device Shadow library.

As mentioned in the [previous section](#aws-iot-device-shadow-config-file),
either a custom config file (i.e. `shadow_config.h`) OR the
`SHADOW_DO_NOT_USE_CUSTOM_CONFIG` macro needs to be provided to build the AWS
IoT Device Shadow library.

For a CMake example of building the AWS IoT Device Shadow library with the
`shadowFilePaths.cmake` file, refer to the `coverity_analysis` library target in
[test/CMakeLists.txt](test/CMakeLists.txt) file.

## Building Unit Tests

### Checkout CMock Submodule

By default, the submodules in this repository are configured with `update=none`
in [.gitmodules](.gitmodules) to avoid increasing clone time and disk space
usage of other repositories (like
[amazon-freertos](https://github.com/aws/amazon-freertos) that submodules this
repository).

To build unit tests, the submodule dependency of CMock is required. Use the
following command to clone the submodule:

```
git submodule update --checkout --init --recursive --test/unit-test/CMock
```

### Platform Prerequisites

- For building the library, **CMake 3.13.0** or later and a **C90 compiler**.
- For running unit tests, **Ruby 2.0.0** or later is additionally required for
  the CMock test framework (that we use).
- For running the coverage target, **gcov** and **lcov** are additionally
  required.

### Steps to build unit tests

1. Go to the root directory of this repository. (Make sure that the **CMock**
   submodule is cloned as described [above](#checkout-cmock-submodule).)

1. Run the _cmake_ command: `cmake -S test -B build`

1. Run this command to build the library and unit tests: `make -C build all`

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

Please refer to the demos of the AWS IoT Device Shadow library in the following
locations for reference examples on POSIX and FreeRTOS platforms:

| Platform |                                                             Location                                                              | Transport Interface Implementation <br> (for [coreMQTT](https://github.com/FreeRTOS/coreMQTT) stack) </br> |
| :------: | :-------------------------------------------------------------------------------------------------------------------------------: | :--------------------------------------------------------------------------------------------------------: |
|  POSIX   | [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main/demos/shadow/shadow_demo_main) |                             POSIX sockets for TCP/IP and OpenSSL for TLS stack                             |
| FreeRTOS |    [FreeRTOS/FreeRTOS](https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS-Plus/Demo/AWS/Device_Shadow_Windows_Simulator)     |                             FreeRTOS+TCP for TCP/IP and mbedTLS for TLS stack                              |
| FreeRTOS |        [FreeRTOS AWS Reference Integrations](https://github.com/aws/amazon-freertos/tree/main/demos/device_shadow_for_aws)        |                                    Based on Secure Sockets Abstraction                                     |

## Documentation

### Existing Documentation

For pre-generated documentation, please see the documentation linked in the
locations below:

|                                                               Location                                                                |
| :-----------------------------------------------------------------------------------------------------------------------------------: |
|         [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C#releases-and-documentation)          |
| [FreeRTOS.org](https://freertos.org/Documentation/api-ref/device-shadow-for-aws-iot-embedded-sdk/docs/doxygen/output/html/index.html) |

Note that the latest included version of IoT Device Shadow library may differ
across repositories.

## Generating documentation

The Doxygen references were created using Doxygen version 1.9.6. To generate the
Doxygen pages, please run the following command from the root of this
repository:

```shell
doxygen docs/doxygen/config.doxyfile
```

## Contributing

See [CONTRIBUTING.md](./.github/CONTRIBUTING.md) for information on
contributing.
