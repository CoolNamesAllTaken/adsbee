# coreMQTT Client Library

**[API Documentation Pages for current and previous releases of this library can be found here](https://freertos.github.io/coreMQTT/)**

This repository contains the coreMQTT library that has been optimized for a low
memory footprint. The coreMQTT library is compliant with the
[MQTT 3.1.1](https://docs.oasis-open.org/mqtt/mqtt/v3.1.1/mqtt-v3.1.1.html)
standard. It has no dependencies on any additional libraries other than the
standard C library, a customer-implemented network transport interface, and
_optionally_ a user-implemented platform time function. This library is
distributed under the [MIT Open Source License](LICENSE).

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
[here](./docs/doxygen/include/size_table.md).

**coreMQTT v2.3.0
[source code](https://github.com/FreeRTOS/coreMQTT/tree/v2.3.0/source) is part
of the
[FreeRTOS 202406.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202406-LTS)
release.**

## MQTT Config File

The MQTT client library exposes build configuration macros that are required for
building the library. A list of all the configurations and their default values
are defined in
[core_mqtt_config_defaults.h](source/include/core_mqtt_config_defaults.h). To
provide custom values for the configuration macros, a custom config file named
`core_mqtt_config.h` can be provided by the application to the library.

By default, a `core_mqtt_config.h` custom config is required to build the
library. To disable this requirement and build the library with default
configuration values, provide `MQTT_DO_NOT_USE_CUSTOM_CONFIG` as a compile time
preprocessor macro.

**Thus, the MQTT library can be built by either**:

- Defining a `core_mqtt_config.h` file in the application, and adding it to the
  include directories list of the library
  **OR**
- Defining the `MQTT_DO_NOT_USE_CUSTOM_CONFIG` preprocessor macro for the
  library build.

## Sending metrics to AWS IoT

When establishing a connection with AWS IoT, users can optionally report the
Operating System, Hardware Platform and MQTT client version information of their
device to AWS. This information can help AWS IoT provide faster issue resolution
and technical support. If users want to report this information, they can send a
specially formatted string (see below) in the username field of the MQTT CONNECT
packet.

Format

The format of the username string with metrics is:

```
<Actual_Username>?SDK=<OS_Name>&Version=<OS_Version>&Platform=<Hardware_Platform>&MQTTLib=<MQTT_Library_name>@<MQTT_Library_version>
```

Where

- <Actual_Username> is the actual username used for authentication, if username
  and password are used for authentication. When username and password based
  authentication is not used, this is an empty value.
- <OS_Name> is the Operating System the application is running on (e.g.
  FreeRTOS)
- <OS_Version> is the version number of the Operating System (e.g. V10.4.3)
- <Hardware_Platform> is the Hardware Platform the application is running on
  (e.g. WinSim)
- <MQTT_Library_name> is the MQTT Client library being used (e.g. coreMQTT)
- <MQTT_Library_version> is the version of the MQTT Client library being used
  (e.g. 1.0.2)

Example

- Actual_Username = “iotuser”, OS_Name = FreeRTOS, OS_Version = V10.4.3,
  Hardware_Platform_Name = WinSim, MQTT_Library_Name = coremqtt,
  MQTT_Library_version = 2.3.0. If username is not used, then “iotuser” can be
  removed.

```
/* Username string:
 * iotuser?SDK=FreeRTOS&Version=v10.4.3&Platform=WinSim&MQTTLib=coremqtt@2.3.0
 */

#define OS_NAME                   "FreeRTOS"
#define OS_VERSION                "V10.4.3"
#define HARDWARE_PLATFORM_NAME    "WinSim"
#define MQTT_LIB                  "coremqtt@2.3.0"

#define USERNAME_STRING           "iotuser?SDK=" OS_NAME "&Version=" OS_VERSION "&Platform=" HARDWARE_PLATFORM_NAME "&MQTTLib=" MQTT_LIB
#define USERNAME_STRING_LENGTH    ( ( uint16_t ) ( sizeof( USERNAME_STRING ) - 1 ) )

MQTTConnectInfo_t connectInfo;
connectInfo.pUserName = USERNAME_STRING;
connectInfo.userNameLength = USERNAME_STRING_LENGTH;
mqttStatus = MQTT_Connect( pMqttContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, pSessionPresent );
```

## Upgrading to v2.0.0 and above

With coreMQTT versions >=v2.0.0, there are breaking changes. Please refer to the
[coreMQTT version >=v2.0.0 Migration Guide](MigrationGuide.md).

## Building the Library

The [mqttFilePaths.cmake](mqttFilePaths.cmake) file contains the information of
all source files and the header include path required to build the MQTT library.

Additionally, the MQTT library requires two header files that are not part of
the ISO C90 standard library, `stdbool.h` and `stdint.h`. For compilers that do
not provide these header files, the [source/include](source/include) directory
contains the files [stdbool.readme](source/include/stdbool.readme) and
[stdint.readme](source/include/stdint.readme), which can be renamed to
`stdbool.h` and `stdint.h`, respectively, to provide the type definitions
required by MQTT.

As mentioned in the previous section, either a custom config file (i.e.
`core_mqtt_config.h`) OR `MQTT_DO_NOT_USE_CUSTOM_CONFIG` macro needs to be
provided to build the MQTT library.

For a CMake example of building the MQTT library with the `mqttFilePaths.cmake`
file, refer to the `coverity_analysis` library target in
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
git submodule update --checkout --init --recursive test/unit-test/CMock
```

### Platform Prerequisites

- Docker

or the following:

- For running unit tests
  - **C90 compiler** like gcc
  - **CMake 3.13.0 or later**
  - **Ruby 2.0.0 or later** is additionally required for the CMock test
    framework (that we use).
- For running the coverage target, **gcov** and **lcov** are additionally
  required.

### Steps to build **Unit Tests**

1. If using docker, launch the container:

   1. `docker build -t coremqtt .`
   1. `docker run -it -v "$PWD":/workspaces/coreMQTT -w /workspaces/coreMQTT coremqtt`

1. Go to the root directory of this repository. (Make sure that the **CMock**
   submodule is cloned as described [above](#checkout-cmock-submodule))

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

Please refer to the demos of the MQTT client library in the following locations
for reference examples on POSIX and FreeRTOS platforms:

| Platform |                                                    Location                                                    |         Transport Interface Implementation         |
| :------: | :------------------------------------------------------------------------------------------------------------: | :------------------------------------------------: |
|  POSIX   | [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main/demos/mqtt) | POSIX sockets for TCP/IP and OpenSSL for TLS stack |
| FreeRTOS |             [FreeRTOS/FreeRTOS](https://github.com/FreeRTOS/FreeRTOS/tree/main/FreeRTOS-Plus/Demo)             | FreeRTOS+TCP for TCP/IP and mbedTLS for TLS stack  |
| FreeRTOS |     [FreeRTOS AWS Reference Integrations](https://github.com/aws/amazon-freertos/tree/main/demos/coreMQTT)     |        Based on Secure Sockets Abstraction         |

## Documentation

### Existing Documentation

For pre-generated documentation, please see the documentation linked in the
locations below:

|                                                       Location                                                       |
| :------------------------------------------------------------------------------------------------------------------: |
| [AWS IoT Device SDK for Embedded C](https://github.com/aws/aws-iot-device-sdk-embedded-C#releases-and-documentation) |
|       [FreeRTOS.org](https://freertos.org/Documentation/api-ref/coreMQTT/docs/doxygen/output/html/index.html)        |

Note that the latest included version of coreMQTT may differ across
repositories.

### Generating Documentation

The Doxygen references were created using Doxygen version 1.9.2. To generate the
Doxygen pages, please run the following command from the root of this
repository:

```shell
doxygen docs/doxygen/config.doxyfile
```

## Contributing

See [CONTRIBUTING.md](./.github/CONTRIBUTING.md) for information on
contributing.
