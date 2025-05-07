# AWS IoT Fleet Provisioning Library

**[API Documentation Pages for current and previous releases of this library can be found here](https://aws.github.io/Fleet-Provisioning-for-AWS-IoT-embedded-sdk/)**

The Fleet Provisioning library enables you to provision IoT devices without
device certificates using the [Fleet Provisioning feature of AWS IoT Core][a1].
For an overview of provisioning options available, see [Device
provisioning][a2]. This library has no dependencies on any additional libraries
other than the standard C library, and therefore, can be used with any MQTT
library. This library is distributed under the [MIT Open Source License][a3].

[a1]:
  https://docs.aws.amazon.com/iot/latest/developerguide/provision-wo-cert.html
[a2]: https://docs.aws.amazon.com/iot/latest/developerguide/iot-provision.html
[a3]: LICENSE

This library has gone through code quality checks including verification that no
function has a [GNU Complexity][a4] score over 8, and checks against deviations
from mandatory rules in the [MISRA coding standard][a5]. Deviations from the
MISRA C:2012 guidelines are documented under [MISRA Deviations][a6]. This
library has also undergone static code analysis using [Coverity static
analysis][a7], and validation of memory safety through the [CBMC automated
reasoning tool][a8].

[a4]: https://www.gnu.org/software/complexity/manual/complexity.html
[a5]: https://www.misra.org.uk
[a6]: MISRA.md
[a7]: https://scan.coverity.com/
[a8]: https://www.cprover.org/cbmc/

See memory requirements for this library [here][a9].

[a9]: ./docs/doxygen/include/size_table.md

**AWS IoT Fleet Provisioning Library v1.1.0
[source code](https://github.com/aws/Fleet-Provisioning-for-AWS-IoT-embedded-sdk/tree/v1.1.0/source)
is part of the
[FreeRTOS 202210.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202210.00-LTS)
release.**

## AWS IoT Fleet Provisioning Library Config File

The AWS IoT Fleet Provisioning Library exposes build configuration macros that
are required for building the library. A list of all the configurations and
their default values are defined in [fleet_provisioning_config_defaults.h][b1].
To provide custom values for the configuration macros, a config file named
`fleet_provisioning_config.h` can be provided by the application to the library.

[b1]: source/include/fleet_provisioning_config_defaults.h

By default, a `fleet_provisioning_config.h` config file is required to build the
library. To disable this requirement and build the library with default
configuration values, provide `FLEET_PROVISIONING_DO_NOT_USE_CUSTOM_CONFIG` as a
compile time preprocessor macro.

**Thus, the Fleet Provisioning library can be built by either**:

- Defining a `fleet_provisioning_config.h` file in the application, and adding
  it to the include directories list of the library.

**OR**

- Defining the `FLEET_PROVISIONING_DO_NOT_USE_CUSTOM_CONFIG` preprocessor macro
  for the library build.

## Building the Library

The [fleetprovisioningFilePaths.cmake][c1] file contains the information of all
source files and the header include paths required to build the Fleet
Provisioning library.

[c1]: fleetprovisioningFilePaths.cmake

As mentioned in the previous section, either a custom config file (i.e.
`fleet_provisioning_config.h`) or `FLEET_PROVISIONING_DO_NOT_USE_CUSTOM_CONFIG`
macro needs to be provided to build the Fleet Provisioning library.

For a CMake example of building the Fleet Provisioning library with the
`fleetprovisioningFilePaths.cmake` file, refer to the `coverity_analysis`
library target in [test/CMakeLists.txt][c2] file.

[c2]: test/CMakeLists.txt

## Building Unit Tests

### Platform Prerequisites

- For running unit tests:
  - **C90 compiler** like gcc.
  - **CMake 3.13.0 or later**.
- For running the coverage target, **gcov** and **lcov** are additionally
  required.

### Steps to build **Unit Tests**

1. Go to the root directory of this repository.

1. Run the _cmake_ command:
   `cmake -S test -B build -DBUILD_CLONE_SUBMODULES=ON`.

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

The [AWS IoT Embedded C-SDK repository][e1] contains a demo showing the use of
the AWS IoT Fleet Provisioning Library on a POSIX platform [here][e2].

[e1]: https://github.com/aws/aws-iot-device-sdk-embedded-C
[e2]:
  https://github.com/aws/aws-iot-device-sdk-embedded-C/tree/main/demos/fleet_provisioning/fleet_provisioning_with_csr

## Generating documentation

The Doxygen references were created using Doxygen version 1.9.6. To generate the
Doxygen pages, please run the following command from the root of this
repository:

```sh
doxygen docs/doxygen/config.doxyfile
```

## Contributing

See [CONTRIBUTING.md][g1] for information on contributing.

[g1]: .github/CONTRIBUTING.md
