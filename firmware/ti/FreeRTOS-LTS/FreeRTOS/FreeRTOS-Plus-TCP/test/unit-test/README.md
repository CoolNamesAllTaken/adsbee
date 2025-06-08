# Unit Tests for FreeRTOS-Plus-TCP library

This directory is made for the purpose of Unit testing and tries to provide the
tools for developing unit tests. To that end, this directory submodules the
[CMock](https://github.com/ThrowTheSwitch/CMock) framework (which submodules
[Unity](https://github.com/throwtheswitch/unity/))
and the [FreeRTOS-Kernel](https://github.com/FreeRTOS/FreeRTOS-Kernel/).

## Getting Started

### Prerequisites

You can run this on any GNU Make compatible systems. But in case of DOS based
systems some tweaking is required with the makefile. To compile and run this
project successfully, you must have the following:

1. Make (You can check whether you have this by typing `make --version`)
   - Not found? Try `apt-get install make`.
2. Ruby (You can check whether you have this by typing `ruby --version`)
   - Not found? Try `apt-get install ruby`.
3. CMake version > 3.15.0 (You can check whether you have this by typing
   `cmake --version`)
   - Not found? Try `apt-get install cmake`
   - Try the `cmake --version` command. If still the version number is >=
     3.15.0, skip to (4.) or else, continue.
   - You will need to get the latest CMake version using curl or wget (or
     similar command).
     - Uninstall the current version of CMake using
       `sudo apt remove --purge --auto-remove cmake`.
     - Download the [CMAKE version 3.15.0](https://cmake.org/files/v3.15/).
     - Extract the cmake download using `tar -xzvf cmake-3.15.0.tar.gz`.
     - Go to the extracted folder (`cd cmake-3.15.0`) and run `./bootstrap`.
     - Run `make -j$(nproc)' and then run `sudo make install`.
     - Check the version using `cmake --version` command.
4. lcov version 1.14 ( check with --version option )
   - 'sudo apt-get install lcov'
5. unifdef version 2.10 ( check with -V option )
   - 'sudo apt-get install unifdef'
6. Download the repo and include the submodules using the following commands.
   - `git clone https://github.com/FreeRTOS/FreeRTOS.git ./FreeRTOS_Dir`
   - `git submodule update --checkout --init --recursive tools/CMock test/FreeRTOS-Kernel`

### To run the Unit tests:

Go to the root directory of the FreeRTOS+TCP repo and run the following script:

```
#!/bin/bash
# This script should be run from the root directory of the FreeRTOS+TCP repo.

if [[ ! -d source ]]; then
    echo "Please run this script from the root directory of the FreeRTOS+TCP repo."
    exit 1
fi

UNIT_TEST_DIR="test/unit-test"
BUILD_DIR="${UNIT_TEST_DIR}/build/"

# Create the build directory using CMake:
rm -rf ${BUILD_DIR}
cmake -S ${UNIT_TEST_DIR} -B ${BUILD_DIR}

# Create the executables:
make -C ${BUILD_DIR} all

pushd ${BUILD_DIR}
# Run the tests for all units
ctest -E system --output-on-failure
popd

# Calculate the coverage
make -C ${BUILD_DIR} coverage
lcov --list --rc lcov_branch_coverage=1 ${BUILD_DIR}coverage.info
```

You should see an output similar to this:

```
-----------------------
6 Tests 0 Failures 0 Ignored
OK
Capturing coverage data from .
... <Skipped some lines here for the sake of brevity>
Overall coverage rate:
  lines......: 84.8% (56 of 66 lines)
  functions..: 85.7% (12 of 14 functions)
  branches...: 50.0% (2 of 4 branches)
```

And also:

```
Reading tracefile test/unit-test/build/coverage.info
                                |Lines       |Functions  |Branches
Filename                        |Rate     Num|Rate    Num|Rate     Num
======================================================================
[/home/hein/freertos_plus_tcp/]
FreeRTOS_ARP.c                  | 100%    238| 100%    14|99.3%    137
FreeRTOS_DHCP.c                 |98.7%    314|92.9%    14| 100%    150
FreeRTOS_Sockets.c              | 3.5%   1150| 1.6%    61| 4.2%    722
FreeRTOS_Stream_Buffer.c        | 100%    107| 100%    12| 100%     54
FreeRTOS_UDP_IP.c               | 100%     97| 100%     2| 100%     58
======================================================================
                          Total:|41.6%   1906|40.8%   103|38.2%   1121
```
