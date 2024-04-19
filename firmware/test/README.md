# Cross-Compiled Unit Tests

## Running Unit Tests
1. Make sure the CMake Build Kit is set to Linux GCC (from the docker container).
2. Run the following commands:
    ```bash
    cd /ads_bee/test/build
    cmake ..
    make
    ./ads_bee_test
    ```

## Unit Test Structure
Individual parts of the program are unit tested with their corresponding unit test file. For instance, `ads_bee.cc` is unit tested using `test_ads_bee.cc`. Cross-compiled unit tests try to avoid including files that interface a lot with the Pico SDK libaries, since that would require a lot of mocking effort. Thus. the ADSBee class is only tested on target. Higher level classes that don't include calls to hardware functions, like ADSBPacket, are tested in cross compilation.

Some functionality for mocking system calls is available through `hal_god_powers.hh`.