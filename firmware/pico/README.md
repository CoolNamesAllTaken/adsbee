## Troubleshooting
### RP2040 does not enumerate as a USB device when running program with USB functionality.

Make sure that tinyusb is installed by running `git submodule update --init` in the pico-sdk folder, then restarting the docker container to make sure it is copied over fresh!

### Getting a weird link issue.

Make sure that you added the file to the CMakeLists.txt file AND added its directory using `add_subdirectory()`!

### Need to see symbols properly when debugging

Run the following from the `firmware/build` directory: `cmake -DPICO_DEOPTIMIZED_DEBUG=1 ..`.

### Can't compile because arm-none-eabi-gcc or arm-none-eabi-gdb doesn't exist

In the docker container, navigate to `modules/setup-scripts` and re-run `sudo bash setup_arm_none_eabi/install_arm_none_eabi.sh`.

### ESP32 firmware file uploading but not executing correctly.

Delete the adsbee firmware build folder, then build and flash the RP2040 again!

### Building unit tests for host fails with `No rule to make target '/ads_bee/modules/googletest/build/lib/libgtest.so', needed by 'ads_bee_test'.  Stop.`

Need to build googletest. See the firmware README.