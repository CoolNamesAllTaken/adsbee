# ADSBee MAVLINK C Library

Source is adapted from the MAVLINK [c_library_v2](https://github.com/mavlink/c_library_v2/tree/master/common).

The RP2040 is a Cortex M0+ processor, and thus does not support unaligned access. Functions that send messages using buffers are disabled on the Pico using the ON_PICO macro. Only sending via structs is allowed, as this ensures proper word alignment so that member variables can be accessed safely.

Most files are pulled from the `common` folder in the c_library_v2, but the heartbeat message is pulled from the `minimal` folder.