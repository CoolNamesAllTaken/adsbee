#!/bin/bash

# Command line options documented here: https://kb.segger.com/J-Link_GDB_Server#Command_line_options

jlinkgdbserver -device RP2040_M0_0 -endian little -speed adaptive -if SWD -port 2331