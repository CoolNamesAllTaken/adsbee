#!/bin/bash

# Command line options documented here: https://kb.segger.com/J-Link_GDB_Server#Command_line_options

jlinkgdbserver -device CC1312R1F3 -endian little -speed 40000 -if cJTAG -port 2337