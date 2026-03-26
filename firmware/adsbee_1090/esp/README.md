# Getting Started in WSL2
## Installation
1. Install idfx following [these instructions](https://github.com/abobija/idfx).
2. Install ESP-IDF in WSL2 following [this script](https://gist.github.com/abobija/2f11d1b2c7cb079bec4df6e2348d969f).

## Helpful commands
* `idf.py set-target esp32s3`
* `idf.py menuconfig`
* `idf.py build`
* `idfx flash COM2`
* `idfx monitor COM2`

## Killing a rogue OpenOCD app (in case debugger won't let you bind to a port because it's already in use)

### Kill with PID:
`lsof -n -i | grep ":6666"` (or whatever the port is).
`kill <pid>` with pid set to the process number for OpenOCD.

### Kill with Process Name:
`pkill openocd`