This directory contains scripts used to set up the ARM compiler and debugging toolchain on Linux, since ARM discontinued releasing their tools on launchpad. Installation scripts are based on [this](https://askubuntu.com/a/1243405) stackexchange answer by Aleksander Khoroshko.

## Install Instructions
Open a terminal and run the following script with sudo.
```bash
sudo bash install_arm_none_eabi.sh
```

## Scripts
### install\_arm\_none\_eabi.sh
Downloads, un-tars, and installs gcc, g++, gdb, and size from ARM's website.

## Check that it works!
```bash
arm-none-eabi-gcc --version
arm-none-eabi-g++ --version
arm-none-eabi-gdb --version
arm-none-eabi-size --version
```

