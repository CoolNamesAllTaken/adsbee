#!/bin/bash

latest_arm_none_eabi=gcc-arm-none-eabi-10.3-2021.10
latest_arm_none_eabi_url=https://developer.arm.com/-/media/Files/downloads/gnu-rm/10.3-2021.10/gcc-arm-none-eabi-10.3-2021.10-x86_64-linux.tar.bz2

sudo apt remove gcc-arm-none-eabi

mkdir temp
wget -O temp/${latest_arm_none_eabi}.tar.bz2 $latest_arm_none_eabi_url
sudo tar xjf temp/${latest_arm_none_eabi}.tar.bz2 -C /usr/share/
sudo ln -s /usr/share/${latest_arm_none_eabi}/bin/arm-none-eabi-gcc /usr/bin/arm-none-eabi-gcc
sudo ln -s /usr/share/${latest_arm_none_eabi}/bin/arm-none-eabi-g++ /usr/bin/arm-none-eabi-g++
sudo ln -s /usr/share/${latest_arm_none_eabi}/bin/arm-none-eabi-gdb /usr/bin/arm-none-eabi-gdb
sudo ln -s /usr/share/${latest_arm_none_eabi}/bin/arm-none-eabi-size /usr/bin/arm-none-eabi-size
sudo ln -s /usr/share/${latest_arm_none_eabi}/bin/arm-none-eabi-objcopy /usr/bin/arm-none-eabi-objcopy
sudo ln -s /usr/share/${latest_arm_none_eabi}/bin/arm-none-eabi-objdump /usr/bin/arm-none-eabi-objdump
# Add other required commands here!

rm -rf temp
