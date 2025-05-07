FROM ubuntu
ADD . /usr/setup
WORKDIR /usr/setup

# NOTE: don't run this before updating all git submodules, e.g. tinyusb for the pico SDK!

# Install sudo to allow the use of scripts meant for use in non-root environment.
RUN ["/usr/bin/bash", "-c", "apt update && apt -y install sudo"]
RUN ["/usr/bin/bash", "-c", "apt -y install wget"]

# Install ARM toolchain and dependencies.
RUN ["chmod", "+x", "/usr/setup/setup_arm_none_eabi/install_arm_none_eabi.sh"]
RUN ["/usr/bin/bash", "-c", "/usr/setup/setup_arm_none_eabi/install_arm_none_eabi.sh"]

# Install JLink toolchain and dependencies.
RUN ["chmod", "+x", "/usr/setup/setup_jlink/install_jlink.sh"]
RUN ["/usr/bin/bash", "-c", "/usr/setup/setup_jlink/install_jlink.sh"]

# Install TI Low Power SimpleLink SDK
ADD simplelink-lowpower-f2-sdk /usr/local/ti-lpf2-sdk
ENV TI_LPF2_SDK_PATH=/usr/local/ti-lpf2-sdk
RUN ["chmod", "+x", "/usr/setup/setup_ti_lpf2_sdk/install_dependencies.sh"]
RUN ["/usr/bin/bash", "-c", "/usr/setup/setup_ti_lpf2_sdk/install_dependencies.sh"]

# Install GDB for local debugging
RUN ["/usr/bin/bash", "-c", "apt -y install gdb"]

# Override valies in imports.mak in lpf2-sdk
ENV CMAKE=/usr/bin/cmake
ENV PYTHON=/usr/bin/python3
ENV GCC_ARMCOMPILER=/usr/bin/arm-none-eabi-gcc

# XDC_INSTALL_DIR        ?= /home/username/ti/xdctools_3_62_01_15_core
# SYSCONFIG_TOOL         ?= /home/username/ti/ccs1270/ccs/utils/sysconfig_1.21.1/sysconfig_cli.sh

# CMAKE                  ?= /home/username/cmake-3.21.3/bin/cmake
# PYTHON                 ?= python3

# TICLANG_ARMCOMPILER    ?= /home/username/ti/ccs1270/ccs/tools/compiler/ti-cgt-armllvm_3.2.2.LTS-0
# GCC_ARMCOMPILER        ?= /home/username/arm-none-eabi-gcc/12.3.Rel1-0
# IAR_ARMCOMPILER        ?= /home/username/iar9.50.2
