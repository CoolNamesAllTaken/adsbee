# Ubuntu 20.04 LTS supported by the TI SimpleLink SDK
FROM ubuntu

# NOTE: don't run this before updating all git submodules, e.g. tinyusb for the pico SDK!

# Install sudo to allow the use of scripts meant for use in non-root environment.
RUN ["/usr/bin/bash", "-c", "apt-get update && apt-get -y install sudo"]
RUN ["/usr/bin/bash", "-c", "apt-get -y install wget"]

ENV CMAKE=/usr/bin/cmake

# Install GDB for local debugging
RUN ["/usr/bin/bash", "-c", "apt-get -y install gdb"]

# Copy over the setup scripts.
COPY scripts /usr/setup_scripts
WORKDIR /usr/setup_scripts

# Install ARM toolchain and dependencies.
RUN ["chmod", "+x", "/usr/setup_scripts/setup_arm_none_eabi/install_arm_none_eabi.sh"]
RUN ["/usr/bin/bash", "-c", "/usr/setup_scripts/setup_arm_none_eabi/install_arm_none_eabi.sh"]
ENV GCC_ARMCOMPILER=/usr/local/gcc-arm-none-eabi-13.3.1

# Install JLink toolchain and dependencies.
RUN ["chmod", "+x", "/usr/setup_scripts/setup_jlink/install_jlink.sh"]
RUN ["/usr/bin/bash", "-c", "/usr/setup_scripts/setup_jlink/install_jlink.sh"]

# Install TI Low Power SimpleLink SDK
COPY simplelink-lowpower-f2-sdk /usr/local/ti-lpf2-sdk
ENV TI_LPF2_SDK_PATH=/usr/local/ti-lpf2-sdk
# Override the default imports.mak file.
COPY imports.mak /usr/local/ti-lpf2-sdk/imports.mak
# Install dependencies.
RUN ["chmod", "+x", "/usr/setup_scripts/setup_ti_lpf2_sdk/install_dependencies.sh"]
RUN ["/usr/bin/bash", "-c", "/usr/setup_scripts/setup_ti_lpf2_sdk/install_dependencies.sh"]
ENV CMAKE_C_COMPILER=/usr/bin/arm-none-eabi-gcc
ENV CMAKE_CXX_COMPILER=/usr/bin/arm-none-eabi-g++
ENV CMAKE_ASM_COMPILER=/usr/bin/arm-none-eabi-as
ENV PYTHON=/usr/bin/python3
WORKDIR /usr/local/ti-lpf2-sdk
# Make with multiple threads fails due to a bad file descriptor :(
RUN make
# RUN ["/usr/bin/bash", "-c", "cd /usr/local/ti-lpf2-sdk && make -j4"]
