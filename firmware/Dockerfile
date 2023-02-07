FROM ubuntu
ADD modules/setup-scripts /usr/setup
WORKDIR /usr/setup

# NOTE: don't run this before updating all git submodules, e.g. tinyusb for the pico SDK!

# Install sudo to allow the use of scripts meant for use in non-root environment.
RUN ["/usr/bin/bash", "-c", "apt update && apt -y install sudo"]
RUN ["/usr/bin/bash", "-c", "apt -y install wget"]

# Install ARM toolchain and dependencies.
RUN ["/usr/bin/bash", "-c", "/usr/setup/setup_arm_none_eabi/install_arm_none_eabi.sh"]
RUN ["/usr/bin/bash", "-c", "/usr/setup/setup_arm_none_eabi/install_dependencies.sh"]

# Install JLink toolchain and dependencies.
RUN ["/usr/bin/bash", "-c", "/usr/setup/setup_jlink/install_jlink.sh"]
RUN ["/usr/bin/bash", "-c", "/usr/setup/setup_jlink/install_dependencies.sh"]

# Install Pico SDK
ADD modules/pico-sdk /usr/local/pico-sdk
ENV PICO_SDK_PATH /usr/local/pico-sdk
RUN ["/usr/bin/bash", "-c", "/usr/setup/setup_pico_sdk/install_dependencies.sh"]

# Install GDB for local debugging
RUN ["/usr/bin/bash", "-c", "apt -y install gdb"]
