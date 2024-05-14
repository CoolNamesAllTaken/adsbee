set(CMAKE_HOST_SYSTEM "Linux-5.15.146.1-microsoft-standard-WSL2")
set(CMAKE_HOST_SYSTEM_NAME "Linux")
set(CMAKE_HOST_SYSTEM_VERSION "5.15.146.1-microsoft-standard-WSL2")
set(CMAKE_HOST_SYSTEM_PROCESSOR "x86_64")

include("/usr/local/pico-sdk/cmake/preload/toolchains/pico_arm_gcc.cmake")

set(CMAKE_SYSTEM "PICO")
set(CMAKE_SYSTEM_NAME "PICO")
set(CMAKE_SYSTEM_VERSION "")
set(CMAKE_SYSTEM_PROCESSOR "cortex-m0plus")

set(CMAKE_CROSSCOMPILING "TRUE")

set(CMAKE_SYSTEM_LOADED 1)
