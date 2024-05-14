# Distributed under the OSI-approved BSD 3-Clause License.  See accompanying
# file Copyright.txt or https://cmake.org/licensing for details.

cmake_minimum_required(VERSION 3.5)

file(MAKE_DIRECTORY
  "/usr/local/pico-sdk/tools/pioasm"
  "/ads_bee/modules/build/pioasm"
  "/ads_bee/modules/build/pico-sdk/src/rp2_common/tinyusb/pioasm"
  "/ads_bee/modules/build/pico-sdk/src/rp2_common/tinyusb/pioasm/tmp"
  "/ads_bee/modules/build/pico-sdk/src/rp2_common/tinyusb/pioasm/src/PioasmBuild-stamp"
  "/ads_bee/modules/build/pico-sdk/src/rp2_common/tinyusb/pioasm/src"
  "/ads_bee/modules/build/pico-sdk/src/rp2_common/tinyusb/pioasm/src/PioasmBuild-stamp"
)

set(configSubDirs )
foreach(subDir IN LISTS configSubDirs)
    file(MAKE_DIRECTORY "/ads_bee/modules/build/pico-sdk/src/rp2_common/tinyusb/pioasm/src/PioasmBuild-stamp/${subDir}")
endforeach()
if(cfgdir)
  file(MAKE_DIRECTORY "/ads_bee/modules/build/pico-sdk/src/rp2_common/tinyusb/pioasm/src/PioasmBuild-stamp${cfgdir}") # cfgdir has leading slash
endif()
