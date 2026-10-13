# The following lines of boilerplate have to be in your project's CMakeLists
# in this exact order for cmake to work correctly
cmake_minimum_required(VERSION 3.16)

add_compile_definitions(ON_ESP32)

include($ENV{IDF_PATH}/tools/cmake/project.cmake)
project(adsbee_esp)