cmake_minimum_required(VERSION 3.22.0)

project(
  "AWS IoT Jobs Tests"
  VERSION 1.5.1
  LANGUAGES C)

# Allow the project to be organized into folders.
set_property(GLOBAL PROPERTY USE_FOLDERS ON)

if(NOT DEFINED CMAKE_C_STANDARD)
  set(CMAKE_C_STANDARD 99)
endif()
if(NOT DEFINED CMAKE_C_STANDARD_REQUIRED)
  set(CMAKE_C_STANDARD_REQUIRED ON)
endif()

# If no configuration is defined, turn everything on.
if( NOT DEFINED COV_ANALYSIS AND NOT DEFINED UNITTEST )
    set( COV_ANALYSIS TRUE )
    set( UNITTEST TRUE )
endif()

# Do not allow in-source build.
if(${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR})
  message(
    FATAL_ERROR
      "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build."
  )
endif()

# Set global path variables.
get_filename_component(__MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/.."
                       ABSOLUTE)
set(MODULE_ROOT_DIR
    ${__MODULE_ROOT_DIR}
    CACHE INTERNAL "Jobs repository root.")

include(FetchContent)

FetchContent_Declare(
  CMock
  GIT_REPOSITORY https://github.com/ThrowTheSwitch/CMock.git
  GIT_TAG ed29ce388f4478bda1bdfb274d371e961b671c2b)

FetchContent_Declare(
  CoreJSON
  # hash: sha256-r0lJff61NK2rPtO7Wr6RudFNQiLt1D4M30V7/p60Zi0=
  GIT_REPOSITORY https://github.com/FreeRTOS/coreJSON.git
  GIT_TAG dc1ab9130a1fb99b801a2a1fa8e9f42239f752be)

FetchContent_MakeAvailable(CMock CoreJSON)

# Add coreJSON library
include("${corejson_SOURCE_DIR}/jsonFilePaths.cmake")
add_library(coreJSON ${JSON_SOURCES})
target_include_directories(coreJSON PUBLIC ${JSON_INCLUDE_PUBLIC_DIRS})

# ================================ Coverity Analysis Configuration =================================

if( COV_ANALYSIS )
  # Include filepaths for source and include.
  include( ${MODULE_ROOT_DIR}/jobsFilePaths.cmake )
  # Target for Coverity analysis that builds the library.
  add_library( coverity_analysis
              ${JOBS_SOURCES}
              ${OTA_HANDLER_SOURCES} )
  # JOBS public include path.
  target_include_directories( coverity_analysis PUBLIC ${JOBS_INCLUDE_PUBLIC_DIRS}
                                                      ${OTA_HANDLER_INCLUDES} )

  target_link_libraries(coverity_analysis PUBLIC coreJSON)

  # Build HTTP library target without logging
  target_compile_options(coverity_analysis PUBLIC -DNDEBUG )
endif()

# ==================================================================================================
if( UNITTEST )
  add_library(
    unity STATIC
    "${cmock_SOURCE_DIR}/vendor/unity/src/unity.c"
    "${cmock_SOURCE_DIR}/vendor/unity/extras/fixture/src/unity_fixture.c"
    "${cmock_SOURCE_DIR}/vendor/unity/extras/memory/src/unity_memory.c")
  target_include_directories(
    unity
    PUBLIC "${cmock_SOURCE_DIR}/vendor/unity/src"
          "${cmock_SOURCE_DIR}/vendor/unity/extras/fixture/src"
          "${cmock_SOURCE_DIR}/vendor/unity/extras/memory/src"
          "${cmock_SOURCE_DIR}/src")

  set_target_properties(
    unity PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib
                    POSITION_INDEPENDENT_CODE ON)

  add_library(cmock STATIC)
  target_sources(cmock PRIVATE ${cmock_SOURCE_DIR}/src/cmock.c)
  target_include_directories(
    cmock
    PUBLIC "${cmock_SOURCE_DIR}/src"
          "${cmock_SOURCE_DIR}/vendor/unity/src/"
          "${cmock_SOURCE_DIR}/examples"
          "${cmock_SOURCE_DIR}/vendor/unity/extras/fixture/src"
          "${cmock_SOURCE_DIR}/vendor/unity/extras/memory/src")
  set_target_properties(
    cmock
    PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib
              POSITION_INDEPENDENT_CODE ON
              COMPILE_FLAGS "-Og")

# ====================================  Test Configuration ========================================

  # Use CTest utility for managing test runs. This has to be added BEFORE defining
  # test targets with add_test()
  enable_testing()

  # Add function to enable CMock based tests and coverage.
  include(${MODULE_ROOT_DIR}/tools/cmock/create_test.cmake)

  # Include build configuration for unit tests.
  add_subdirectory(unit-test)

  # ==================================== Coverage Analysis configuration ========================================

  # Add a target for running coverage on tests.
  add_custom_target(
    coverage
    COMMAND ${CMAKE_COMMAND} -DCMOCK_DIR=${cmock_SOURCE_DIR} -P
            ${MODULE_ROOT_DIR}/tools/cmock/coverage.cmake
    DEPENDS cmock unity jobs_utest ota_job_handler_utest job_parser_utest
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR})
endif()
