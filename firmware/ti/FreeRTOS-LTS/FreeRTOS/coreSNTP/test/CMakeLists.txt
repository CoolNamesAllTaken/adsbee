cmake_minimum_required( VERSION 3.13.0 )
project( "coreSNTP tests"
         VERSION 1.3.1
         LANGUAGES C )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )

# Use C90.
set( CMAKE_C_STANDARD 90 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# If no configuration is defined, turn everything on.
if( NOT DEFINED COV_ANALYSIS AND NOT DEFINED UNITTEST AND NOT DEFINED BUILD_CODE_EXAMPLE )
    set( COV_ANALYSIS ON )
    set( UNITTEST ON )
    set( BUILD_CODE_EXAMPLE ON )
endif()

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Set global path variables.
get_filename_component(__MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/.." ABSOLUTE)
set( MODULE_ROOT_DIR ${__MODULE_ROOT_DIR} CACHE INTERNAL "coreSNTP source root." )
set( UNIT_TEST_DIR ${MODULE_ROOT_DIR}/test/unit-test CACHE INTERNAL "coreSNTP unit test directory." )
set( CMOCK_DIR ${UNIT_TEST_DIR}/CMock CACHE INTERNAL "Unity library source directory." )

# Configure options to always show in CMake GUI.
option( BUILD_CLONE_SUBMODULES
        "Set this to ON to automatically clone any required Git submodules. When OFF, submodules must be manually cloned."
        OFF )

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

# Include filepaths for source and include.
include( ${MODULE_ROOT_DIR}/coreSntpFilePaths.cmake )

# ================================ Coverity Analysis Configuration =================================

if( COV_ANALYSIS )

    # Target for Coverity analysis that builds the library.
    add_library( coverity_analysis
                 ${CORE_SNTP_SOURCES} )

    # Add coreSNTP library public include path.
    target_include_directories( coverity_analysis
                                PUBLIC
                                ${CORE_SNTP_INCLUDE_PUBLIC_DIRS} )

    # Build SNTP library target without custom config dependency.
    target_compile_definitions( coverity_analysis PUBLIC SNTP_DO_NOT_USE_CUSTOM_CONFIG=1 )

    # Build without debug enabled when performing static analysis
    target_compile_options(coverity_analysis PUBLIC -DNDEBUG )
endif()

#  ==================================== Code Example Build ====================================

if( BUILD_CODE_EXAMPLE )
    # Target for Coverity analysis that builds the library.
    add_executable( code_example_posix
                    ${CORE_SNTP_SOURCES}
                    ${MODULE_ROOT_DIR}/docs/doxygen/code_examples/example_sntp_client_posix.c )

    target_include_directories( code_example_posix
                                PUBLIC
                                ${CORE_SNTP_INCLUDE_PUBLIC_DIRS} )

    # Build SNTP library target without custom config dependency.
    target_compile_definitions( code_example_posix PUBLIC SNTP_DO_NOT_USE_CUSTOM_CONFIG=1 )

    # Build without debug enabled when performing static analysis
    target_compile_options( code_example_posix PUBLIC -DNDEBUG )
endif()

#  ==================================== Unit Test Configuration ====================================

if( UNITTEST )
    # Include CMock build configuration.
    include( unit-test/cmock_build.cmake )

    # Check if the CMock source directory exists, and if not present, clone the submodule
    # if BUILD_CLONE_SUBMODULES configuration is enabled.
    if( NOT EXISTS ${CMOCK_DIR}/src )
        # Attempt to clone CMock.
            clone_cmock()
    endif()

    # Add unit test and coverage configuration.

    # Use CTest utility for managing test runs. This has to be added BEFORE
    # defining test targets with add_test()
    enable_testing()

    # Add build targets for CMock, required for unit testing.
    add_cmock_targets()

    # Add function to enable CMock/Unity based tests and coverage.
    include( ${MODULE_ROOT_DIR}/tools/cmock/create_test.cmake )

    # Include build configuration for unit tests.
    add_subdirectory( unit-test )
endif()

#  ==================================== Coverage Analysis configuration ============================

# Add a target for running coverage on tests.
add_custom_target( coverage
    COMMAND ${CMAKE_COMMAND} -DCMOCK_DIR=${CMOCK_DIR}
    -P ${MODULE_ROOT_DIR}/tools/cmock/coverage.cmake
    DEPENDS cmock core_sntp_client_utest core_sntp_serializer_utest
    WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
)
