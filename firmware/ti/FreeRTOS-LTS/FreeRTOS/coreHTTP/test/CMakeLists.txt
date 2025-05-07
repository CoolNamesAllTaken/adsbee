# Project information.
cmake_minimum_required ( VERSION 3.13.0 )
project ( "coreHTTP tests"
          VERSION 3.1.1
          LANGUAGES C )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )

# Use C99 as llhttp requires C99.
set( CMAKE_C_STANDARD 99 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# If no configuration is defined, turn everything on.
if( NOT DEFINED COV_ANALYSIS AND NOT DEFINED UNITTEST )
    set( COV_ANALYSIS TRUE )
    set( UNITTEST TRUE )
endif()

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Set global path variables.
get_filename_component(__MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/.." ABSOLUTE)
set(MODULE_ROOT_DIR ${__MODULE_ROOT_DIR} CACHE INTERNAL "coreHTTP repository root.")

# Configure options to always show in CMake GUI.
option( BUILD_CLONE_SUBMODULES
        "Set this to ON to automatically clone any required Git submodules. When OFF, submodules must be manually cloned."
        ON )

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

# ====================== Coverity Analysis Configuration =======================

if( COV_ANALYSIS )
    # Include filepaths for source and include.
    include( ${MODULE_ROOT_DIR}/httpFilePaths.cmake )

    # Target for Coverity analysis that builds the library.
    add_library( coverity_analysis
                 ${CMAKE_CURRENT_LIST_DIR}/../source/core_http_client.c )

    # Build HTTP library target without custom config dependency.
    target_compile_definitions( coverity_analysis PUBLIC HTTP_DO_NOT_USE_CUSTOM_CONFIG=1 )

    # HTTP public include path.
    target_include_directories( coverity_analysis PUBLIC ${HTTP_INCLUDE_PUBLIC_DIRS} )

    target_compile_options( coverity_analysis PUBLIC
        # Build HTTP library target without logging
        -DNDEBUG

        # GCC compiler option
        -Wall
        -Wextra
        -Wpedantic
        -Wconversion
        -Werror
    )
endif()
# ===================== Clone needed third-party libraries ======================

# Define an llhttp parser resource path.
set( LLHTTP_DIR ${MODULE_ROOT_DIR}/source/dependency/3rdparty/llhttp CACHE INTERNAL "llhttp library source directory." )

include( llhttp_build.cmake )

# Check if the llhttp_source directory exists.
if( NOT EXISTS ${LLHTTP_DIR}/src/llhttp.c )
    # Attempt to clone llhttp.
    if( ${BUILD_CLONE_SUBMODULES} )
        clone_llhttp()
    else()
        message( FATAL_ERROR "The required submodule llhttp does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
    endif()
endif()

# ============================ Test configuration ==============================
if( UNITTEST )
    # Define a CMock resource path.
    set( CMOCK_DIR ${MODULE_ROOT_DIR}/test/unit-test/CMock CACHE INTERNAL "CMock library source directory." )

    # Include CMock build configuration.
    include( unit-test/cmock_build.cmake )

    # Check if the CMock source directory exists, and if not present, clone the submodule
    # if BUILD_CLONE_SUBMODULES configuration is enabled.
    if( NOT EXISTS ${CMOCK_DIR}/src )
        # Attempt to clone CMock.
        if( ${BUILD_CLONE_SUBMODULES} )
            clone_cmock()
        else()
            message( FATAL_ERROR "The required submodule CMock does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
        endif()
    endif()

    # Add unit test and coverage configuration.

    # Use CTest utility for managing test runs. This has to be added BEFORE
    # defining test targets with add_test()
    enable_testing()

    # Add build targets for CMock and Unit, required for unit testing.
    add_cmock_targets()

    # Add function to enable CMock based tests and coverage.
    include( ${MODULE_ROOT_DIR}/tools/cmock/create_test.cmake )

    # Include build configuration for unit tests.
    add_subdirectory( unit-test )

    #  ==================== Coverage Analysis configuration ========================

    # Add a target for running coverage on tests.
    add_custom_target( coverage
        COMMAND ${CMAKE_COMMAND} -DCMOCK_DIR=${CMOCK_DIR}
        -P ${MODULE_ROOT_DIR}/tools/cmock/coverage.cmake
        DEPENDS cmock unity core_http_utest core_http_send_utest
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    )
endif()
