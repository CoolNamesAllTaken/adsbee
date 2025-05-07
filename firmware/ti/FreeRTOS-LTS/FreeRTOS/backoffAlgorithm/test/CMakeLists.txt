cmake_minimum_required( VERSION 3.13.0 )
project( "backoffAlgorithm unit test"
         VERSION 1.4.1
         LANGUAGES C )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )

# Use C90.
set( CMAKE_C_STANDARD 90 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Set global path variables.
get_filename_component(__MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/.." ABSOLUTE)
set( MODULE_ROOT_DIR ${__MODULE_ROOT_DIR} CACHE INTERNAL "backoffAlgorithm source root." )
set( UNIT_TEST_DIR ${MODULE_ROOT_DIR}/test/unit-test CACHE INTERNAL "backoffAlgorithm unit test directory." )
set( UNITY_DIR ${UNIT_TEST_DIR}/Unity CACHE INTERNAL "Unity library source directory." )

# Configure options to always show in CMake GUI.
option( UNITTEST
        "Set this to ON to build unit tests. This will clone the required Unity test framework submodule if it is not cloned already."
        OFF )
option( COV_ANALYSIS
        "Set this to ON to build coverity analysis project."
	OFF )

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

# Include filepaths for source and include.
include( ${MODULE_ROOT_DIR}/backoffAlgorithmFilePaths.cmake )

# ================================ Coverity Analysis Configuration =================================
if( COV_ANALYSIS )

    # Target for Coverity analysis that builds the library.
    add_library( coverity_analysis
                ${BACKOFF_ALGORITHM_SOURCES} )

    # Backoff Algorithm library public include path.
    target_include_directories( coverity_analysis
                                PUBLIC
                                ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS} )

    # Disable logging/assert() calls when building the Coverity analysis target
    target_compile_options(coverity_analysis PUBLIC -DNDEBUG )
endif()

#  ==================================== Unit Test Configuration ====================================

if(${BUILD_CODE_EXAMPLE})

    # Target for code example binary.
    add_executable( code_example_posix
                    ${MODULE_ROOT_DIR}/docs/doxygen/code_examples/backoff_algorithm_posix.c
                    ${BACKOFF_ALGORITHM_SOURCES} )

    # Backoff Algorithm library public include path.
    target_include_directories( code_example_posix
                                PUBLIC
                                ${BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS} )
endif()

#  ==================================== Unit Test Configuration ====================================

if( UNITTEST )

    # Include Unity build configuration.
    include( unit-test/unity_build.cmake )

    # Check if the Unity source directory exists, and if not present, clone the submodule
    # if BUILD_CLONE_SUBMODULES configuration is enabled.
    if( NOT EXISTS ${UNITY_DIR}/src )
        # Attempt to clone Unity.
        if( ${BUILD_CLONE_SUBMODULES} )
            clone_unity()
        else()
            message( FATAL_ERROR "The required submodule Unity does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
        endif()

    endif()

    # Add unit test and coverage configuration.

    # Use CTest utility for managing test runs. This has to be added BEFORE
    # defining test targets with add_test()
    enable_testing()

    # Add build targets for Unity and Unit, required for unit testing.
    add_unity_targets()

    # Add function to enable Unity based tests and coverage.
    include( ${MODULE_ROOT_DIR}/tools/unity/create_test.cmake )

    # Include build configuration for unit tests.
    add_subdirectory( unit-test )

    #  ==================================== Coverage Analysis configuration ============================

    # Add a target for running coverage on tests.
    add_custom_target( coverage
        COMMAND ${CMAKE_COMMAND} -DUNITY_DIR=${UNITY_DIR}
        -P ${MODULE_ROOT_DIR}/tools/unity/coverage.cmake
        DEPENDS unity backoff_algorithm_utest
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    )

endif()
