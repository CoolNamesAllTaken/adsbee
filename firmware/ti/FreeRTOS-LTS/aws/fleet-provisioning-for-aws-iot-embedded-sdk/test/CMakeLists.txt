cmake_minimum_required ( VERSION 3.22.0 )
project ( "Fleet Provisioning unit test"
          VERSION 1.2.1
          LANGUAGES C )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )

# Use C90.
set( CMAKE_C_STANDARD 90 )
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

# Set global path variable.
get_filename_component( __MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/.." ABSOLUTE )
set( MODULE_ROOT_DIR ${__MODULE_ROOT_DIR} CACHE INTERNAL "Fleet Provisioning repository root." )
set( UNIT_TEST_DIR ${MODULE_ROOT_DIR}/test/unit-test CACHE INTERNAL "Fleet Provisioning unit test directory." )
set( UNITY_DIR ${UNIT_TEST_DIR}/Unity CACHE INTERNAL "Unity library source directory." )

# Configure options to always show in CMake GUI.
option( BUILD_CLONE_SUBMODULES
        "Set this to ON to automatically clone any required Git submodules. When OFF, submodules must be manually cloned."
        ON )

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

#  ====================== Coverity Analysis Configuration ======================

if( COV_ANALYSIS )
    # Include filepaths for source and include.
    include( ${MODULE_ROOT_DIR}/fleetprovisioningFilePaths.cmake )

    # Target for Coverity analysis that builds the library.
    add_library( coverity_analysis
                ${FLEET_PROVISIONING_SOURCES} )

    # Fleet Provisioning public include path and test config file.
    target_include_directories( coverity_analysis PUBLIC
                                ${FLEET_PROVISIONING_INCLUDE_PUBLIC_DIRS}
                                "${CMAKE_CURRENT_LIST_DIR}/include" )


    # Build without debug enabled when performing static analysis
    target_compile_options(coverity_analysis PUBLIC -DNDEBUG -DDISABLE_LOGGING)
endif()

#  ============================  Test Configuration ============================

if( UNITTEST )
    # Include Unity build configuration.
    include( unit-test/unity_build.cmake )

    # Check if the Unity source directory exists. If it does not exist and the
    # BUILD_CLONE_SUBMODULES configuration is enabled, clone the Unity submodule.
    if( NOT EXISTS ${UNITY_DIR}/src )
        # Attempt to clone Unity.
        if( ${BUILD_CLONE_SUBMODULES} )
            clone_unity()
        else()
            message( FATAL_ERROR "The required submodule Unity does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
        endif()
    endif()

    # Use CTest utility for managing test runs.
    enable_testing()

    # Add build target for Unity, required for unit testing.
    add_unity_target()

    # Add functions to enable Unity based tests and coverage.
    include( ${MODULE_ROOT_DIR}/tools/unity/create_test.cmake )

    # Include build configuration for unit tests.
    add_subdirectory( unit-test )

    #  ====================== Coverage Analysis configuration ======================

    # Add a target for running coverage on tests.
    add_custom_target( coverage
                       COMMAND ${CMAKE_COMMAND} -DUNITY_DIR=${UNITY_DIR}
                       -P ${MODULE_ROOT_DIR}/tools/unity/coverage.cmake
                       DEPENDS unity fleet_provisioning_utest
                       WORKING_DIRECTORY ${CMAKE_BINARY_DIR} )
endif()
