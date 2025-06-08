# Minimum required version of CMake
cmake_minimum_required ( VERSION 3.15.0 )

# Name of the project
project ( "FreeRTOS+TCP Static analysis"
          VERSION 1.0.0
          LANGUAGES C )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )
set(CMAKE_VERBOSE_MAKEFILE ON)

# Use C90.
set( CMAKE_C_STANDARD 90 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Set global path variables.
get_filename_component(__MODULE_ROOT_DIR "${CMAKE_CURRENT_LIST_DIR}/../.." ABSOLUTE)
set( MODULE_ROOT_DIR ${__MODULE_ROOT_DIR} CACHE INTERNAL "FreeRTOS-Plus-TCP repository root." )

# Set the kernel directory
set( KERNEL_DIRECTORY ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel )

# If the kernel is not submoduled, download it.
if( NOT EXISTS ${KERNEL_DIRECTORY}/include )
    # Inform the user of the actions
    message( STATUS "FreeRTOS-Kernel is required for this build. Submoduling it..." )
    execute_process( COMMAND git submodule update --init --checkout ${KERNEL_DIRECTORY}
                     WORKING_DIRECTORY ${MODULE_ROOT_DIR} )
endif()

# Add kernel sources to a list
file( GLOB KERNEL_SOURCES
           ${KERNEL_DIRECTORY}/*.c )

# Add TCP sources to a list
file( GLOB TCP_SOURCES
           ${MODULE_ROOT_DIR}/source/*.c )

# A better way would be to create a library such that all other dependencies are
# ignored by the static analysis tool. But, since +TCP is very closely linked
# with the FreeRTOS-Kernel, an executable had to be created.

# Add the executable for static analysis
add_executable( StaticAnalysis ${TCP_SOURCES}
                               ${KERNEL_SOURCES}
                               ${CMAKE_CURRENT_LIST_DIR}/Portable.c
                               ${MODULE_ROOT_DIR}/source/portable/BufferManagement/BufferAllocation_2.c )

# Link the include directories with the target
target_include_directories( StaticAnalysis
                            PUBLIC "${KERNEL_DIRECTORY}/include"
                            PUBLIC "${MODULE_ROOT_DIR}/test/Coverity/ConfigFiles"
                            PUBLIC "${MODULE_ROOT_DIR}/source/include" )

# Uncomment the below line if the desired platform is 32-bit
set_target_properties( StaticAnalysis PROPERTIES COMPILE_FLAGS "-m32" LINK_FLAGS "-m32" )
