# Include filepaths for Device Defender library.
include( ${MODULE_ROOT_DIR}/defenderFilePaths.cmake )

set( library_name "defender" )
set( library_target_name "${library_name}_target" )
set( utest_binary_name "${library_name}_utest" )

# =========================== Library ==============================

# List of library source files.
list( APPEND library_source_files
             ${DEFENDER_SOURCES} )

# List of library include directories.
list( APPEND library_include_directories
      ${DEFENDER_INCLUDE_PUBLIC_DIRS}
      "${CMAKE_CURRENT_LIST_DIR}/../include" )

# Create a target for building library.
create_library_target( ${library_target_name}
                       "${library_source_files}"
                       "${library_include_directories}" )

# =========================== Test Binary ==============================

# The source file containing the unit tests.
set( utest_source_file "defender_utest.c" )

# The list of include directories for the test binary target.
list( APPEND utest_include_directories
             ${DEFENDER_INCLUDE_PUBLIC_DIRS} )

# Libraries to be linked while building the test binary.
list( APPEND utest_link_list
             lib${library_target_name}.a )

# The targets on which the test binary target depends.
list( APPEND utest_dep_list
             ${library_target_name} )

# Create a target for the test binary.
create_test_binary_target( ${utest_binary_name}
                           ${utest_source_file}
                           "${utest_link_list}"
                           "${utest_dep_list}"
                           "${test_include_directories}" )
