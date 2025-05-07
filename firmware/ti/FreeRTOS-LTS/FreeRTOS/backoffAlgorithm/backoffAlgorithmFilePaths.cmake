# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# Backoff Algorithm library source files.
set( BACKOFF_ALGORITHM_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/source/backoff_algorithm.c" )

# Backoff Algorithm library Public Include directories.
set( BACKOFF_ALGORITHM_INCLUDE_PUBLIC_DIRS
     "${CMAKE_CURRENT_LIST_DIR}/source/include" )
