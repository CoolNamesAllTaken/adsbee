# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# coreSNTP library source files.
set( CORE_SNTP_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/source/core_sntp_serializer.c"
     "${CMAKE_CURRENT_LIST_DIR}/source/core_sntp_client.c" )

# coreSNTP library Public Include directories.
set( CORE_SNTP_INCLUDE_PUBLIC_DIRS
     "${CMAKE_CURRENT_LIST_DIR}/source/include" )
