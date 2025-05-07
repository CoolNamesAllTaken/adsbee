# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# Fleet Provisioning library source files.
set( FLEET_PROVISIONING_SOURCES
     "${CMAKE_CURRENT_LIST_DIR}/source/fleet_provisioning.c" )

# Fleet Provisioning library public include directories.
set( FLEET_PROVISIONING_INCLUDE_PUBLIC_DIRS
     "${CMAKE_CURRENT_LIST_DIR}/source/include" )
