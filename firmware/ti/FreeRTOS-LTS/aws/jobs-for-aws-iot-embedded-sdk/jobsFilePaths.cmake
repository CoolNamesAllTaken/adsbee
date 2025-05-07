# This file adds source files and include directories
# into variables for use from different repositories
# in their Cmake based build systems.  Only the library
# files are added.

# JOBS library source files.
set( JOBS_SOURCES
     ${CMAKE_CURRENT_LIST_DIR}/source/jobs.c )

# JOBS library Public Include directories.
set( JOBS_INCLUDE_PUBLIC_DIRS
     ${CMAKE_CURRENT_LIST_DIR}/source/include )

# OTA Parser source files
set( OTA_HANDLER_SOURCES
     ${CMAKE_CURRENT_LIST_DIR}/source/otaJobParser/job_parser.c
     ${CMAKE_CURRENT_LIST_DIR}/source/otaJobParser/ota_job_handler.c )

# OTA Parser Public Include directories.
set( OTA_HANDLER_INCLUDES
     ${CMAKE_CURRENT_LIST_DIR}/source/otaJobParser/include )
