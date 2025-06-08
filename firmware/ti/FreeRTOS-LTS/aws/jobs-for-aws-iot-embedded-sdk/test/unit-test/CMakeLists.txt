cmake_minimum_required(VERSION 3.16.0)
project(
  "AWS IoT Jobs Tests"
  VERSION 1.5.0
  LANGUAGES C)

# Include filepaths for source and include.
include(${MODULE_ROOT_DIR}/jobsFilePaths.cmake)
include("${corejson_SOURCE_DIR}/jsonFilePaths.cmake")

# ====================  Define your project name (edit) ========================
set(project_name "jobs")

# =====================  Create your mock here  (edit)  ========================

# list the files to mock here
list(APPEND mock_list "${MODULE_ROOT_DIR}/source/otaJobParser/include/job_parser.h")

# list the directories your mocks need
list(APPEND mock_include_list "${MODULE_ROOT_DIR}/source/otaJobParser/include")
# list the definitions of your mocks to control what to be included
list(APPEND mock_define_list "")

# ================= Create the library under test here (edit) ==================

# Base name for temporary files
set( TEMP_BASE ${CMAKE_BINARY_DIR}/${project_name} )

# Strip static constraints so unit tests may call internal functions
execute_process( COMMAND sed "s/^static //"
                 WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                 INPUT_FILE ${JOBS_SOURCES}
                 OUTPUT_FILE ${TEMP_BASE}.c
        )

# Generate a header file for internal functions
execute_process( COMMAND sed -n "/^static.*(/,/^{\$/{s/^static //; s/)\$/&;/; /{/d; p;}"
                 WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                 INPUT_FILE ${JOBS_SOURCES}
                 OUTPUT_FILE ${TEMP_BASE}_annex.h
        )

execute_process(COMMAND cp ./source/otaJobParser/job_parser.c ./build/job_parser.c )

execute_process(COMMAND cp ./source/otaJobParser/ota_job_handler.c ./build/ota_job_handler.c )

set(OTA_HANDLER_TEST_SOURCES
        ${MODULE_ROOT_DIR}/build/job_parser.c
        ${MODULE_ROOT_DIR}/build/ota_job_handler.c)

# list the files you would like to test here
list(APPEND real_source_files ${OTA_HANDLER_TEST_SOURCES} ${JSON_SOURCES})
# list the directories the module under test includes
list(APPEND real_include_directories . ${OTA_HANDLER_INCLUDES}
     ${JSON_INCLUDE_PUBLIC_DIRS})
# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories . ${OTA_HANDLER_INCLUDES})

# =============================  (end edit)  ===================================

# Create ota_job_handler unit test
set(real_name "ota_job_handler_real")
set(utest_name "ota_job_handler_utest")
set(utest_source "ota_job_handler_utest.c")
set(mock_name "ota_job_handler_mock")
set(real_name "ota_job_handler_real")

create_mock_list(
  ${mock_name} "${mock_list}" "${MODULE_ROOT_DIR}/tools/cmock/project.yml"
  "${mock_include_list}" "${mock_define_list}")

create_real_library(${real_name} "${real_source_files}"
                    "${real_include_directories}" "${mock_name}")

list(APPEND utest_link_list -l${mock_name} lib${real_name}.a)

list(APPEND utest_dep_list ${real_name})

create_test(${utest_name} ${utest_source} "${utest_link_list}"
            "${utest_dep_list}" "${test_include_directories}")

# # Create job parser unit test
set(real_name "job_parser_real")
set(utest_name "job_parser_utest")
set(utest_source "job_parser_utest.c")
# No need to redefine mocks since we do not need any

set(utest_link_list "")
list(APPEND utest_dep_list ${real_name})

create_real_library(${real_name} "${real_source_files}"
                    "${real_include_directories}" "")

# Redefine the linked files to ignore the mock files
list(APPEND utest_link_list lib${real_name}.a)

create_test(${utest_name} ${utest_source} "${utest_link_list}"
            "${utest_dep_list}" "${test_include_directories}")

# Create jobs unit test
list(APPEND real_source_files ${TEMP_BASE}.c)
list(APPEND real_include_directories ${JOBS_INCLUDE_PUBLIC_DIRS})
list(APPEND test_include_directories ${JOBS_INCLUDE_PUBLIC_DIRS}
                                     ${CMAKE_BINARY_DIR})
set(real_name "jobs_real")

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    ""
        )

list(APPEND utest_link_list
        lib${real_name}.a
    )

list(APPEND utest_dep_list
            ${real_name}
        )

set(utest_name "jobs_utest")
set(utest_source "jobs_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )
