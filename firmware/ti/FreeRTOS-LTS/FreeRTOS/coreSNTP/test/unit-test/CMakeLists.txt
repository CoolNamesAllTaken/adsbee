# Include file path configuration for coreSNTP library.
include(${MODULE_ROOT_DIR}/coreSntpFilePaths.cmake)

project ("coreSNTP unit tests")
cmake_minimum_required (VERSION 3.2.0)

# ====================  Define your project name ========================
set(project_name "core_sntp")

# =====================  Create your mock here   ========================

# list the files to mock here
list(APPEND mock_list
        "${MODULE_ROOT_DIR}/source/include/core_sntp_serializer.h"
        )

# list the directories your mocks need
list(APPEND mock_include_list
                ${CORE_SNTP_INCLUDE_PUBLIC_DIRS}
        )
#list the definitions of your mocks to control what to be included
list(APPEND mock_define_list
                ""
        )

# ================= Create the library under test here ==================

# list the files you would like to test here
list(APPEND real_source_files
                ${CORE_SNTP_SOURCES}
        )

# list the directories the module under test includes
list(APPEND real_include_directories
                ${CORE_SNTP_INCLUDE_PUBLIC_DIRS}
                ${CMAKE_CURRENT_LIST_DIR}
        )

# =====================  Create UnitTest Code here   =====================

# list the directories your test needs to include
list(APPEND test_include_directories
                ${CORE_SNTP_INCLUDE_PUBLIC_DIRS}
                ${CMAKE_CURRENT_LIST_DIR}
        )

# ============================= Create unit test targets  ===================================

set(mock_name "${project_name}_mock")
set(real_name "${project_name}_real")

create_mock_list(${mock_name}
        "${mock_list}"
        "${MODULE_ROOT_DIR}/tools/cmock/project.yml"
        "${mock_include_list}"
        "${mock_define_list}"
)

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

# As both Mock and Real libraries targets contain the
# symbols for the core_sntp_serializer.c file, the linking
# order has the mock library first for the core_sntp_client_utest.c
# to use the mock for Serializer API calls.
list(APPEND utest_link_list
            -l${mock_name}
            lib${real_name}.a
        )

list(APPEND utest_dep_list
            ${real_name}
        )

# core_sntp_client_utest target
set(utest_name "${project_name}_client_utest")
set(utest_source "${project_name}_client_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

# Redefine the linking list as the mock is not needed for
# the core_sntp_serializer tests.
set(utest_link_list "")
list(APPEND utest_link_list
        lib${real_name}.a
    )

# core_sntp_serializer_utest target
set(utest_name "${project_name}_serializer_utest")
set(utest_source "${project_name}_serializer_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )
