# ====================  Define your project name (edit) ========================
set(project_name "cellular")

# =====================  Create your mock here  (edit)  ========================

# list the files to mock here
list(APPEND mock_list
            "${CELLULAR_COMMON_INCLUDE_PRIVATE_DIRS}/cellular_pktio_internal.h"
            "${CELLULAR_COMMON_INCLUDE_DIRS}/cellular_common.h"
            "${CELLULAR_COMMON_INCLUDE_DIRS}/cellular_at_core.h"
            "${CELLULAR_COMMON_INCLUDE_DIRS}/cellular_common_portable.h"
        )

# list the directories your mocks need
list(APPEND mock_include_list
            .
            ${CMAKE_CURRENT_LIST_DIR}/logging
            ${CELLULAR_COMMON_INCLUDE_DIRS}
            ${CELLULAR_COMMON_INCLUDE_PRIVATE_DIRS}
            ${CELLULAR_INTERFACE_INCLUDE_DIRS}
            ${CELLULAR_INCLUDE_DIRS}
        )
#list the definitions of your mocks to control what to be included
list(APPEND mock_define_list
            "MOCK_LIB_TEST=1"
        )

# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            ${CELLULAR_COMMON_SOURCE_DIRS}/cellular_at_core.c
            ${CELLULAR_COMMON_SOURCE_DIRS}/cellular_pktio.c
            ${CELLULAR_COMMON_SOURCE_DIRS}/cellular_pkthandler.c
            ${CELLULAR_COMMON_SOURCE_DIRS}/cellular_common_api.c
            ${CELLULAR_COMMON_SOURCE_DIRS}/cellular_3gpp_urc_handler.c
            ${CELLULAR_COMMON_SOURCE_DIRS}/cellular_3gpp_api.c
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            .
            ${CMAKE_CURRENT_LIST_DIR}/logging
            ${CELLULAR_INCLUDE_DIRS}
            ${CELLULAR_INTERFACE_INCLUDE_DIRS}
            ${CELLULAR_COMMON_INCLUDE_DIRS}
            ${CELLULAR_COMMON_INCLUDE_PRIVATE_DIRS}
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            .
            ${CELLULAR_COMMON_INCLUDE_DIRS}
            ${CELLULAR_COMMON_INCLUDE_PRIVATE_DIRS}
            ${CELLULAR_INTERFACE_INCLUDE_DIRS}
        )

# =============================  (end edit)  ===================================

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

list(APPEND utest_link_list
            -l${mock_name}
            lib${real_name}.a
        )

list(APPEND utest_dep_list
            ${real_name}
        )

set(utest_name "${project_name}_pkthandler_utest")
set(utest_source "${project_name}_pkthandler_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

set(utest_name "${project_name}_common_api_utest")
set(utest_source "${project_name}_common_api_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

set(utest_name "${project_name}_3gpp_api_utest")
set(utest_source "${project_name}_3gpp_api_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

set(utest_name "${project_name}_3gpp_urc_handler_utest")
set(utest_source "${project_name}_3gpp_urc_handler_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

# The following unit test don't need mock module.

set(utest_name "${project_name}_at_core_utest")
set(utest_source "${project_name}_at_core_utest.c")

# need to redefine because the tests below don't use any mocks
set(utest_link_list "")
list(APPEND utest_link_list
                lib${real_name}.a
        )

create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

# cellular_pktio_utest
set(utest_name "${project_name}_pktio_utest")
set(utest_source "${project_name}_pktio_utest.c")

# need to redefine because the tests below don't use any mocks
set(utest_link_list "")
list(APPEND utest_link_list
                lib${real_name}.a
        )

create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

# Create another custom mock list

# list the files to mock here
list(APPEND cellular_common_mock_list
            "${CELLULAR_COMMON_INCLUDE_PRIVATE_DIRS}/cellular_pktio_internal.h"
            "${CELLULAR_COMMON_INCLUDE_PRIVATE_DIRS}/cellular_pkthandler_internal.h"
            "${CELLULAR_COMMON_INCLUDE_DIRS}/cellular_at_core.h"
        )

# list the files you would like to test here
list(APPEND cellular_common_real_source_files
            ${CELLULAR_COMMON_SOURCE_DIRS}/cellular_common.c
            ${CELLULAR_COMMON_SOURCE_DIRS}/cellular_3gpp_urc_handler.c
            ${CELLULAR_COMMON_SOURCE_DIRS}/cellular_3gpp_api.c
        )

set(cellular_common_mock_name "${project_name}_common_mock")
set(cellular_common_real_name "${project_name}_common_real")

create_mock_list(${cellular_common_mock_name}
                "${cellular_common_mock_list}"
                "${MODULE_ROOT_DIR}/tools/cmock/project.yml"
                "${mock_include_list}"
                "${mock_define_list}"
        )

create_real_library(${cellular_common_real_name}
                    "${cellular_common_real_source_files}"
                    "${real_include_directories}"
                    "${cellular_common_mock_name}"
        )

set(utest_link_list "")
list(APPEND utest_link_list
            -l${cellular_common_mock_name}
            lib${cellular_common_real_name}.a
        )

set(utest_dep_list "")
list(APPEND utest_dep_list
            ${cellular_common_real_name}
        )

set(utest_name "${project_name}_common_utest")
set(utest_source "${project_name}_common_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )
