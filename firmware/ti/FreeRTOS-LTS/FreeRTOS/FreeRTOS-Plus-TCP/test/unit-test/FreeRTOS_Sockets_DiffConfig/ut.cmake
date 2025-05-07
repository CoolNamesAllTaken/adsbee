# Include filepaths for source and include.
include( ${MODULE_ROOT_DIR}/test/unit-test/TCPFilePaths.cmake )

# ====================  Define your project name (edit) ========================
set( project_name "FreeRTOS_Sockets_DiffConfig" )
message( STATUS "${project_name}" )

# =====================  Create your mock here  (edit)  ========================
set(mock_list "")

# list the files to mock here
list(APPEND mock_list
            "${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include/task.h"
            "${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include/list.h"
            "${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include/queue.h"
            "${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include/event_groups.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/portable.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_IP.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_IPv4_Sockets.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_IPv6_Sockets.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_Routing.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_Stream_Buffer.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/FreeRTOS_TCP_WIN.h"
            "${CMAKE_BINARY_DIR}/Annexed_TCP/NetworkBufferManagement.h"
            "${MODULE_ROOT_DIR}/test/unit-test/${project_name}/Sockets_DiffConfig_list_macros.h"
        )

set(mock_include_list "")
# list the directories your mocks need
list(APPEND mock_include_list
            ${MODULE_ROOT_DIR}/test/unit-test/${project_name}
            .
            ${TCP_INCLUDE_DIRS}
            ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include
            ${MODULE_ROOT_DIR}/test/unit-test/ConfigFiles
            ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/portable/ThirdParty/GCC/Posix
        )

set(mock_define_list "")
#list the definitions of your mocks to control what to be included
list(APPEND mock_define_list
            ""
       )

# ================= Create the library under test here (edit) ==================

set(real_source_files "")

# list the files you would like to test here
list(APPEND real_source_files
            ${CMAKE_BINARY_DIR}/Annexed_TCP_Sources/FreeRTOS_Sockets.c
            ${MODULE_ROOT_DIR}/test/unit-test/${project_name}/${project_name}_stubs.c
	)

set(real_include_directories "")
# list the directories the module under test includes
list(APPEND real_include_directories
            ${MODULE_ROOT_DIR}/test/unit-test/${project_name}
            .
            ${TCP_INCLUDE_DIRS}
            ${MODULE_ROOT_DIR}/test/unit-test/ConfigFiles
            ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/include
            ${MODULE_ROOT_DIR}/test/FreeRTOS-Kernel/portable/ThirdParty/GCC/Posix
            ${CMOCK_DIR}/vendor/unity/src
            ${MODULE_ROOT_DIR}/test/unit-test/FreeRTOS_Sockets
	)

# =====================  Create UnitTest Code here (edit)  =====================
set(test_include_directories "")
# list the directories your test needs to include
list(APPEND test_include_directories
            ${MODULE_ROOT_DIR}/test/unit-test/${project_name}
            .
            ${CMOCK_DIR}/vendor/unity/src
            ${TCP_INCLUDE_DIRS}
        )

# =============================  (end edit)  ===================================

set(mock_name "${project_name}_mock")
set(real_name "${project_name}_real")

create_mock_list(${mock_name}
                "${mock_list}"
                "${MODULE_ROOT_DIR}/test/unit-test/cmock/project.yml"
                "${mock_include_list}"
                "${mock_define_list}"
        )

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

set( utest_link_list "" )
list(APPEND utest_link_list
            -l${mock_name}
            lib${real_name}.a
        )

list(APPEND utest_dep_list
            ${real_name}
        )

set(utest_name "${project_name}_privates_utest")
set(utest_source "${project_name}/${project_name}_privates_utest.c" )

create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )
