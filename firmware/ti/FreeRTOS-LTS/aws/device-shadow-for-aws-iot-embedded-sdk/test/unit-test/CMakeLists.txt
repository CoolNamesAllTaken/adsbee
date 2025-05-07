# Include filepaths for source and include.
include( ${MODULE_ROOT_DIR}/shadowFilePaths.cmake )

# ====================  Define your project name (edit) ========================
set(project_name "shadow")

# =====================  Create your mock here  (edit)  ========================
# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            ${SHADOW_SOURCES}
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            .
            ${SHADOW_INCLUDE_PUBLIC_DIRS}
            "${CMAKE_CURRENT_LIST_DIR}/../include"
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            .
            ${SHADOW_INCLUDE_PUBLIC_DIRS}
        )

# =============================  (end edit)  ===================================

set(real_name "${project_name}_real")

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

list(APPEND utest_link_list
            lib${real_name}.a
        )

list(APPEND utest_dep_list
            ${real_name}
        )

set(utest_name "${project_name}_utest")
set(utest_source "${project_name}_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )
