include( ${MODULE_ROOT_DIR}/jsonFilePaths.cmake )

# ====================  Define your project name (edit) ========================
set(project_name "core_json")

# =====================  Create your mock here  (edit)  ========================
# ================= Create the library under test here (edit) ==================

# Base name for temporary files
set( TEMP_BASE ${CMAKE_BINARY_DIR}/${project_name} )

# Strip static constraints so unit tests may call internal functions
execute_process( COMMAND sed "s/^static //"
                 WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                 INPUT_FILE ${JSON_SOURCES}
                 OUTPUT_FILE ${TEMP_BASE}.c
        )

# Generate a header file for internal functions
execute_process( COMMAND sed -n "/^static.*(/,/^{\$/{s/^static //; s/)\$/&;/; /{/d; p;}"
                 WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
                 INPUT_FILE ${JSON_SOURCES}
                 OUTPUT_FILE ${TEMP_BASE}_annex.h
        )

# list the files you would like to test here
list(APPEND real_source_files
            ${TEMP_BASE}.c
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            ${JSON_INCLUDE_PUBLIC_DIRS}
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            ${JSON_INCLUDE_PUBLIC_DIRS}
            ${UNIT_TEST_DIR}
            ${CMAKE_BINARY_DIR}
        )

# =============================  (end edit)  ===================================

set(real_name "${project_name}_real")

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
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
