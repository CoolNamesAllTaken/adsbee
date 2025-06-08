# Taken from amazon-freertos repository

#function to create the test executable
function(create_test test_name
                     test_src
                     link_list
                     dep_list
                     include_list)
    include (CTest)
    get_filename_component(test_src_absolute ${test_src} ABSOLUTE)
    add_custom_command(OUTPUT ${test_name}_runner.c
                  COMMAND ruby
                    ${UNITY_DIR}/auto/generate_test_runner.rb
                    ${MODULE_ROOT_DIR}/tools/unity/project.yml
                    ${test_src_absolute}
                    ${test_name}_runner.c
                  DEPENDS ${test_src}
        )
    add_executable(${test_name} ${test_src} ${test_name}_runner.c)
    set_target_properties(${test_name} PROPERTIES
            COMPILE_FLAG "-O0 -ggdb"
            RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}/bin/tests"
            INSTALL_RPATH_USE_LINK_PATH TRUE
            LINK_FLAGS " \
                -Wl,-rpath,${CMAKE_BINARY_DIR}/lib \
                -Wl,-rpath,${CMAKE_CURRENT_BINARY_DIR}/lib"
        )
    target_include_directories(${test_name} PUBLIC
                               ${include_list}
        )

    target_link_directories(${test_name} PUBLIC
                            ${CMAKE_CURRENT_BINARY_DIR}
        )

    # link all libraries sent through parameters
    foreach(link IN LISTS link_list)
        target_link_libraries(${test_name} ${link})
    endforeach()

    # add dependency to all the dep_list parameter
    foreach(dependency IN LISTS dep_list)
        add_dependencies(${test_name} ${dependency})
        target_link_libraries(${test_name} ${dependency})
    endforeach()
    target_link_libraries(${test_name} -lgcov unity)
    target_link_directories(${test_name}  PUBLIC
                            ${CMAKE_CURRENT_BINARY_DIR}/lib
            )
    add_test(NAME ${test_name}
             COMMAND ${CMAKE_BINARY_DIR}/bin/tests/${test_name}
             WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
            )
endfunction()

function(create_real_library target
                             src_file
                             real_include_list)
    add_library(${target} STATIC
            ${src_file}
        )
    target_include_directories(${target} PUBLIC
            ${real_include_list}
        )
    set_target_properties(${target} PROPERTIES
            COMPILE_FLAGS "-Wextra -Wpedantic \
                -fprofile-arcs -ftest-coverage -fprofile-generate \
                -Wno-unused-but-set-variable"
            LINK_FLAGS "-fprofile-arcs -ftest-coverage \
                -fprofile-generate "
            ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib
        )
endfunction()
