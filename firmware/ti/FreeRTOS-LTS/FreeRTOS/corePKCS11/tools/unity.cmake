include(FetchContent)

FetchContent_Declare(
    unity GIT_REPOSITORY https://github.com/ThrowTheSwitch/unity.git GIT_TAG v2.6.0
)

FetchContent_GetProperties(
    unity
    POPULATED unity_POPULATED
)
if(NOT ${unity_POPULATED})
    FetchContent_Populate(unity)
endif()

if(NOT TARGET unity)
    add_library(unity STATIC)

    target_sources(
        unity
        PRIVATE ${unity_SOURCE_DIR}/src/unity.c
        PRIVATE ${unity_SOURCE_DIR}/extras/fixture/src/unity_fixture.c
        PRIVATE ${unity_SOURCE_DIR}/extras/memory/src/unity_memory.c
    )

    target_include_directories(
        unity
        PRIVATE ${unity_SOURCE_DIR}/src
        PRIVATE ${unity_SOURCE_DIR}/extras/memory/src
        PRIVATE ${unity_SOURCE_DIR}/extras/fixture/src
    )

    target_include_directories(
        unity
        PUBLIC ${unity_SOURCE_DIR}/src
        PUBLIC ${unity_SOURCE_DIR}/extras/memory/src
        PUBLIC ${unity_SOURCE_DIR}/extras/fixture/src
    )
endif()

macro(add_test_target target test_src)
    add_executable(${target} ${test_src})

    set_target_properties(
        ${target} PROPERTIES COMPILE_FLAG "-O0 -ggdb" RUNTIME_OUTPUT_DIRECTORY
                                                      "${CMAKE_BINARY_DIR}/bin"
    )

    include(CTest)
    add_test(NAME ${target} COMMAND "${CMAKE_BINARY_DIR}/bin/${target}"
             WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    )
endmacro()

macro(target_enable_gcov target flag)
    get_target_property(target_type ${target} TYPE)

    if(target_type STREQUAL "INTERFACE_LIBRARY")
        set(c_flag INTERFACE)
        set(l_flag INTERFACE)
    else()
        set(c_flag PRIVATE)
        set(l_flag PUBLIC)
    endif()

    target_compile_options(
        ${target}
        ${c_flag}
        "-Wextra"
        ${c_flag}
        "-Wpedantic"
        ${c_flag}
        "-fprofile-arcs"
        ${c_flag}
        "-ftest-coverage"
        ${c_flag}
        "-fprofile-generate"
    )

    if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
        target_link_options(${target} ${l_flag} "-fprofile-instr-generate")
        target_compile_options(${target} ${c_flag} "-Wno-unused-private-field")
    elseif(CMAKE_CXX_COMPILER_ID MATCHES "GNU")
        target_link_libraries(${target} ${l_flag} -lgcov)
        target_compile_options(${target} ${c_flag} "-Wno-unused-but-set-variable")
    endif()
endmacro()

macro(target_add_test_runner target unity_config test_src)
    get_filename_component(test_name ${test_src} NAME_WE)
    get_target_property(target_type ${target} TYPE)

    if(target_type STREQUAL "INTERFACE_LIBRARY")
        set(s_flag INTERFACE)
    else()
        set(s_flag PRIVATE)
    endif()

    add_custom_command(
        OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${test_name}_runner.c
        DEPENDS ${test_src} ${unity_config}
        COMMAND
            ruby ${unity_SOURCE_DIR}/auto/generate_test_runner.rb ${unity_config} ${test_src}
            ${CMAKE_CURRENT_BINARY_DIR}/${test_name}_runner.c
        WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
    )
    target_sources(${target} ${s_flag} ${CMAKE_CURRENT_BINARY_DIR}/${test_name}_runner.c)

    target_link_libraries(${target} ${s_flag} unity)
endmacro()
