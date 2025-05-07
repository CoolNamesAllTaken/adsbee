include(FetchContent)

# Ensure unity target has been added.
if(NOT TARGET unity)
    include(${MODULE_ROOT_DIR}/tools/unity.cmake)
endif()

FetchContent_Declare(
    cmock GIT_REPOSITORY https://github.com/ThrowTheSwitch/CMock.git
    GIT_TAG v2.5.3
)

FetchContent_GetProperties(
    cmock
    POPULATED cmock_POPULATED
)

if(NOT ${cmock_POPULATED})
    FetchContent_Populate(cmock)
endif()

if(NOT TARGET cmock)
    add_library(cmock STATIC)
    target_sources(cmock PRIVATE ${cmock_SOURCE_DIR}/src/cmock.c)

    set_target_properties(cmock PROPERTIES COMPILE_FLAGS "-Og")
    target_include_directories(cmock PRIVATE ${cmock_SOURCE_DIR}/src)
    target_include_directories(cmock PUBLIC ${cmock_SOURCE_DIR}/src)
    target_link_libraries(cmock PRIVATE unity)
endif()

macro(
    target_add_mock_pp
    mock_target
    cmock_config
    mock_header
    pp_args
)
    get_filename_component(mock_basename ${mock_header} NAME_WE)
    get_filename_component(cmock_config_absolute ${cmock_config} ABSOLUTE)
    get_filename_component(mock_header_absolute ${mock_header} ABSOLUTE)

    get_target_property(target_defs ${mock_target} COMPILE_DEFINITIONS)

    set(target_flags "")
    if(NOT "${target_defs}" STREQUAL "target_defs-NOTFOUND")
        foreach(target_def ${target_defs})
            set(target_flags ${target_flags} ${target_def})
        endforeach()
    endif()

    get_target_property(target_include_dirs ${mock_target} INCLUDE_DIRECTORIES)

    if(NOT "${target_include_dirs}" STREQUAL "target_include_dirs-NOTFOUND")
        foreach(include_dir ${target_include_dirs})
            set(target_flags ${target_flags} -I${include_dir})
        endforeach()
    endif()

    add_custom_target(
        mocks_pp_dir ALL
        COMMAND ${CMAKE_COMMAND} -E make_directory ${CMAKE_CURRENT_BINARY_DIR}/mocks_pp
    )

    # Preprocess header file before generating mock
    add_custom_command(
        OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/mocks_pp/${mock_basename}.h
        VERBATIM
        COMMAND
            ${CMAKE_C_COMPILER} -E ${pp_args} ${target_flags} -nostdlib -nodefaultlibs
            ${mock_header_absolute} -o ${CMAKE_CURRENT_BINARY_DIR}/mocks_pp/${mock_basename}.h
        DEPENDS mocks_pp_dir pkcs11_api
    )

    # Generate mock
    add_custom_command(
        OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/mock_${mock_basename}.c
        COMMAND
            ruby ${cmock_SOURCE_DIR}/lib/cmock.rb -o${cmock_config_absolute}
            ${CMAKE_CURRENT_BINARY_DIR}/mocks_pp/${mock_basename}.h
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
        DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/mocks_pp/${mock_basename}.h
    )

    target_sources(${mock_target} PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/mock_${mock_basename}.c)

    target_include_directories(${mock_target} PRIVATE ${CMAKE_CURRENT_BINARY_DIR})
endmacro()

macro(target_add_mock mock_target cmock_config mock_header)
    get_filename_component(mock_basename ${mock_header} NAME_WE)
    get_filename_component(cmock_config_absolute ${cmock_config} ABSOLUTE)
    get_filename_component(mock_header_absolute ${mock_header} ABSOLUTE)

    get_target_property(target_defs ${mock_target} COMPILE_DEFINITIONS)

    set(target_flags "")
    if(NOT "${target_defs}" STREQUAL "target_defs-NOTFOUND")
        foreach(target_def ${target_defs})
            set(target_flags ${target_flags} -D${target_def})
        endforeach()
    endif()

    # Generate mock
    add_custom_command(
        OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/mock_${mock_basename}.c
        COMMAND
            ruby ${cmock_SOURCE_DIR}/lib/cmock.rb -o${cmock_config_absolute}
            ${mock_header_absolute}
        WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    )

    target_sources(${mock_target} PRIVATE ${CMAKE_CURRENT_BINARY_DIR}/mock_${mock_basename}.c)

    target_include_directories(${mock_target} PRIVATE ${CMAKE_CURRENT_BINARY_DIR})
endmacro()
