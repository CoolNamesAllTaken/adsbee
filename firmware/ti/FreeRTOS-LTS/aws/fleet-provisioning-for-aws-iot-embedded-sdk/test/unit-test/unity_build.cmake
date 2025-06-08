# Macro to clone the Unity submodule.
macro( clone_unity )
    find_package( Git REQUIRED )
    message( "Cloning Unity submodule." )
    execute_process( COMMAND rm -rf ${UNITY_DIR}
                     COMMAND ${GIT_EXECUTABLE} submodule update --checkout --init --recursive ${UNITY_DIR}
                     WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
                     RESULT_VARIABLE UNITY_CLONE_RESULT )

    if( NOT ${UNITY_CLONE_RESULT} STREQUAL "0" )
        message( FATAL_ERROR "Failed to clone Unity submodule." )
    endif()
endmacro()

# Macro to add library target for Unity to build configuration.
macro( add_unity_target )
    add_library( unity STATIC
                 "${UNITY_DIR}/src/unity.c"
                 "${UNITY_DIR}/extras/fixture/src/unity_fixture.c"
                 "${UNITY_DIR}/extras/memory/src/unity_memory.c" )

    target_include_directories( unity PUBLIC
                                "${UNITY_DIR}/src/"
                                "${UNITY_DIR}/extras/fixture/src"
                                "${UNITY_DIR}/extras/memory/src" )

    set_target_properties( unity PROPERTIES
                           ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib
                           POSITION_INDEPENDENT_CODE ON )

    target_link_libraries( unity )
endmacro()
