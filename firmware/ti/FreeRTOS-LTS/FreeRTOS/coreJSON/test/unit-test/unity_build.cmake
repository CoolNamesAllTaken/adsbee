# Macro utility to clone the Unity submodule.
macro( clone_unity )
        find_package( Git REQUIRED )
        message( "Cloning submodule Unity." )
        execute_process( COMMAND rm -rf ${UNITY_DIR}
                         COMMAND ${GIT_EXECUTABLE} submodule update --checkout --init --recursive ${UNITY_DIR}
                        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
                        RESULT_VARIABLE UNITY_CLONE_RESULT )

        if( NOT ${UNITY_CLONE_RESULT} STREQUAL "0" )
                message( FATAL_ERROR "Failed to clone Unity submodule." )
        endif()
endmacro()

# Macro utility to add library targets for Unity and Unity to build configuration.
macro( add_unity_targets )
        # Build Configuration for Unity and Unity libraries.
        list( APPEND UNITY_INCLUDE_DIRS
                "${UNITY_DIR}/src/"
                "${UNITY_DIR}/extras/fixture/src"
                "${UNITY_DIR}/extras/memory/src"
        )

        add_library( unity STATIC
                "${UNITY_DIR}/src/unity.c"
                "${UNITY_DIR}/extras/fixture/src/unity_fixture.c"
                "${UNITY_DIR}/extras/memory/src/unity_memory.c"
        )

        set_target_properties( unity PROPERTIES
                ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib
                POSITION_INDEPENDENT_CODE ON
        )

        target_include_directories( unity PUBLIC
                ${UNITY_INCLUDE_DIRS}
        )
endmacro()
