macro( clone_llhttp )
        find_package( Git REQUIRED )
        message( "Cloning submodule llhttp." )
        execute_process( COMMAND ${GIT_EXECUTABLE} submodule update --init --recursive ${LLHTTP_DIR}
                        WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}
                        RESULT_VARIABLE LLHTTP_CLONE_RESULT )

        if( NOT ${LLHTTP_CLONE_RESULT} STREQUAL "0" )
            message( FATAL_ERROR "Failed to clone llhttp submodule." )
        endif()
endmacro()

# llhttp library target.
add_library( llhttp
             ${LLHTTP_DIR}/src/api.c
             ${LLHTTP_DIR}/src/http.c
             ${LLHTTP_DIR}/src/llhttp.c )

# llhttp public include path.
target_include_directories( llhttp PUBLIC
                            ${LLHTTP_DIR}/include )
