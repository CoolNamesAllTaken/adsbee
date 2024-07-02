if (COMPILED_FOR_TARGET)
    file(GLOB SRC_FILES "*.c")
    target_sources(${PROJECT_NAME} PRIVATE
        ${SRC_FILES}
    )
endif()
# Don't deal with any of this for unit testing on the host.