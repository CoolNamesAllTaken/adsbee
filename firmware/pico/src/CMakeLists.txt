add_subdirectory(app)
add_subdirectory(comms)
add_subdirectory(esp32_flasher)
add_subdirectory(target_test)
if(NOT COMPILED_FOR_TARGET)
    # Build for testing on host.
    target_include_directories(${PROJECT_NAME} PRIVATE
        app
        # Don't share comms headers with unit tests.
        comms/beast
    )
else()
    # Build for embedded target
    target_include_directories(${PROJECT_NAME} PRIVATE
        app
        comms
        target_test
    )
    target_sources(${PROJECT_NAME} PRIVATE
        main.cc # Don't include main for testing.
    )
endif()