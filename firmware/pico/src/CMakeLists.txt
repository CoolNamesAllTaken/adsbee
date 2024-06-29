add_subdirectory(app)
add_subdirectory(../../common adsbee_common) # Explicityly specify binary directory for out of tree subdirectory.
add_subdirectory(comms)
add_subdirectory(hal)
add_subdirectory(test)
if(CROSS_COMPILED)
# Build for testing on host.
target_include_directories(${PROJECT_NAME} PRIVATE
    app
    ../../common
    hal
    # Don't share comms headers with unit tests.
)
else()
# Build for embedded target
target_include_directories(${PROJECT_NAME} PRIVATE
    app
    ../../common
    comms
    hal
    test
)
target_sources(${PROJECT_NAME} PRIVATE
    main.cc # Don't include main for testing.
)
endif()