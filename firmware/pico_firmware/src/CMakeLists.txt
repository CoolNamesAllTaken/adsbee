add_subdirectory(app)
add_subdirectory(common)
add_subdirectory(comms)
add_subdirectory(hal)
add_subdirectory(test)
if(CROSS_COMPILED)
# Build for testing on host.
target_include_directories(ads_bee_test PRIVATE
    app
    common
    hal
    # Don't share comms headers with unit tests.
)
else()
# Build for embedded target
target_include_directories(ads_bee PRIVATE
    app
    common
    comms
    hal
    test
)
target_sources(ads_bee
PRIVATE
    main.cc # Don't include main for testing.
)
endif()