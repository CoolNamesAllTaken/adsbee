add_subdirectory(app)
add_subdirectory(hal)

if(CROSS_COMPILED)
# Build for testing on host.
target_include_directories(ads_bee_test PRIVATE
    app
    hal
)
else()
# Build for embedded target
target_include_directories(ads_bee PRIVATE
    app
    hal
)
endif()