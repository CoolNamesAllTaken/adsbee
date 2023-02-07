add_subdirectory(app)

if(CROSS_COMPILED)
# Build for testing on host.
target_include_directories(ads_bee_test PRIVATE
    app
)
else()
# Build for embedded target
target_include_directories(ads_bee PRIVATE
    app
)
endif()