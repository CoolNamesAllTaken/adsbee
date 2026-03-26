if(NOT ON_EMBEDDED_DEVICE)
    # Build for testing on host.
    target_sources(host_test PRIVATE
        # comms.cc
    )
    target_include_directories(host_test PRIVATE
        beast
    )
else()
    # Build for embedded target
    target_sources(application PRIVATE
        at/comms_at.cc
        comms.cc
    )
    target_include_directories(application PRIVATE
        at
        .
    )
endif()