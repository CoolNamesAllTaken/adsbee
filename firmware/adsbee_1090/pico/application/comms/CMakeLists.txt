if(NOT ON_EMBEDDED_DEVICE)
    # Build for testing on host.
    foreach(_test_tgt IN ITEMS host_test host_test_fpu)
        if (TARGET ${_test_tgt})
            target_sources(${_test_tgt} PRIVATE
                # comms.cc
            )
            target_include_directories(${_test_tgt} PRIVATE
                beast
            )
        endif()
    endforeach()
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