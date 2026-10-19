# The ESP32 build picks this directory up through SRC_DIRS in adsbee_1090/esp/main/CMakeLists.txt.
if (TARGET host_test OR TARGET host_test_fpu)
    foreach(_test_tgt IN ITEMS host_test host_test_fpu)
        if (TARGET ${_test_tgt})
            target_sources(${_test_tgt} PRIVATE
                swarm_reporter.cpp
            )
            target_include_directories(${_test_tgt} PRIVATE
                .
            )
        endif()
    endforeach()
endif()
