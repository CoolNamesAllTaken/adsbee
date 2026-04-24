
if (TARGET application)
    target_sources(application PRIVATE
        composite_array.cpp
        spi_coprocessor.cpp
        object_dictionary.cpp
    )
    target_include_directories(application PRIVATE
        .
    )
elseif (TARGET sub_ghz_radio)
    target_sources(sub_ghz_radio PRIVATE
        composite_array.cpp
        spi_coprocessor.cpp
        object_dictionary.cpp
    )
    target_include_directories(sub_ghz_radio PRIVATE
        .
    )
elseif (TARGET host_test OR TARGET host_test_fpu)
    foreach(_test_tgt IN ITEMS host_test host_test_fpu)
        if (TARGET ${_test_tgt})
            target_sources(${_test_tgt} PRIVATE
                composite_array.cpp
                spi_coprocessor.cpp
                object_dictionary.cpp
            )
            target_include_directories(${_test_tgt} PRIVATE
                .
            )
        endif()
    endforeach()
endif()
