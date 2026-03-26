
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
elseif (TARGET host_test)
    target_sources(host_test PRIVATE
        composite_array.cpp
        spi_coprocessor.cpp
        object_dictionary.cpp
    )
    target_include_directories(host_test PRIVATE
        .
    )
endif()
