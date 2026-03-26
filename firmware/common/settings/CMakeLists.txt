
if (TARGET application)
    target_sources(application PRIVATE
        settings_strs.cpp
        settings.cpp
    )
    target_include_directories(application PRIVATE
        .
    )
elseif (TARGET sub_ghz_radio)
    target_sources(sub_ghz_radio PRIVATE
        settings_strs.cpp
        settings.cpp
    )
    target_include_directories(sub_ghz_radio PRIVATE
        .
    )
elseif (TARGET host_test)
    target_sources(host_test PRIVATE
        settings_strs.cpp
        settings.cpp
    )
    target_include_directories(host_test PRIVATE
        .
    )
endif()
