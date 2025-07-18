target_sources(sub_ghz_radio PRIVATE
    smartrf/smartrf_settings.c
    sub_ghz_radio.cpp

    RFQueue.cpp
)
target_include_directories(sub_ghz_radio PRIVATE
    .
)
