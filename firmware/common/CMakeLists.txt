
add_subdirectory(adsb)
add_subdirectory(comms)
add_subdirectory(coprocessor)
add_subdirectory(firmware_update)
add_subdirectory(settings)
add_subdirectory(utils)

if (TARGET application)
    # NOTE: Annoyingly, all source files need to end with .c or .cpp to be seen by the ESP IDF.
    target_include_directories(application PRIVATE .)
elseif (TARGET sub_ghz_radio)
    target_include_directories(sub_ghz_radio PRIVATE .)
endif()