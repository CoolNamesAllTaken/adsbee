target_sources(${PROJECT_NAME} PRIVATE
    hal.cc
    main.cc
    # test_ads_b_decoder.cc
    test_ads_b_packet.cc
    test_aircraft_dictionary.cc
    # test_ads_bee.cc
    test_data_structures.cc
    test_platform.cc
    test_spi_coprocessor.cc
    test_unit_conversions.cc
    test_reporting_beast.cc
    test_reporting_csbee.cc
    test_decode_utils.cc
    test_mode_a_c_packets.cc
)

target_include_directories(${PROJECT_NAME} PRIVATE
    mocks
)