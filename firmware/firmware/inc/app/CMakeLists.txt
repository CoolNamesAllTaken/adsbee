# if(CROSS_COMPILED)
# # Build for testing on host.
# target_sources(ads_bee_test PRIVATE
#     buffer_utils.hh
#     aircraft_dictionary.hh
#     ads_b_packet.hh
#     # ads_bee.hh # left out since it requires a lot of mocking
#     decode_utils.hh
# )
# else()
# # Build for embedded target
# target_sources(ads_bee PRIVATE
#     buffer_utils.hh
#     aircraft_dictionary.hh
#     ads_b_packet.hh
#     ads_bee.hh
#     decode_utils.hh
# )
# endif()