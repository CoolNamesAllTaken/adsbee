if(FREERTOS_PLUS_TCP_ENABLE_BUILD_CHECKS)
  add_subdirectory(build-combination)
endif()

if(FREERTOS_PLUS_TCP_BUILD_TEST)
  add_subdirectory(Coverity)
  add_subdirectory(unit-test)
endif()

