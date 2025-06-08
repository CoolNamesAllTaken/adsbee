set( headerList
     FreeRTOS_DHCP
     FreeRTOS_DNS
     FreeRTOS_IP
     FreeRTOS_ND
     FreeRTOS_Routing
     FreeRTOS_Sockets
     NetworkBufferManagement
     NetworkInterface )

foreach( header IN LISTS headerList )
    add_executable(freertos_plus_tcp_build_test_${header} EXCLUDE_FROM_ALL)

    target_sources(freertos_plus_tcp_build_test_${header}
      PRIVATE
        Common/main.c
    )

    # In header self contain test, we include headers one by one (by "-include ${header}.h")
    # to make sure all header files are able to include separately.
    target_compile_options(freertos_plus_tcp_build_test_${header}
      PRIVATE
        -include ${header}.h
        $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-cast-qual>
        $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-format-nonliteral>
        $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-implicit-function-declaration>
        $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-noreturn>
        $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-prototypes>
        $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-missing-variable-declarations>
        $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-reserved-identifier>
        $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-shorten-64-to-32>
        $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-sign-conversion>
        $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-unused-parameter>
        $<$<COMPILE_LANG_AND_ID:C,Clang>:-Wno-unused-macros>
        $<$<COMPILE_LANG_AND_ID:C,Clang,GNU>:-Wno-unused-variable>
    )

    target_link_libraries(freertos_plus_tcp_build_test_${header}
        PRIVATE
        freertos_plus_tcp
        freertos_kernel
    )
endforeach()
