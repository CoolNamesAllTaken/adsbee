# Build Instructions

This test aims at finding only compilation issues and as a result, the
generated binary is not runnable.

## UNIX (Linux and Mac)

All the CMake commands are to be run from the root of the repository.

* Build checks (Enable all functionalities)
```
cmake -S . -B build -DFREERTOS_PLUS_TCP_ENABLE_BUILD_CHECKS=ON -DFREERTOS_PLUS_TCP_TEST_CONFIGURATION=ENABLE_ALL
cmake --build build --target freertos_plus_tcp_build_test
```

* Build checks (Disable all functionalities)
```
cmake -S . -B build -DFREERTOS_PLUS_TCP_ENABLE_BUILD_CHECKS=ON -DFREERTOS_PLUS_TCP_TEST_CONFIGURATION=DISABLE_ALL
cmake --build build --target freertos_plus_tcp_build_test
```

* Build checks (Default configuration)
```
cmake -S . -B build -DFREERTOS_PLUS_TCP_ENABLE_BUILD_CHECKS=ON -DFREERTOS_PLUS_TCP_TEST_CONFIGURATION=DEFAULT_CONF
cmake --build build --target freertos_plus_tcp_build_test
```

## Windows

All the CMake commands are to be run from the root of the repository.

* Build checks (Enable all functionalities)
```
cmake -S . -B build -DFREERTOS_PLUS_TCP_ENABLE_BUILD_CHECKS=ON -DFREERTOS_PLUS_TCP_TEST_CONFIGURATION=ENABLE_ALL -DCMAKE_GENERATOR_PLATFORM=Win32
```
Open the generated Visual Studio Solution file `test\build-combination\build\FreeRTOS-Plus-TCP Build Combination.sln`
in Visual Studio and click `Build --> Build Solution`.

* Build checks (Disable all functionalities)
```
cmake -S . -B build -DFREERTOS_PLUS_TCP_ENABLE_BUILD_CHECKS=ON -DFREERTOS_PLUS_TCP_TEST_CONFIGURATION=ENABLE_ALL -DCMAKE_GENERATOR_PLATFORM=Win32
```
Open the generated Visual Studio Solution file `test\build-combination\build\FreeRTOS-Plus-TCP Build Combination.sln`
in Visual Studio and click `Build --> Build Solution`.

* Build checks (Default configuration)
```
cmake -S . -B build -DFREERTOS_PLUS_TCP_ENABLE_BUILD_CHECKS=ON -DFREERTOS_PLUS_TCP_TEST_CONFIGURATION=ENABLE_ALL -DCMAKE_GENERATOR_PLATFORM=Win32
```
Open the generated Visual Studio Solution file `test\build-combination\build\FreeRTOS-Plus-TCP Build Combination.sln`
in Visual Studio and click `Build --> Build Solution`.
