# Change Log for corePKCS11 Library

## v3.6.1 (June 2024)
* Fix doxygen deployment on Github.

## v3.6.0 (May 2024)
* [#195](https://github.com/FreeRTOS/corePKCS11/pull/195),[#196](https://github.com/FreeRTOS/corePKCS11/pull/196) Add more unit test to increase code coverage rate
* [#193](https://github.com/FreeRTOS/corePKCS11/pull/193) Fix the C_GetAttributeValue implementation in the mbedtls port to return CK_UNAVAILABLE_INFORMATION
* [#192](https://github.com/FreeRTOS/corePKCS11/pull/192) Use MBedTLS v3.6.0 LTS and v2.28.8 in mbedtls integration test
* [#190](https://github.com/FreeRTOS/corePKCS11/pull/190) Fix MISRA C 2012 deviations
* [#184](https://github.com/FreeRTOS/corePKCS11/pull/184) Support MBedTLS 3.5.1
* [#183](https://github.com/FreeRTOS/corePKCS11/pull/183) Support optional write generated private key and certificate to disk for fleet provisioning
* [#182](https://github.com/FreeRTOS/corePKCS11/pull/182) Fix incorrect RSA verify data length check
* [#178](https://github.com/FreeRTOS/corePKCS11/pull/178) Adjust prvAddObjectToList so that it adds or updates as necessary
* [#163](https://github.com/FreeRTOS/corePKCS11/pull/163) Update doxygen to 1.9.6

## v3.5.0 (October 2022)
* [#156](https://github.com/FreeRTOS/corePKCS11/pull/156) MISRA C:2012 compliance updates
* [#155](https://github.com/FreeRTOS/corePKCS11/pull/155) Update CBMC Starter kit
* [#150](https://github.com/FreeRTOS/corePKCS11/pull/150) Update CorePKCS11 mbedtls implementation to support mbedtls version 3.x in addition to version 2.x

## v3.4.0 (December 2021)
* [#144](https://github.com/FreeRTOS/corePKCS11/pull/144) Update mbedtls submodule to [v2.28.0](https://github.com/ARMmbed/mbedtls/tree/v2.28.0)

## v3.3.0 (November 2021)
* [#137](https://github.com/FreeRTOS/corePKCS11/pull/137) Fix code in winsim PAL missed in prior refactor.
* [#133](https://github.com/FreeRTOS/corePKCS11/pull/133) Update doxygen version for documentation.

## v3.2.0 (August 2021)
* [#129](https://github.com/FreeRTOS/corePKCS11/pull/129) Enable address sanitizer for tests in PR Checks.
* [#128](https://github.com/FreeRTOS/corePKCS11/pull/128) Fix invalid memory read in system tests.
* [#126](https://github.com/FreeRTOS/corePKCS11/pull/126) Add default values for Claim credentials label configuration macros.
* [#125](https://github.com/FreeRTOS/corePKCS11/pull/125) Fix memory leaks in corePKCS11.
* [#123](https://github.com/FreeRTOS/corePKCS11/pull/123) Changes PAL folder structure and adds core+pkcs11\_pal\_utils for shared code between PALs.
* [#124](https://github.com/FreeRTOS/corePKCS11/pull/124) Add backwards compatibility for deprecated configuration macros.
* [#121](https://github.com/FreeRTOS/corePKCS11/pull/121) Add labels for supporting Claim credentials useful for Fleet Provisioning feature of AWS IoT Core.
* [#122](https://github.com/FreeRTOS/corePKCS11/pull/122) Add `core_pkcs11_config_defaults.h` file for default definition of configuration macros. and make doxygen documentation fixes.

## v3.1.0 (July 2021)
* [#119](https://github.com/FreeRTOS/corePKCS11/pull/119) Update mbedTLS submodule to [v2.26.0](https://github.com/ARMmbed/mbedtls/tree/v2.26.0).
* [#118](https://github.com/FreeRTOS/corePKCS11/pull/118) Update version numbers and add C++ header guards
* [#116](https://github.com/FreeRTOS/corePKCS11/pull/116) Remove redundant mbedtls error sources
* [#115](https://github.com/FreeRTOS/corePKCS11/pull/115) Update broken links to MISRA in documentation
* [#113](https://github.com/FreeRTOS/corePKCS11/pull/113) Fix description of CBMC in README
* [#112](https://github.com/FreeRTOS/corePKCS11/pull/112) Add additional validation of the return value of mbedtls\_pk\_write\_\*\_der functions
* [#111](https://github.com/FreeRTOS/corePKCS11/pull/111) Add AES-CMAC algorithm support in Windows port
* [#110](https://github.com/FreeRTOS/corePKCS11/pull/110) Hygiene fixes in CI checks
* [#104](https://github.com/FreeRTOS/corePKCS11/pull/104) Minor MISRA fixes
* [#103](https://github.com/FreeRTOS/corePKCS11/pull/103) Fix doxygen main page generation
* [#102](https://github.com/FreeRTOS/corePKCS11/pull/102) Feature: AES CMAC Sign/SignInit
* [#101](https://github.com/FreeRTOS/corePKCS11/pull/101) Feature: AES CMAC - VerifyInit/Verify
* [#98](https://github.com/FreeRTOS/corePKCS11/pull/98) Fix MISRA regressions
* [#97](https://github.com/FreeRTOS/corePKCS11/pull/97) Implement C\_CreateObject for AES CMAC keys
* [#96](https://github.com/FreeRTOS/corePKCS11/pull/96) Feature: SHA256-HMAC sign
* [#95](https://github.com/FreeRTOS/corePKCS11/pull/95) Feature: SHA256-HMAC C\_SignInit
* [#94](https://github.com/FreeRTOS/corePKCS11/pull/94) Fix system test output suppresion
* [#91](https://github.com/FreeRTOS/corePKCS11/pull/91) Fix potential double free in core\_pkcs11.c
* [#86](https://github.com/FreeRTOS/corePKCS11/pull/86) Feature: SHA256-HMAC VerifyInit
* [#84](https://github.com/FreeRTOS/corePKCS11/pull/84) Feature: Import SHA256-HMAC secret Key

## v3.0.1 (February 2021)
* Removed default `PKCS11_PAL_DestroyObject` implementation from `core_pkcs11_mbedtls.c`. [#74](https://github.com/FreeRTOS/corePKCS11/pull/74). This means that all PAL ports must implement `PKCS11_PAL_DestroyObject`.

## v3.0.0 (December 2020)
* Changed `xFindObjectWithLabelAndClass` to include a size parameter to allow the caller to specify the size of the passed in label.
* Added CBMC memory proofs for all functions
* Removed `threading_alt.h` from corePKCS11
* Restructured third party folder in order to align with other core repositories. Folders located in `corePKCS11/3rdparty` are now in `corePKCS11/source/dependency/3rdparty`.
* Updated logs and format specifiers to use standard C types.
* Added a POSIX PAL port.

## v2.0.1 (September 2020)
* Replaced *iot* prefix on files with *core* prefix.

## v2.0.0 (September 2020)
This is the first release of the corePKCS11 library in this repository.

This library is a software based implementation of the PKCS #11 specification.

* PKCS #11 library is now decoupled from the FreeRTOS-Kernel, and instead uses mutex and heap function abstractions provided by mbed TLS.
* The PKCS #11 library logging has been overhauled and is now decoupled from FreeRTOS.
* Added `PKCS11_PAL_Initialize` to `core_pkcs11_pal.h` to defer PAL layer initialization to PKCS #11 PAL.
