# Changelog for coreHTTP Client Library

## v3.1.1 (June 2024)
- Fix doxygen deployment on Github.

## v3.1.0 (May 2023)
- [#176](https://github.com/FreeRTOS/coreHTTP/pull/176) Update llhttp to v6.1.1. Update CMock to v2.5.3.
- [#174](https://github.com/FreeRTOS/coreHTTP/pull/174) MISRA C:2012 compliance update
- [#173](https://github.com/FreeRTOS/coreHTTP/pull/173) Add on_status_complete callback
- [#167](https://github.com/FreeRTOS/coreHTTP/pull/167) Expose HTTPClient_SendHttpData, HTTPClient_SendHttpHeaders and HTTPClient_ReceiveAndParseHttpResponse for enhanced usability
- [#164](https://github.com/FreeRTOS/coreHTTP/pull/164) Support http request without HTTP_USER_AGENT_FIELD
- [#159](https://github.com/FreeRTOS/coreHTTP/pull/159) Handle upgrade header
- [#151](https://github.com/FreeRTOS/coreHTTP/pull/151) Update doxygen to v1.9.6

## v3.0.0 (October 2022)

### Updates

- [#134](https://github.com/FreeRTOS/coreHTTP/pull/134), [#138](https://github.com/FreeRTOS/coreHTTP/pull/138) Replace strncpy with memcpy to remove warnings
- [#132](https://github.com/FreeRTOS/coreHTTP/pull/132), [#142](https://github.com/FreeRTOS/coreHTTP/pull/142), [#144](https://github.com/FreeRTOS/coreHTTP/pull/144) MISRA C:2012 compliance update
- [#129](https://github.com/FreeRTOS/coreHTTP/pull/129) Update http-parser to use llhttp
- [#127](https://github.com/FreeRTOS/coreHTTP/pull/127) CBMC proof changes, and updates to use llhttp
- [#126](https://github.com/FreeRTOS/coreHTTP/pull/126) Replace http-parser with llhttp. Using llhttp requires C99, so this library will need to use C99 at minimum as well. The swap to llhttp impacts the HTTPParsingContext_t struct, as well as many of the functions in coreHTTP. coreHTTP APIs preserve backwards compatibility by usage, however any use of the internal structures or dependency on http parser directly can cause compatibility issues.
- [#125](https://github.com/FreeRTOS/coreHTTP/pull/125) Add response buffer len check

## v2.1.0 (Nov 2021)

### Updates

- [#114](https://github.com/FreeRTOS/coreHTTP/pull/114) Update http-parser version in manifest to reflect commit
- [#112](https://github.com/FreeRTOS/coreHTTP/pull/112) Add function prototypes for exported functions to CBMC proof harnesses
- [#111](https://github.com/FreeRTOS/coreHTTP/pull/111) Update Doxygen version to 1.9.2

## v2.0.2 (July 2021)

### Updates

- [#109](https://github.com/FreeRTOS/coreHTTP/pull/109) Add C++ header guards
- [#106](https://github.com/FreeRTOS/coreHTTP/pull/106) Update case-insensitive compare function for header-field parser
- [#104](https://github.com/FreeRTOS/coreHTTP/pull/104) Update CBMC proofs to work with the latest version of CBMC

## v2.0.1 (February 2021)

### Other

- [#89](https://github.com/FreeRTOS/coreHTTP/pull/89) Fix documentation of memory size estimates of the library.

## v2.0.0 (December 2020)

### Updates

 - [#83](https://github.com/FreeRTOS/coreHTTP/pull/83) Implement transport send and receive retry timeouts in coreHTTP. This change adds a timestamp callback function to the HTTPResponse_t struct, and new configuration macros to set the transport send and receive retry timeouts. Due to the HTTPResponse_t struct field addition, coreHTTP v2.0.0 is not backward compatible under certain conditions.
 - [#79](https://github.com/FreeRTOS/coreHTTP/pull/79), [#82](https://github.com/FreeRTOS/coreHTTP/pull/82) transport_interface.h documentation updates.
 - [#75](https://github.com/FreeRTOS/coreHTTP/pull/75) Small fix to cast logging arguments to types matching the format specifiers.

### Other
 - [#70](https://github.com/FreeRTOS/coreHTTP/pull/70), [#72](https://github.com/FreeRTOS/coreHTTP/pull/72), [#78](https://github.com/FreeRTOS/coreHTTP/pull/78) Github actions updates.
 - [#73](https://github.com/FreeRTOS/coreHTTP/pull/73), [#76](https://github.com/FreeRTOS/coreHTTP/pull/76) Github repo chores.
 - [#71](https://github.com/FreeRTOS/coreHTTP/pull/71) CBMC automation chore.
 - [#81](https://github.com/FreeRTOS/coreHTTP/pull/81), [#84](https://github.com/FreeRTOS/coreHTTP/pull/84) Doxygen memory estimates table update.

## v1.0.0 November 2020

This is the first release of the coreHTTP client library in this repository.

The HTTP client library is a client-side implementation that supports a subset
of the HTTP/1.1 protocol. It is optimized for resource-constrained devices, and
does not allocate any memory.
