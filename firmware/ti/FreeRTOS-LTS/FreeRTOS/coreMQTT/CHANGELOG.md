# Changelog for coreMQTT Client Library

## v2.3.1 (July 2024)

### Changes

- [#297](https://github.com/FreeRTOS/coreMQTT/pull/297) Update release action for version number update and verification.

## v2.3.0 (June 2024)

### Changes

- [#288](https://github.com/FreeRTOS/coreMQTT/pull/288) Fix time comparison overflow.

## v2.2.0 (April 2024)

### Changes

- [#283](https://github.com/FreeRTOS/coreMQTT/pull/283) Fix build error with Werror=sign-compare is enabled.
- [#279](https://github.com/FreeRTOS/coreMQTT/pull/279) Add documentation about timer behavior when it overflows.
- [#275](https://github.com/FreeRTOS/coreMQTT/pull/275) Correct TransportRecv_t documentation.
- [#268](https://github.com/FreeRTOS/coreMQTT/pull/268) Typecast outgoing and incoming publish count to unsigned longs to match format specifier.
- [#255](https://github.com/FreeRTOS/coreMQTT/pull/255) Fix MQTT_Status_strerror to return correct error on NeedMoreBytes error.
- [#252](https://github.com/FreeRTOS/coreMQTT/pull/252) Fix sending empty strings in MQTT packets.
- [#258](https://github.com/FreeRTOS/coreMQTT/pull/258) Fix race condition in handleKeepAlive.
- [#250](https://github.com/FreeRTOS/coreMQTT/pull/250) Fix timeout calculation in sendVector function to account for overflow.
- [#249](https://github.com/FreeRTOS/coreMQTT/pull/249) Replace magic numbers with macros and add explaining comments.
- [#235](https://github.com/FreeRTOS/coreMQTT/pull/235) Fix to update the timestamp of the last packet received.

## v2.1.1 (November 2022)

### Changes
- [#230](https://github.com/FreeRTOS/coreMQTT/pull/230) Fix a broken link in MISRA.md.
- [#229](https://github.com/FreeRTOS/coreMQTT/pull/229) Fixed multiple Sub/Unsub request sending logic.

## v2.1.0 (October 2022)

### Changes
- [#224](https://github.com/FreeRTOS/coreMQTT/pull/224) Update timeout duration to be constant for all transmit functions. Timeout shall occur if the whole packet is not sent within the configured timeout value.
- [#225](https://github.com/FreeRTOS/coreMQTT/pull/225) Updated the documentation of ReceiveLoop and ProcessLoop.
- [#223](https://github.com/FreeRTOS/coreMQTT/pull/223) Modify a check to make sure that keep alive is sent even when data is in the buffer.

## v2.0.0 (September 2022)

### Changes
- [#221](https://github.com/FreeRTOS/coreMQTT/pull/221) Remove LWT payload non-zero restriction.
- [#219](https://github.com/FreeRTOS/coreMQTT/pull/219) Fix MISRA deviations in the source.
- [#218](https://github.com/FreeRTOS/coreMQTT/pull/218) Fix bugs in receiveSingleIteration and optimize sendMessageVector.
- [#213](https://github.com/FreeRTOS/coreMQTT/pull/213) Fix MISRA deviations in the source.
- [#200](https://github.com/FreeRTOS/coreMQTT/pull/200) Add hooks to the code.
- [#205](https://github.com/FreeRTOS/coreMQTT/pull/205) Update logging and add MQTT_InitStatefulQoS to prevent log leaks.
- [#199](https://github.com/FreeRTOS/coreMQTT/pull/199) Make use of user provided buffer only for packet reception. Stack space will be used for sending packets.
- [#198](https://github.com/FreeRTOS/coreMQTT/pull/198) Remove timeout from MQTT\_ProcessLoop and MQTT\_ReceiveLoop and make the implementations non-blocking.
- [#196](https://github.com/FreeRTOS/coreMQTT/pull/196) Add a cancel callback API to cancel sent publish packets.
- [#191](https://github.com/FreeRTOS/coreMQTT/pull/191) Generate PINGREQ packets on idle input or output.

## v1.2.0 (November 2021)

### Changes
 - [#175](https://github.com/FreeRTOS/coreMQTT/pull/175) Change levels of some logs.
 - [#174](https://github.com/FreeRTOS/coreMQTT/pull/174) Fix warnings for some compiler options.
 - [#148](https://github.com/FreeRTOS/coreMQTT/pull/148) Update doxygen version used for documentation to 1.9.2.

## v1.1.2 (July 2021)

### Updates
 - [#168](https://github.com/FreeRTOS/coreMQTT/pull/168) Add header guards for C++ linkage.
 - [#163](https://github.com/FreeRTOS/coreMQTT/pull/163) Fix bug to check for ping responses within `MQTT_PINGRESP_TIMEOUT_MS` instead of the entire keep alive interval.
 - [#159](https://github.com/FreeRTOS/coreMQTT/pull/159) Add more checks for malformed packets when deserializing acknowledgments.

## v1.1.1 (February 2021)

### Changes
 - [#142](https://github.com/FreeRTOS/coreMQTT/pull/142), [#143](https://github.com/FreeRTOS/coreMQTT/pull/143), and [#150](https://github.com/FreeRTOS/coreMQTT/pull/150) Documentation fixes.

## v1.1.0 (December 2020)

### Updates
 - [#118](https://github.com/FreeRTOS/coreMQTT/pull/118) Use the `stdbool.h` header file instead of using preprocessor checks for when `bool` is not defined. This also provides `stdbool.readme` and `stdint.readme` files in the case that a non-C99 compiler does not provide the respective header.
 - [#120](https://github.com/FreeRTOS/coreMQTT/pull/120) Introduce a `MQTT_RECV_POLLING_TIMEOUT_MS` configuration macro to control the timeout for retrying zero byte network read operations. Previously, network read attempts were controlled by a runtime timeout parameter, which could result in a premature timeout even when data could still be read. Now, reads will wait for at least the macro timeout value before returning error. Conversely, the macro timeout value is now the maximum duration during which no data may be received, regardless of the timeout passed at runtime.
 - [#124](https://github.com/FreeRTOS/coreMQTT/pull/124), [#127](https://github.com/FreeRTOS/coreMQTT/pull/127), Introduce a `MQTT_SEND_RETRY_TIMEOUT_MS` configuration macro to control the similar case of retrying zero byte transport send operations.
 - [#139](https://github.com/FreeRTOS/coreMQTT/pull/139) Add a parameter check for empty topic filters in SUBSCRIBE and UNSUBSCRIBE packets.

### Other
 - [#107](https://github.com/FreeRTOS/coreMQTT/pull/107), [#109](https://github.com/FreeRTOS/coreMQTT/pull/109), [#121](https://github.com/FreeRTOS/coreMQTT/pull/121) Improve continuous integration checks.
 - [#110](https://github.com/FreeRTOS/coreMQTT/pull/107) Rename the master branch to main.
 - [#113](https://github.com/FreeRTOS/coreMQTT/pull/113), [#116](https://github.com/FreeRTOS/coreMQTT/pull/116), [#117](https://github.com/FreeRTOS/coreMQTT/pull/117), [#125](https://github.com/FreeRTOS/coreMQTT/pull/125) Update logging and cast to C standard types for logs.
 - [#115](https://github.com/FreeRTOS/coreMQTT/pull/115), [#122](https://github.com/FreeRTOS/coreMQTT/pull/122), [#128](https://github.com/FreeRTOS/coreMQTT/pull/128), [#132](https://github.com/FreeRTOS/coreMQTT/pull/132), [#133](https://github.com/FreeRTOS/coreMQTT/pull/133), [#136](https://github.com/FreeRTOS/coreMQTT/pull/136), [#138](https://github.com/FreeRTOS/coreMQTT/pull/138) Minor documentation updates.

## v1.0.1 (November 2020)

### Updates
 - [#83](https://github.com/FreeRTOS/coreMQTT/pull/83) Accept duplicate publishes regardless of the value of the "DUP" flag.
 - [#86](https://github.com/FreeRTOS/coreMQTT/pull/86) Remove `const` qualifier from transport interface function pointers.
 - [#91](https://github.com/FreeRTOS/coreMQTT/pull/91) `transport_interface.h` was moved to the `interface/` directory.

### Other
 - [#69](https://github.com/FreeRTOS/coreMQTT/pull/69), [#80](https://github.com/FreeRTOS/coreMQTT/pull/80), [#95](https://github.com/FreeRTOS/coreMQTT/pull/95), [#98](https://github.com/FreeRTOS/coreMQTT/pull/98) Minor documentation updates.
 - [#71](https://github.com/FreeRTOS/coreMQTT/pull/71) Set publish payloads to NULL when they are zero length.
 - [#74](https://github.com/FreeRTOS/coreMQTT/pull/74) Resolve clang build warnings from the unit tests.
 - [#75](https://github.com/FreeRTOS/coreMQTT/pull/75) Configure submodules to not be cloned by default.

## v1.0.0 (September 2020)

This is the first release of a coreMQTT client library in this repository.

The MQTT library is a client-side implementation that is compliant with the [MQTT 3.1.1 specification](https://docs.oasis-open.org/mqtt/mqtt/v3.1.1/os/mqtt-v3.1.1-os.html).   It is optimized for resource-constrained devices, and does not allocate any memory.
