# Changelog for AWS IoT Device Shadow library

## v1.4.1 (June 2024)

### Other
- Fix doxygen deployment on Github.

## v1.4.0 (May 2024)

### Other
- [#102](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/pull/121) MISRA C:2012 compliance checked with Coverity static analysis version 2023.6.1
- [#101](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/pull/111) Update doxygen version to 1.9.6

## v1.3.0 (October 2022)

### Other
- [#102](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/pull/102) MISRA C:2012 compliance update
- [#101](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/pull/101) Update CBMC starter kit
- [#98](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/pull/98) Loop invariant update

## v1.2.0 (November 2021)

### Other
 - [#93](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/pull/93) Rename master references to main.
 - [#94](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/pull/94) Updated CBMC proof.

## v1.1.1 (July 2021)

### Other
 - [#85](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/pull/85) Fix CBMC proof for `Shadow_AssembleTopicString` API.
 - [#88](https://github.com/aws/Device-Shadow-for-AWS-IoT-embedded-sdk/pull/88) Update broken MISRA link

## v1.1.0 (March 2021)

### Updates
 - [#56](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/56), [#56](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/72) and [#73](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/73) Add support for named shadow, a feature of the AWS IoT Device Shadow service that allows you to create multiple shadows for a single IoT device.

### Other
 - [#74](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/74) Add CBMC proof for `Shadow_MatchTopic` API.

## v1.0.2 (December 2020)

### Updates
 - [#60](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/60) Cast logging arguments to C types matching the format specifier.

### Other
 - [#51](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/51) Formatting update.
 - [#57](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/57) Fix a broken link.
 - [#54](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/54), [#62](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/62) Github actions update.
 - [#58](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/58), [#61](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/61) Github repo chores
 - [#53](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/53) CBMC automation update.

## v1.0.1 (November 2020)

### Updates
 - [#41](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/41) Resolve build warning from visual studio due to terminator character.
 - [#35](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/35) Configure submodules to not be cloned by default.

### Other
 - [#19](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/19), [#27](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/27), [#29](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/29), [#32](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/32),[#34](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/34), [#43](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/43),[#44](https://github.com/aws/device-shadow-for-aws-iot-embedded-sdk/pull/44) Minor documentation updates.

## v1.0.0 (September 2020)

This is the first release of the Device Shadow library in this repository.
