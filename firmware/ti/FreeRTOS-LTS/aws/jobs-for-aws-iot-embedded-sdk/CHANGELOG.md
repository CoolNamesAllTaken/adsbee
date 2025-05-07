# Changelog for AWS IoT Jobs Library

## v1.5.1 (June 2024)
- Fix doxygen deployment on Github

## v1.5.0 (May 2024)
- [#95](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/95) Fix misra violations
- [#93](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/93) Performance and safety improvements

## v1.4.0 (November 2023)
- [#90](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/90) Update doxygen to reflect addition of OTA Job Parser
- [#88](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/88) ADD OTA Job Parser for parsing out the fields of an incoming Job Document sent to a device from AWS IoT
- [#86](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/85) MISRA C:2012 Compliance update
- [#85](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/85) Add API's to jobs.c for interacting with the AWS IoT Jobs Service

## v1.3.0 (October 2022)

### Other Updates:
- [#67](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/67) MISRA C:2012 Compliance update
- [#65](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/65) Update CBMC starter kit
- [#61](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/61) Loop invariant update

## v1.2.0 (November 2021)

### Other Updates:
- [#57](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/57) Update litani and template submodules for cbmc
- [#55](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/55) Update Doxygen version to 1.9.2
- [#54](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/54) Updated aws-templates-for-cbmc-proofs submodule

## v1.1.1 (July 2021)

### API Changes:
- [#50](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/50) Move declaration of temporary variables after length check

## v1.1.0 (March 2021)

### API Changes:
- [#34](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/34) and [#35](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/35) Add support for generating and matching DescribeJobExecution API topics with `$next` as a jobID.
- [#38](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/38) Add new utility macros to API for compile-time generation of AWS IoT Jobs API topics.

### Other Updates:
- [#37](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/37) Add code examples in documentation of API functions.
- [#43](https://github.com/aws/Jobs-for-AWS-IoT-embedded-sdk/pull/43) Add MISRA rule 2.5 in list of ignored violations in MISRA.md file.

## v1.0.0 (November 2020)

This is the first release of the AWS IoT Jobs Library in this
repository.
