# Changelog for backoffAlgorithm Library

## v1.4.1 (June 2024)

### Changes
- Fix doxygen deployment on Github.

## v1.4.0 (May 2024)

### Changes
- [#51](https://github.com/FreeRTOS/backoffAlgorithm/pull/51) Update MISRA Check Information.
- [#45](https://github.com/FreeRTOS/backoffAlgorithm/pull/45) Update doxygen version to 1.9.6.

## v1.3.0 (October 2022)

### Changes

- [#38](https://github.com/FreeRTOS/backoffAlgorithm/pull/38) MISRA compliance update

## v1.2.0 (November 2021)

### Changes

- [#31](https://github.com/FreeRTOS/backoffAlgorithm/pull/31) Update doxygen version for documentation.
- [#30](https://github.com/FreeRTOS/backoffAlgorithm/pull/30) Add code examples to documentation.

## v1.1.0 (July 2021)

### Changes

- [#29](https://github.com/FreeRTOS/backoffAlgorithm/pull/29) Set BACKOFF_ALGORITHM_RETRY_FOREVER to be nonzero and add header guards for C++ linkage.
- [#27](https://github.com/FreeRTOS/backoffAlgorithm/pull/27) Fix incorrect comment about use of BACKOFF_ALGORITHM_RETRY_FOREVER constant in BackoffAlgorithm_GetNextBackoff API.

## v1.0.1 (February 2021)

### Changes

- [#24](https://github.com/FreeRTOS/backoffAlgorithm/pull/24) Fix MISRA 10.4 and 10.7 rule violations, and add documentation of MISRA compliance.
- [#18](https://github.com/FreeRTOS/backoffAlgorithm/pull/18), [#19](https://github.com/FreeRTOS/backoffAlgorithm/pull/19), and [#20](https://github.com/FreeRTOS/backoffAlgorithm/pull/20) Documentation fixes.

## v1.0.0 (December 2020)

This is the first release of the backoffAlgorithm library in this repository.

The backoffAlgorithm library is a utility library to calculate backoff period using an exponential backoff with jitter algorithm for retrying network operations (like failed network connection with server).
This library uses the "Full Jitter" strategy for the exponential backoff with jitter algorithm.
More information about the algorithm can be seen in the [Exponential Backoff and Jitter](https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/) AWS blog.
