## backoffAlgorithm Library

**[API Documentation Pages for current and previous releases of this library can be found here](https://freertos.github.io/backoffAlgorithm/)**

This repository contains the backoffAlgorithm library, a utility library to
calculate backoff period using an exponential backoff with jitter algorithm for
retrying network operations (like failed network connection with server). This
library uses the "Full Jitter" strategy for the exponential backoff with jitter
algorithm. More information about the algorithm can be seen in the
[Exponential Backoff and Jitter](https://aws.amazon.com/blogs/architecture/exponential-backoff-and-jitter/)
AWS blog.

The backoffAlgorithm library is distributed under the
[MIT Open Source License](LICENSE).

Exponential backoff with jitter is typically used when retrying a failed network
connection or operation request with the server. An exponential backoff with
jitter helps to mitigate failed network operations with servers, that are caused
due to network congestion or high request load on the server, by spreading out
retry requests across multiple devices attempting network operations. Besides,
in an environment with poor connectivity, a client can get disconnected at any
time. A backoff strategy helps the client to conserve battery by not repeatedly
attempting reconnections when they are unlikely to succeed.

See memory requirements for this library
[here](./docs/doxygen/include/size_table.md).

**backoffAlgorithm v1.3.0
[source code](https://github.com/FreeRTOS/backoffAlgorithm/tree/v1.3.0/source)
is part of the
[FreeRTOS 202210.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202210.00-LTS)
release.**

**backoffAlgorithm v1.0.0
[source code](https://github.com/FreeRTOS/backoffAlgorithm/tree/v1.0.0/source)
is part of the
[FreeRTOS 202012.00 LTS](https://github.com/FreeRTOS/FreeRTOS-LTS/tree/202012.00-LTS)
release.**

## Reference example

The example below shows how to use the backoffAlgorithm library on a POSIX
platform to retry a DNS resolution query for `amazon.com`.

```c
#include "backoff_algorithm.h"
#include <stdlib.h>
#include <string.h>
#include <netdb.h>
#include <unistd.h>
#include <time.h>

/* The maximum number of retries for the example code. */
#define RETRY_MAX_ATTEMPTS            ( 5U )

/* The maximum back-off delay (in milliseconds) for between retries in the example. */
#define RETRY_MAX_BACKOFF_DELAY_MS    ( 5000U )

/* The base back-off delay (in milliseconds) for retry configuration in the example. */
#define RETRY_BACKOFF_BASE_MS         ( 500U )

int main()
{
    /* Variables used in this example. */
    BackoffAlgorithmStatus_t retryStatus = BackoffAlgorithmSuccess;
    BackoffAlgorithmContext_t retryParams;
    char serverAddress[] = "amazon.com";
    uint16_t nextRetryBackoff = 0;

    int32_t dnsStatus = -1;
    struct addrinfo hints;
    struct addrinfo ** pListHead = NULL;
    struct timespec tp;

    /* Add hints to retrieve only TCP sockets in getaddrinfo. */
    ( void ) memset( &hints, 0, sizeof( hints ) );

    /* Address family of either IPv4 or IPv6. */
    hints.ai_family = AF_UNSPEC;
    /* TCP Socket. */
    hints.ai_socktype = ( int32_t ) SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;

    /* Initialize reconnect attempts and interval. */
    BackoffAlgorithm_InitializeParams( &retryParams,
                                       RETRY_BACKOFF_BASE_MS,
                                       RETRY_MAX_BACKOFF_DELAY_MS,
                                       RETRY_MAX_ATTEMPTS );


    /* Seed the pseudo random number generator used in this example (with call to
     * rand() function provided by ISO C standard library) for use in backoff period
     * calculation when retrying failed DNS resolution. */

    /* Get current time to seed pseudo random number generator. */
    ( void ) clock_gettime( CLOCK_REALTIME, &tp );
    /* Seed pseudo random number generator with seconds. */
    srand( tp.tv_sec );

    do
    {
        /* Perform a DNS lookup on the given host name. */
        dnsStatus = getaddrinfo( serverAddress, NULL, &hints, pListHead );

        /* Retry if DNS resolution query failed. */
        if( dnsStatus != 0 )
        {
            /* Generate a random number and get back-off value (in milliseconds) for the next retry.
             * Note: It is recommended to use a random number generator that is seeded with
             * device-specific entropy source so that backoff calculation across devices is different
             * and possibility of network collision between devices attempting retries can be avoided.
             *
             * For the simplicity of this code example, the pseudo random number generator, rand()
             * function is used. */
            retryStatus = BackoffAlgorithm_GetNextBackoff( &retryParams, rand(), &nextRetryBackoff );

            /* Wait for the calculated backoff period before the next retry attempt of querying DNS.
             * As usleep() takes nanoseconds as the parameter, we multiply the backoff period by 1000. */
            ( void ) usleep( nextRetryBackoff * 1000U );
        }
    } while( ( dnsStatus != 0 ) && ( retryStatus != BackoffAlgorithmRetriesExhausted ) );

    return dnsStatus;
}
```

## Building the library

A compiler that supports **C90 or later** such as _gcc_ is required to build the
library.

Additionally, the library uses a header file introduced in ISO C99, `stdint.h`.
For compilers that do not provide this header file, the
[source/include](source/include) directory contains
[stdint.readme](source/include/stdint.readme), which can be renamed to
`stdint.h` to build the backoffAlgorithm library.

For instance, if the example above is copied to a file named `example.c`, _gcc_
can be used like so:

```bash
gcc -I source/include example.c source/backoff_algorithm.c -o example
./example
```

_gcc_ can also produce an output file to be linked:

```bash
gcc -I source/include -c source/backoff_algorithm.c
```

## Building unit tests

### Checkout Unity Submodule

By default, the submodules in this repository are configured with `update=none`
in [.gitmodules](.gitmodules), to avoid increasing clone time and disk space
usage of other repositories (like
[amazon-freertos](https://github.com/aws/amazon-freertos) that submodules this
repository).

To build unit tests, the submodule dependency of Unity is required. Use the
following command to clone the submodule:

```
git submodule update --checkout --init --recursive test/unit-test/Unity
```

### Platform Prerequisites

- For running unit tests
  - C89 or later compiler like gcc
  - CMake 3.13.0 or later
- For running the coverage target, gcov is additionally required.

### Steps to build Unit Tests

1. Go to the root directory of this repository. (Make sure that the **Unity**
   submodule is cloned as described [above](#checkout-unity-submodule).)

1. Create build directory: `mkdir build && cd build`

1. Run _cmake_ while inside build directory: `cmake -S ../test`

1. Run this command to build the library and unit tests: `make all`

1. The generated test executables will be present in `build/bin/tests` folder.

1. Run `ctest` to execute all tests and view the test run summary.

## Contributing

See [CONTRIBUTING.md](./.github/CONTRIBUTING.md) for information on
contributing.
