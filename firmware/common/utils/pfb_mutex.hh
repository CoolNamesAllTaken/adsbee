#ifndef PFB_MUTEX_HH_
#define PFB_MUTEX_HH_

// Platform abstraction for mutex locks used by PFBQueue.
// To use a different platform's mutex implementation, replace this file or
// define PFB_MUTEX_CUSTOM before including data_structures.hh and provide
// your own implementations of the macros below.

#ifndef PFB_MUTEX_CUSTOM

#if __has_include("pico/mutex.h")
// Pico SDK mutex implementation
#include "pico/mutex.h"

#define PFB_MUTEX_TYPE mutex_t
#define PFB_MUTEX_INIT(mtx) mutex_init(&(mtx))
#define PFB_MUTEX_LOCK(mtx) mutex_enter_blocking(&(mtx))
#define PFB_MUTEX_UNLOCK(mtx) mutex_exit(&(mtx))

#else
// Stub implementation for platforms without mutex support (single-core/non-concurrent use).
// Replace this section for other platforms (e.g., FreeRTOS, std::mutex, etc.)

struct PfbMutexStub {};
#define PFB_MUTEX_TYPE PfbMutexStub
#define PFB_MUTEX_INIT(mtx) ((void)0)
#define PFB_MUTEX_LOCK(mtx) ((void)0)
#define PFB_MUTEX_UNLOCK(mtx) ((void)0)

#endif  // PICO_SDK

#endif  // PFB_MUTEX_CUSTOM

#endif  // PFB_MUTEX_HH_
