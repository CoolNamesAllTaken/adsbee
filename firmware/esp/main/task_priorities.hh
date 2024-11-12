#ifndef TASK_PRIORITIES_HH_
#define TASK_PRIORITIES_HH_

#include <stdint.h>

#include "freertos/task.h"

// This will cause weird crashes if it's too small to support full size SPI transfers!
static const unsigned int kSPIReceiveTaskStackSizeBytes = 6 * 4096;
static const unsigned int kSPIReceiveTaskPriority = 10;
static const unsigned int kSPIReceiveTaskCore = 1;
static const unsigned int kWiFiAPTaskPriority = tskIDLE_PRIORITY;
static const unsigned int kWiFiAPTaskCore = 0;
static const unsigned int kWiFiSTATaskPriority = tskIDLE_PRIORITY;
static const unsigned int kWiFiSTATaskCore = 0;
static const unsigned int kTCPServerTaskPriority = tskIDLE_PRIORITY;
static const unsigned int kTCPServerTaskCore = 0;
// Handles network console buffers but that happens in heap.
static const unsigned int kTCPServerTaskStackSizeBytes = 4096;

#endif /* TASK_PRIORITIES_HH_ */