#ifndef TASK_PRIORITIES_HH_
#define TASK_PRIORITIES_HH_

#include <stdint.h>

#include "freertos/task.h"

static const unsigned int kSPIReceiveTaskPriority = 10;
static const unsigned int kSPIReceiveTaskCore = 1;
static const unsigned int kWiFiAPTaskPriority = tskIDLE_PRIORITY;
static const unsigned int kWiFiAPTaskCore = 0;
static const unsigned int kWiFiSTATaskPriority = tskIDLE_PRIORITY;
static const unsigned int kWiFiSTATaskCore = 0;

#endif /* TASK_PRIORITIES_HH_ */