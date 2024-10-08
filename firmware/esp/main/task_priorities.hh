#ifndef TASK_PRIORITIES_HH_
#define TASK_PRIORITIES_HH_

#include <stdint.h>

#include "freertos/task.h"

static const unsigned int kSPIReceiveTaskPriority = 10;
static const unsigned int kSPIReceiveTaskCore = 1;
static const unsigned int kUDPServerTaskPriority = tskIDLE_PRIORITY;
static const unsigned int kUDPServerTaskCore = 0;

#endif /* TASK_PRIORITIES_HH_ */