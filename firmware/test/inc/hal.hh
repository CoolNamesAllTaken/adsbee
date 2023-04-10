#ifndef _HAL_HH_
#define _HAL_HH_

#include "stdint.h"

uint64_t time_since_boot_us();

// Additional God Power functions available for creating tests.
void set_time_since_boot_us(uint64_t time_us);

#endif /* _HAL_HH_ */