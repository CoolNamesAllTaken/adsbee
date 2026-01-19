#pragma once

// FIXME: If the ISRS_ON_CORE1 define is uncommented, DemodComplete ISR will run on both core 0 and core 1
// simultaneously, leading to packet corruption.

// #define ISRS_ON_CORE1