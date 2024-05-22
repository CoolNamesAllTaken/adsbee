#include "i2c.h"
#include "pio.h"

i2c_inst i2c_0 = {.hw = nullptr, .restart_on_next = false};
i2c_inst i2c_1 = {.hw = nullptr, .restart_on_next = false};

i2c_inst_t *i2c0 = &i2c_0;
i2c_inst_t *i2c1 = &i2c_1;

pio_hw_t pio_0;
pio_hw_t pio_1;

PIO pio0 = &pio_0;
PIO pio1 = &pio_1;