#ifndef MOCK_I2C_H_
#define MOCK_I2C_H_

typedef struct
{
    // Empty and fake.
} i2c_hw_t;

struct i2c_inst
{
    i2c_hw_t *hw;
    bool restart_on_next;
};

typedef i2c_inst i2c_inst_t;

extern i2c_inst_t *i2c0;
extern i2c_inst_t *i2c1;

#endif /* MOCK_I2C_H_ */