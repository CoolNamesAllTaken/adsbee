#ifndef MOCK_PIO_H_
#define MOCK_PIO_H_

typedef struct
{
    // Empty and fake.
} pio_hw_t;

typedef pio_hw_t *PIO;

extern PIO pio0;
extern PIO pio1;

#endif /* MOCK_PIO_H_ */