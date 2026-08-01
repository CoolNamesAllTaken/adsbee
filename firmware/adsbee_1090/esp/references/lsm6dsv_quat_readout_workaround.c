#include "application.h"
#include "board.h"
#include "device.h"
#include <math.h>

#define SFLP_ODR_15HZ   (0 << 3)
#define SFLP_ODR_30HZ   (1 << 3)
#define SFLP_ODR_60HZ   (2 << 3)
#define SFLP_ODR_120HZ  (3 << 3)
#define SFLP_ODR_240HZ  (4 << 3)
#define SFLP_ODR_480HZ  (5 << 3)
#define SFLP_ODR_960HZ  (6 << 3)
#define SFLP_ODR_MASK   0x38

static void load_config(uint8_t print_en);
static void normalize(float quat[4], __fp16 sflp[4]);

static struct interface interface;
static volatile uint8_t int1, int2;

static uint8_t config[][2] = {
  // sflp and sensor conf
  { 0x01, 0x80 },
  { 0x04, 0x02 }, // enable game rotation vector
  { 0x5E, 0x40 | SFLP_ODR_120HZ }, // default (tilt) + set game_odr = 120 Hz
  { 0x01, 0x00 },
  { 0x13, 0x08 }, // DRDY_MASK = 1
  { 0x15, 0x03 }, // gyr fs = 1000 dps
  { 0x17, 0x02 }, // acc fs = 8 g
  { 0x63, 0x30 }, // EMB_FUNC_IRQ_MASK_GY_SETTL = 1 | EMB_FUNC_IRQ_MASK_XL_SETTL = 1
  { 0x10, 0x06 }, // acc odr = 120 Hz
  { 0x11, 0x06 }, // gyr odr = 120 Hz
  { 0x0E, 0x80 }, // INT2_EMB_FUNC_ENDOP = 1
};

void application(void)
{
  /* select vdd/vddio and wait for stable value */
  delay(300);
  set_vdd(1.8);
  set_vddio(1.8);
  delay(300);

  /* select interface */
  interface.bus = SPI;
  interface.wire = WIRE_4;
  set_interface(&interface);

  uint8_t whoami;
  read(0x0F, &whoami, 1);

  /* load device configuration */
  load_config(1);

  while (1) {
    if (int2) {
      int2 = 0;
      float quat[4];
      union { __fp16 sflp[4]; uint8_t buff[8]; };

      write(0x01, 0x80);
      write(0x17, 0x20);
      write(0x02, 0x31);

      for (uint8_t i = 0; i < 8; i++) {
        write(0x08, 0x4C + i);
        read(0x09, &buff[i], 1);
      }

      write(0x17, 0x00);
      write(0x01, 0x00);

      normalize(quat, sflp);
      printf("%f\t%f\t%f\t%f\n", quat[1], quat[2], quat[3], quat[0]);
    }
  }
}

static void normalize(float quat[4], __fp16 sflp[4])
{
  float n = 0;

  quat[0] = sflp[0];
  quat[1] = sflp[1];
  quat[2] = sflp[2];
  quat[3] = sflp[3];

  for (uint8_t i = 0; i < 4; i++)
    n += quat[i] * quat[i];

  n = sqrtf(n);

  for (uint8_t i = 0; i < 4; i++)
    quat[i] /= n;
}

void int2_callback(void)
{
  int2 = 1;
}

static void load_config(uint8_t print_en)
{
  if (print_en) {
    printf("Loading configuration...\r\n");
  }

  for (uint16_t i = 0; i < sizeof(config) / sizeof(config[0]); i++) {
    write(config[i][0], config[i][1]);
    if (print_en) {
      printf("0x%02X = 0x%02X\r\n", config[i][0], config[i][1]);
    }
  }
}
