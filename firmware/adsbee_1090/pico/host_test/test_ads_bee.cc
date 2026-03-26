// THIS FILE IS CURRENTLY UNUSED: Need to mock a LOT more stuff to bring ADSBee into the mix.

#include "adsbee.hh"
#include "gtest/gtest.h"
#include "hal.hh"
#include "hal_god_powers.hh"
#include "hardware/pwm.h"

TEST(ADSBee, SetMTLMilliVolts) {
    ADSBee::ADSBeeConfig config;
    ADSBee* bee = new ADSBee(config);
    bee->SetMTLMilliVolts(5);
    EXPECT_EQ(bee->GetMTLMilliVolts, 5);
    EXPECT_EQ(get_last_pwm_set_vals(), std::make_tuple(pwm_gpio_to))
}