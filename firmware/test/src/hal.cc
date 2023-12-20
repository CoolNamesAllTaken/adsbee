#include "hal.hh"
#include "hal_god_powers.hh"

/** Mock Pico SDK functions here for testing. **/

// Time Mocks

static uint64_t time_since_boot_us = 0;

uint64_t get_time_since_boot_us() {
    return time_since_boot_us;
}

uint32_t get_time_since_boot_ms() {
    return time_since_boot_us / 1e3;
}

// PWM Mocks: Currently unused.

/** \brief Determine the PWM slice that is attached to the specified GPIO
 *  \ingroup hardware_pwm
 *
 * \return The PWM slice number that controls the specified GPIO.
 */
static inline uint32_t pwm_gpio_to_slice_num(uint32_t gpio) {
    return (gpio >> 1u) & 7u;
}

/** \brief Determine the PWM channel that is attached to the specified GPIO.
 *  \ingroup hardware_pwm
 *
 * Each slice 0 to 7 has two channels, A and B.
 *
 * \return The PWM channel that controls the specified GPIO.
 */
static inline uint32_t pwm_gpio_to_channel(uint32_t gpio) {
    return gpio & 1u;
}

static std::tuple<uint32_t, uint32_t, uint16_t> last_pwm_set_vals = std::make_tuple(0, 0, 0);

void pwm_set_chan_level(uint32_t slice_num, uint32_t chan, uint16_t level) {
    last_pwm_set_vals = std::make_tuple(slice_num, chan, level);
}

std::tuple<uint32_t, uint32_t, uint16_t> get_last_pwm_set_vals() {
    return last_pwm_set_vals;
}

/** God Powers **/
void set_time_since_boot_us(uint64_t time_us) {
    time_since_boot_us = time_us;
}

void inc_time_since_boot_us(uint64_t inc) {
    time_since_boot_us+=inc;
}

void set_time_since_boot_ms(uint32_t time_ms) {
    time_since_boot_us = 1e3 * time_ms;
}

void inc_time_since_boot_ms(uint32_t inc) {
    time_since_boot_us += 1e3*inc;
}

