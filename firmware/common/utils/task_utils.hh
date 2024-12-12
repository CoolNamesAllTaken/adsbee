#ifndef TASK_UTILS_HH_
#define TASK_UTILS_HH_

#ifdef ON_ESP32

#include "comms.hh"
#include "esp_log.h"
#include "esp_timer.h"

#endif /* ON_ESP32 */

// Function to set up the delayed call
inline esp_err_t ScheduleDelayedFunctionCall(int delay_ms, esp_timer_cb_t delayed_function) {
    esp_timer_handle_t timer;
    esp_timer_create_args_t timer_args = {.callback = delayed_function, .arg = NULL, .name = "one_shot_timer"};

    // Create the timer
    esp_err_t ret = esp_timer_create(&timer_args, &timer);
    if (ret != ESP_OK) {
        CONSOLE_ERROR("ScheduleDelayedFunctionCall", "Failed to create timer");
        return ret;
    }

    // Start the timer (one-shot mode)
    ret = esp_timer_start_once(timer, delay_ms * 1000);  // Convert ms to microseconds
    if (ret != ESP_OK) {
        CONSOLE_ERROR("ScheduleDelayedFunctionCall", "Failed to start timer");
        esp_timer_delete(timer);
        return ret;
    }

    return ESP_OK;
}

#endif /* TASK_UTILS_HH_ */