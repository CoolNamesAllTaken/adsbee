#ifndef TASK_UTILS_HH_
#define TASK_UTILS_HH_

#ifdef ON_ESP32

#include "comms.hh"
#include "esp_log.h"
#include "esp_timer.h"
#include <stdlib.h>

struct DelayedCallContext {
    esp_timer_handle_t timer;
    esp_timer_cb_t real_callback;
};

// Wrapper that deletes the timer and frees the context before invoking the real callback,
// preventing the handle leak that occurs when one-shot timers are never explicitly deleted.
static void delayed_call_wrapper(void* arg) {
    DelayedCallContext* ctx = static_cast<DelayedCallContext*>(arg);
    esp_timer_handle_t timer = ctx->timer;
    esp_timer_cb_t cb = ctx->real_callback;
    free(ctx);
    esp_timer_delete(timer);
    cb(nullptr);
}

inline esp_err_t ScheduleDelayedFunctionCall(int delay_ms, esp_timer_cb_t delayed_function) {
    DelayedCallContext* ctx = static_cast<DelayedCallContext*>(malloc(sizeof(DelayedCallContext)));
    if (ctx == nullptr) {
        CONSOLE_ERROR("ScheduleDelayedFunctionCall", "Failed to allocate timer context");
        return ESP_ERR_NO_MEM;
    }
    ctx->real_callback = delayed_function;

    esp_timer_create_args_t timer_args = {};
    timer_args.callback = delayed_call_wrapper;
    timer_args.arg = ctx;
    timer_args.name = "one_shot_timer";

    esp_err_t ret = esp_timer_create(&timer_args, &ctx->timer);
    if (ret != ESP_OK) {
        CONSOLE_ERROR("ScheduleDelayedFunctionCall", "Failed to create timer");
        free(ctx);
        return ret;
    }

    ret = esp_timer_start_once(ctx->timer, delay_ms * 1000);  // Convert ms to microseconds
    if (ret != ESP_OK) {
        CONSOLE_ERROR("ScheduleDelayedFunctionCall", "Failed to start timer");
        esp_timer_delete(ctx->timer);
        free(ctx);
        return ret;
    }

    return ESP_OK;
}

#endif /* ON_ESP32 */

#endif /* TASK_UTILS_HH_ */