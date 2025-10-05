#include "cpu_utils.hh"

#ifdef ON_ESP32
temperature_sensor_handle_t CPUMonitor::temp_sensor_handle_ = nullptr;
bool CPUMonitor::temp_sensor_initialized_ = false;
#endif

void CPUMonitor::Init() {
#ifdef ON_PICO
    adc_set_temp_sensor_enabled(true);
#elif defined(ON_TI)
    Temperature_init();
#elif defined(ON_ESP32)
    temperature_sensor_config_t temp_sensor_config = {
        .range_min = 50, .range_max = 125, .clk_src = TEMPERATURE_SENSOR_CLK_SRC_DEFAULT, .flags = {.allow_pd = 0}
        // Do not allow power down in light sleep.
    };
    if (temperature_sensor_install(&temp_sensor_config, &temp_sensor_handle_) == ESP_OK) {
        temp_sensor_initialized_ = true;
    }
    if (!temp_sensor_handle_) {
        CONSOLE_ERROR("CPUMonitor::Init", "Failed to initialize temperature sensor.");
        return;
    }
    temperature_sensor_enable(temp_sensor_handle_);
#endif
}

#ifdef ON_ESP32
void CPUMonitor::ReadCPUUsage(uint8_t &core_0_usage_percent, uint8_t &core_1_usage_percent) {
    // Total number of tasks currently existing in the system
    UBaseType_t uxArraySize = uxTaskGetNumberOfTasks();

    // Allocate memory to hold task status information for all tasks
    TaskStatus_t *pxTaskStatusArray = (TaskStatus_t *)pvPortMalloc(uxArraySize * sizeof(TaskStatus_t));

    if (pxTaskStatusArray == NULL) {
        CONSOLE_ERROR("CPUMonitor::ReadCPUUsage", "Failed to allocate memory for task status array.");
        return;
    }

    // Get the task status for all tasks. ulTotalRunTime is also calculated.
    uint32_t ulTotalRunTime;
    uxArraySize = uxTaskGetSystemState(pxTaskStatusArray, uxArraySize, &ulTotalRunTime);

    // Check for a non-zero total run time to prevent division by zero
    if (ulTotalRunTime > 0) {
        // The time spent in the IDLE tasks is the time the core was *not* busy.
        uint32_t idle_runtime_core0 = 0;
        uint32_t idle_runtime_core1 = 0;

        // 1. Find the run time for the IDLE tasks (IDLE0 and IDLE1)
        for (UBaseType_t x = 0; x < uxArraySize; x++) {
            // Note: The task name length is defined by configMAX_TASK_NAME_LEN
            if (strcmp(pxTaskStatusArray[x].pcTaskName, "IDLE0") == 0) {
                idle_runtime_core0 = pxTaskStatusArray[x].ulRunTimeCounter;
            } else if (strcmp(pxTaskStatusArray[x].pcTaskName, "IDLE1") == 0) {
                idle_runtime_core1 = pxTaskStatusArray[x].ulRunTimeCounter;
            }
        }

        // 2. Calculate the utilization for each core.

        if (ulTotalRunTime > 0) {
            // Utilization = 100 - (Idle Time / Total Core Time) * 100
            core_0_usage_percent = static_cast<uint8_t>(100 - (100 * idle_runtime_core0 / ulTotalRunTime));

            core_1_usage_percent = static_cast<uint8_t>(100 - (100 * idle_runtime_core1 / ulTotalRunTime));
        }
    }

    // Free the dynamically allocated array
    vPortFree(pxTaskStatusArray);
}
#else
void CPUMonitor::Update() {
    uint32_t current_timestamp_ms = get_time_since_boot_ms();

    // Use local copies of last_update_timestamp_ms_ and ticks_since_last_update_ to avoid issues if
    // Update() is called from a different core than the core calling Tick().
    uint32_t delta_time_ms = current_timestamp_ms - last_update_timestamp_ms_;
    uint32_t ticks_since_last_update = ticks_since_last_update_;

    if (delta_time_ms < config_.update_interval_ms) {
        return;  // Not enough time has passed since the last update.
    }

    // Number of ticks that would correspond to 100% CPU usage.
    uint32_t idle_expected_ticks =
        MAX(delta_time_ms * config_.idle_ticks_per_update_interval / config_.update_interval_ms,
            1);  // No division by zero.
    uint32_t full_usage_expected_ticks =
        MAX(delta_time_ms * full_usage_ticks_per_update_interval_ / config_.update_interval_ms,
            1);  // No division by zero.
    cpu_usage_percent_ =
        100 - MIN((ticks_since_last_update - full_usage_expected_ticks) * 100 / idle_expected_ticks, 100);
    // cpu_usage_percent_ = 100 - MIN(ticks_since_last_update * 100 / idle_expected_ticks, 100);  // Avoid
    // underflow.

    // Reset the counters.
    ticks_since_last_update_ = 0;
    last_update_timestamp_ms_ = current_timestamp_ms;
}
#endif

int8_t CPUMonitor::ReadTemperatureDegC() {
#ifdef ON_PICO
    adc_select_input(kTempSensorADCChannel);             // Internal temperature sensor.
    uint32_t temp_adc_mv = adc_read() * 3300 / (0xFFF);  // Convert 12-bit ADC reading to mV assuming VREF=3.3V.
    // Convert the ADC reading to degrees C using the formula from the RP2040 datasheet.
    // See: https://datasheets.raspberrypi.com/rp2040/rp2040-datasheet.pdf Section 4.9.5
    return static_cast<int8_t>((27 - (temp_adc_mv - 706) * 581 / 1000));
#elif defined(ON_TI)
    // NOTE: Temperature_init() must be called before using this function.
    return Temperature_getTemperature();  // Convert degrees C to milliC.
#elif defined(ON_ESP32)
    if (!temp_sensor_handle_) {
        CONSOLE_ERROR("CPUMonitor::ReadTemperatureDegC",
                      "Attempted to read temperature without an initialized temperature sensor handle.");
        return 0;  // Not initialized.
    }
    if (!temp_sensor_initialized_) {
        CONSOLE_ERROR("CPUMonitor::ReadTemperatureDegC", "Attempted to read temperature without initializing sensor.");
        return 0;  // Not initialized.
    }
    float temp_deg_c = 0.0f;
    temperature_sensor_get_celsius(temp_sensor_handle_, &temp_deg_c);
    return static_cast<int8_t>(temp_deg_c);
#else
    return 0;
#endif
}