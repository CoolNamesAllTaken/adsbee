/* Copyright 2020-2023 Espressif Systems (Shanghai) CO LTD
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#warning Please replace serial_io.h with esp_loader_io.h and change the function names \
to match the new API

/* Defines used to avoid breaking existing ports */
#define loader_port_change_baudrate loader_port_change_transmission_rate
#define loader_port_serial_write    loader_port_write
#define loader_port_serial_read     loader_port_read

#include "esp_loader_io.h"
