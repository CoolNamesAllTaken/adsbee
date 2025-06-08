#include <core_json.h>
#include <stdint.h>

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  JSON_Validate((char *)data, size);
  return 0;
}
