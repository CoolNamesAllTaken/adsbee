#ifndef JSON_UTILS_HH_
#define JSON_UTILS_HH_

#include <cstdio>

#include "stdint.h"

/**
 * Writes an array of objects to a JSON formatted array, with the provided label and format for each element.
 * @param[in] buf Buffer to write to.
 * @param[in] buf_len Length of buffer to write to.
 * @param[in] label C-string label to use for the name of the array in the JSON object.
 * @param[in] arr Array of elements to iterate through.
 * @param[in] format printf format string to use when printing each element.
 * @param[in] trailing_comma Whether to add a trailing comma after the array (in case this array is not the last item in
 * the JSON dictionary.)
 */
template <typename T, size_t N>
static inline uint16_t ArrayToJSON(char* buf, uint16_t buf_len, const char* label, const T (&arr)[N],
                                   const char* format, bool trailing_comma = false) {
    uint16_t chars_written = 0;
    chars_written += snprintf(buf + chars_written, buf_len - chars_written, "\"%s\": [", label);
    for (size_t i = 0; i < N; i++) {
        chars_written += snprintf(buf + chars_written, buf_len - chars_written, format, arr[i]);
        chars_written += snprintf(buf + chars_written, buf_len - chars_written, "%s", i < N - 1 ? ", " : "");
    }
    chars_written += snprintf(buf + chars_written, buf_len - chars_written, "]%s", trailing_comma ? ", " : " ");
    return chars_written;
}

#endif /* JSON_UTILS_HH_ */