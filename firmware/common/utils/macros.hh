#ifndef MACROS_HH_
#define MACROS_HH_

// Conditionally define the MAX macro because the pico platform includes it by default in pico/platform.h.
#ifndef MAX
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#endif

#ifndef MIN
#define MIN(a, b) ((b) > (a) ? (a) : (b))
#endif

#ifndef ABS
#define ABS(x) ((x) < 0 ? -(x) : (x))
#endif

#endif /* MACROS_HH_ */