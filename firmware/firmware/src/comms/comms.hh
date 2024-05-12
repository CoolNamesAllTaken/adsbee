#ifndef _COMMS_HH_
#define _COMMS_HH_

#include "cpp_at.hh"

extern CppAT at_parser;

bool InitCommsAT();
bool UpdateCommsAT();

typedef enum {
    RUN = 0,
    CONFIG = 1
} ATConfigMode_t;



#endif /* _COMMS_HH_ */