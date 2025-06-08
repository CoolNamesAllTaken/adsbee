#include <stdlib.h>
#include <string.h>

size_t strnlen( const char * s,
                size_t maxlen )
{
    __CPROVER_assert( s != NULL, "String pointer must not be null." );

    size_t result;

    result = ( size_t ) strlen( s );

    if( result > maxlen )
    {
        result = maxlen;
    }

    return result;
}
