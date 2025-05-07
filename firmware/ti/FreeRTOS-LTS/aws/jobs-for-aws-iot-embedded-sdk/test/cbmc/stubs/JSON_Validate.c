#include <stdlib.h>
#include "../coreJSON/source/include/core_json.h"

JSONStatus_t JSON_Validate( const char * buf,
                            size_t max )
{
    __CPROVER_assert( buf != NULL, "Buffer must not be null." );

    JSONStatus_t ret = 0;

    __CPROVER_assume( ( ret == JSONNullParameter ) || ( ret == JSONBadParameter ) ||
                      ( ret == JSONSuccess ) || ( ret = JSONIllegalDocument ) );

    return ret;
}
