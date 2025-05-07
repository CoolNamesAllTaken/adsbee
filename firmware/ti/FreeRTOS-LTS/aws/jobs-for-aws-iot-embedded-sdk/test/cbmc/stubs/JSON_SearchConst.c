#include <stdlib.h>
#include "../coreJSON/source/include/core_json.h"

JSONStatus_t JSON_SearchConst( char * buf,
                               size_t max,
                               const char * query,
                               size_t queryLength,
                               char ** outValue,
                               size_t * outValueLength,
                               JSONTypes_t * outType )
{
    __CPROVER_assert( buf != NULL, "Buffer is not NULL" );
    __CPROVER_assert( query != NULL, "query is not NULL" );

    JSONStatus_t ret = 0;

    __CPROVER_assume( ( ret == JSONNullParameter ) || ( ret == JSONBadParameter ) ||
                      ( ret == JSONSuccess ) || ( ret == JSONNotFound ) );

    return ret;
}
