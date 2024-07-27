#include "SysTickTimeSource.h"
#include <hardware/structs/systick.h>
#include <hardware/exception.h>

namespace adsbee::time {

template<>
SysTickTimeSource<true>::SysTickTimeSource() {
    systick_hw->csr = 
        0 | /*enable, false*/ 
        (1 << 1) | /*interrupt enable, true*/ 
        (0 << 2); /*clock source, external*/

    systick_hw->rvr = 12000000; /* 1 seconds at 12MHz */
    systick_hw->cvr = 0; /* Clear current value */
    systick_hw->csr = systick_hw->csr | 1;
}

}