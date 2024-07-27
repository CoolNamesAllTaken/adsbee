#pragma once

#include <hardware/structs/systick.h>

#include <atomic>
#include <cstddef>
#include <cstdlib>
#include <memory>
#include <stdexcept>

#include "ITimeSource.h"

namespace adsbee::time {

class SysTickTimeSource : ITimeSource {
    SysTickTimeSource(bool external)
        : _external(external),
          CLOCK_RESET_VAL(_external ? 12000000 /* 1 seconds at 12MHz */ : 12500000 /* 0.1 seconds at 125Mhz */) {
        systick_hw->csr = 0 |                      /*enable, false*/
                          (1 << 1) |               /*interrupt enable, true*/
                          (external ? 0 : 1 << 2); /*clock source*/

        systick_hw->rvr = CLOCK_RESET_VAL;
        systick_hw->cvr = 0; /* Clear current value */
        systick_hw->csr = systick_hw->csr | 1;
    }

    SysTickTimeSource(const SysTickTimeSource&) = delete;
    SysTickTimeSource& operator=(const SysTickTimeSource&) = delete;
    SysTickTimeSource(SysTickTimeSource&&) = delete;
    SysTickTimeSource& operator=(SysTickTimeSource&&) = delete;
    friend class SysTimeTimeSourceFactory;

   public:
    ~SysTickTimeSource() { systick_hw->csr = 0; }

   private:
    bool _external;
    const uint32_t CLOCK_RESET_VAL;
};

class SysTimeTimeSourceFactory {
   public:
    static std::shared_ptr<SysTickTimeSource> create(bool external) {
        if (created) {
            if (external == isExternal) {
                return instance;
            } else {
                return nullptr;
            }
        } else {
            instance = std::shared_ptr<SysTickTimeSource>(new SysTickTimeSource(external));
            isExternal = external;
            return instance;
        }
    }

   private:
    static bool created;
    static bool isExternal;
    static std::shared_ptr<SysTickTimeSource> instance;
};

}  // namespace adsbee::time