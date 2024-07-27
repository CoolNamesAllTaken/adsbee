#pragma once

#include <hardware/exception.h>
#include <hardware/structs/systick.h>

#include <atomic>
#include <cstddef>
#include <cstdlib>
#include <functional>
#include <memory>
#include <mutex>
#include <stdexcept>

#include "ITimeSource.h"
#include "mutex.h"

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

        exception_set_exclusive_handler(SYSTICK_EXCEPTION, handleIrq);
    }

    SysTickTimeSource(const SysTickTimeSource&) = delete;
    SysTickTimeSource& operator=(const SysTickTimeSource&) = delete;
    SysTickTimeSource(SysTickTimeSource&&) = delete;
    SysTickTimeSource& operator=(SysTickTimeSource&&) = delete;
    friend class SysTimeTimeSourceFactory;

   public:
    ~SysTickTimeSource() { systick_hw->csr = 0; }
    uint64_t getTickCount() {
        // todo: prevent deadlock with IRQ
        std::lock_guard lock(_mutex);
        return CLOCK_RESET_VAL * _interruptCount + systick_hw->cvr;
    }

   private:
    static void handleIrq() {
        // todo: prevent deadlock with getTickCount()
        std::lock_guard lock(_mutex);
        // increment on volatile vars is deprecated
        _interruptCount = _interruptCount + 1;
    }

    bool _external;
    const uint32_t CLOCK_RESET_VAL;
    // We can make this static since there can only be one instance of the class
    static volatile uint64_t _interruptCount;
    static adsbee::hal::Mutex _mutex;
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