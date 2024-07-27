#pragma once

#include <atomic>
#include <cstdlib>
#include <memory>
#include <stdexcept>
#include "ITimeSource.h"
#include <hardware/structs/systick.h>

namespace adsbee::time {

    template <bool external>
    class SysTickTimeSource : ITimeSource  { 
        SysTickTimeSource();
        
        SysTickTimeSource(const SysTickTimeSource&) = delete;
        SysTickTimeSource& operator=(const SysTickTimeSource&) = delete;
        SysTickTimeSource(SysTickTimeSource&&) = delete;
        SysTickTimeSource& operator=(SysTickTimeSource&&) = delete;
        friend class SysTimeTimeSourceFactory;

        public: 
        ~SysTickTimeSource() {
        systick_hw->csr = 0;
        }
    };

    class SysTimeTimeSourceFactory {
        public:
        template<bool external>
        static std::shared_ptr<SysTickTimeSource<external>> create() {
            if (created) {
                if constexpr (external) {
                    if (!externalSysTick) {
                        return nullptr;
                    }
                    return externalSysTick;
                } else {
                    if (!internalSysTick) {
                        return nullptr;
                    }
                    return internalSysTick;
                }
            } else {
                if constexpr (external) {
                    externalSysTick = std::shared_ptr<SysTickTimeSource<true>>(new SysTickTimeSource<true>());
                    return externalSysTick;
                } else {
                    internalSysTick = std::shared_ptr<SysTickTimeSource<false>>(new SysTickTimeSource<false>());
                    return internalSysTick;
                }
            }
            return nullptr;
        }
        
        private:
        static bool created;
        static std::shared_ptr<SysTickTimeSource<true>> externalSysTick;
        static std::shared_ptr<SysTickTimeSource<false>> internalSysTick;
    };

} /*namepace adsbee::time */