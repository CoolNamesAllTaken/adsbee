#include "SysTickTimeSource.h"

namespace adsbee::time{
bool SysTimeTimeSourceFactory::created = false;
std::shared_ptr<SysTickTimeSource<true>> SysTimeTimeSourceFactory::externalSysTick = nullptr;
std::shared_ptr<SysTickTimeSource<false>> SysTimeTimeSourceFactory::internalSysTick = nullptr;
}