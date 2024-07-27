#include "SysTickTimeSource.h"

std::shared_ptr<adsbee::time::SysTickTimeSource> adsbee::time::SysTimeTimeSourceFactory::instance = nullptr;
bool adsbee::time::SysTimeTimeSourceFactory::created = false;
bool adsbee::time::SysTimeTimeSourceFactory::isExternal;
adsbee::hal::Mutex adsbee::time::SysTickTimeSource::_mutex;
volatile uint64_t adsbee::time::SysTickTimeSource::_interruptCount;