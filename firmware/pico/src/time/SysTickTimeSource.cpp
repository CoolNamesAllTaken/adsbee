#include "SysTickTimeSource.h"

std::shared_ptr<adsbee::time::SysTickTimeSource> adsbee::time::SysTimeTimeSourceFactory::instance = nullptr;
bool adsbee::time::SysTimeTimeSourceFactory::created = false;
bool adsbee::time::SysTimeTimeSourceFactory::isExternal;