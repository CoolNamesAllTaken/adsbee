// SPDX-FileCopyrightText: 2020-2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once

#include "types.h"

namespace fixedmath
  {
inline constexpr fixed_t phi{as_fixed(fixed_internal(205887))};
inline constexpr fixed_t fixpi = phi;
inline constexpr fixed_t fixpi2{as_fixed(fixed_internal(411775))};
inline constexpr fixed_t fixpi3{as_fixed(fixed_internal(617662))};
inline constexpr fixed_t fixpidiv2{as_fixed(fixed_internal(102944))};  // phi/2 90deg
inline constexpr fixed_t fixpidiv3{as_fixed(fixed_internal(68629))};   // phi/3 60deg
inline constexpr fixed_t fixpidiv4{as_fixed(fixed_internal(51472))};   // phi/4 45deg

inline constexpr fixed_t fixa90{as_fixed(fixed_internal(5898240))};
inline constexpr fixed_t fixa180{as_fixed(fixed_internal(11796480))};
inline constexpr fixed_t fixa270{as_fixed(fixed_internal(17694720))};
inline constexpr fixed_t fixa360{as_fixed(fixed_internal(23592960))};

// fixed index to radians
inline constexpr fixed_t fixtorad_r = {as_fixed(fixed_internal(1608))};     // 2pi/256
inline constexpr fixed_t radtofix_r = {as_fixed(fixed_internal(2670177))};  // 256/2pi
  }  // namespace fixedmath
