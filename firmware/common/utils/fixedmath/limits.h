// SPDX-FileCopyrightText: 2020-2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once

#include "types.h"

namespace fixedmath
  {
  }

namespace std
  {
template<>
struct numeric_limits<fixedmath::fixed_t>
  {
  using value_type = fixedmath::fixed_t;
  using fixed_internal = fixedmath::fixed_internal;
  using fix_carrier_t = fixedmath::fix_carrier_t;

  static constexpr bool is_integer{false};
  static constexpr bool is_specialized{true};
  static constexpr bool is_signed{true};
  static constexpr bool is_exact{true};
  static constexpr bool has_infinity{};
  static constexpr bool has_quiet_NaN{true};
  static constexpr bool has_signaling_NaN{};
  static constexpr bool has_denorm_loss{};
  static constexpr float_round_style round_style{round_toward_zero};
  static constexpr bool is_iec559{};
  static constexpr bool is_bounded{true};
  static constexpr bool is_modulo{};
  static constexpr int digits{16};
  static constexpr int digits10{4};
  static constexpr int max_digits10{6};
  static constexpr int radix{2};
  static constexpr bool traps{true};
  static constexpr bool tinyness_before{};

  static consteval value_type min() noexcept { return fix_carrier_t{fixed_internal{1}}; }

  static consteval value_type lowest() noexcept { return fix_carrier_t{fixed_internal{-0x7FFFFFFFFFFFFFFEll}}; }

  static consteval value_type max() noexcept { return fix_carrier_t{fixed_internal{0x7FFFFFFFFFFFFFFEll}}; }

  static consteval value_type one() noexcept { return fix_carrier_t{fixed_internal{65536}}; }

  static consteval value_type epsilon() noexcept { return fix_carrier_t{fixed_internal{1}}; }

  static consteval value_type round_error() noexcept { return fix_carrier_t{fixed_internal{1}}; }

  static consteval value_type quiet_NaN() noexcept { return fix_carrier_t{fixed_internal{0x7FFFFFFFFFFFFFFFll}}; }

  static consteval int32_t max_integral() noexcept { return 2147483647; }

  static consteval int32_t min_integral() noexcept { return -2147483647; }
  };

  }  // namespace std

namespace fixedmath
  {
inline consteval auto quiet_NaN_result() -> fixed_t { return std::numeric_limits<fixed_t>::quiet_NaN(); }
  }  // namespace fixedmath

