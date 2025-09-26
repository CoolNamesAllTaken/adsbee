// SPDX-FileCopyrightText: 2020-2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once

#include "../types.h"
#include "type_traits.h"
#include <bit>

namespace fixedmath::inline v2::detail
  {

template<int digits>
[[gnu::const, gnu::always_inline]]
constexpr auto unsigned_shift_left_signed(std::signed_integral auto value) noexcept -> fixed_internal
  {
  return static_cast<fixed_internal>(
    (static_cast<fixed_internal_unsigned>(value) << digits)
    | (static_cast<fixed_internal_unsigned>(value) & (fixed_internal_unsigned(1) << 63u))
  );
  }

template<int digits>
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto unsigned_shift_left_unsigned(std::unsigned_integral auto value) noexcept -> fixed_internal
  {
  return static_cast<fixed_internal>(static_cast<fixed_internal_unsigned>(value) << digits);
  }

template<std::integral value_type>
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto promote_type_to_signed(value_type value) noexcept
  {
  if constexpr(std::is_signed_v<value_type>)
    return value;
  else
    {
    using signed_type = typetraits::promote_to_signed_t<value_type>;
    return static_cast<signed_type>(value);
    }
  }

[[nodiscard, gnu::const, gnu::always_inline]]
///\returns the highest power of 4 that is less than or equal to \ref value
constexpr auto highest_pwr4_clz(concepts::internal_unsigned auto value) noexcept -> fixed_internal
  {
  if(value != 0) [[likely]]
    {
    int clz{std::countl_zero(value)};

    clz = (64 - clz);
    if((clz & 1) == 0)
      clz -= 1;

    return fixed_internal(1ll << (clz - 1));
    }
  return 0;
  }

[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto highest_pwr4(std::unsigned_integral auto value) noexcept -> fixed_internal
  {
  // one starts at the highest power of four <= than the argument.
  fixed_internal_unsigned pwr4{1ll << 62};  // second-to-top bit set

  while(pwr4 > value)
    pwr4 >>= 2;
  return fixed_internal(pwr4);
  }

template<int precision>
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto mul_(concepts::internal auto x, concepts::internal auto y) noexcept -> fixed_internal
  {
  return (x * y) >> precision;
  }

template<int precision>
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto div_(concepts::internal auto x, concepts::internal auto y) noexcept -> fixed_internal
  {
  return (x << precision) / y;
  }

template<int precision>
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto fix_(std::integral auto x) noexcept -> fixed_internal
  {
  return fixed_internal(x) << precision;
  }

[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto set_sign(bool sign_, concepts::internal auto result) -> fixed_t
  {
  if(!sign_)
    return as_fixed(result);
  return as_fixed(-result);
  }

template<concepts::arithmetic T>
constexpr void swap(T & a, T & b) noexcept
  {
  T temp = a;
  a = b;
  b = temp;
  }
  }  // namespace fixedmath::inline v2::detail

