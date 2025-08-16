// SPDX-FileCopyrightText: 2020-2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once

#include "types.h"
#include "limits.h"
#include "math.h"

namespace fixedmath::inline v2
  {
// representative fractions in fixed and any of sum of them
//  1      1<<0   0.0000152587890625
//  2      1<<1   0.0000305175781250
//  4      1<<2   0.0000610351562500
//  8      1<<3   0.0001220703125000
//  16     1<<4   0.0002441406250000
//  32     1<<5   0.0004882812500000
//  64     1<<6   0.0009765625000000
//  128    1<<7   0.0019531250000000
//  256    1<<8   0.0039062500000000
//  512    1<<9   0.0078125000000000
//  1024   1<<10  0.0156250000000000
//  2048   1<<11  0.0312500000000000
//  4096   1<<12  0.0625000000000000
//  8192   1<<13  0.1250000000000000
//  16384  1<<14  0.2500000000000000
//  32768  1<<15  0.5000000000000000

[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto operator>>(std::same_as<fixed_t> auto l, int r) noexcept -> fixed_t
  {
  return fobj::rshift(l, r);
  }

[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto operator<<(std::same_as<fixed_t> auto l, int r) noexcept -> fixed_t
  {
  return fobj::lshift(l, r);
  }

inline auto constexpr operator&(std::same_as<fixed_t> auto l, std::same_as<fixed_t> auto r) noexcept -> fixed_t
  {
  return fobj::bit_and(l, r);
  }

[[gnu::always_inline]]
constexpr auto operator+=(fixed_t & l, concepts::arithmetic auto r) noexcept -> fixed_t &
  {
  l = fobj::add(l, r);
  return l;
  }

///\brief returns result of addition of to arguments
///\note when one of arguments is double precission operation is promoted to double
template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
  requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto operator+(supported_type1 l, supported_type2 r) noexcept
  {
  return fobj::add(l, r);
  }

[[gnu::always_inline]]
inline constexpr auto operator-=(fixed_t & lh, concepts::arithmetic auto rh) noexcept -> fixed_t &
  {
  lh = fobj::subtract(lh, rh);
  return lh;
  }

template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
  requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto operator-(supported_type1 lh, supported_type2 rh) noexcept
  {
  return fobj::subtract(lh, rh);
  }

[[gnu::always_inline]]
constexpr auto operator*=(fixed_t & lh, concepts::arithmetic auto rh) noexcept -> fixed_t &
  {
  lh = fobj::multiply(lh, rh);
  return lh;
  }

template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
  requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto operator*(supported_type1 lh, supported_type2 rh) noexcept
  {
  return fobj::multiply(lh, rh);
  }

[[gnu::always_inline]]
constexpr auto operator/=(fixed_t & lh, concepts::arithmetic auto rh) noexcept -> fixed_t &
  {
  lh = fobj::division(lh, rh);
  return lh;
  }

template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
  requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto operator/(supported_type1 lh, supported_type2 rh) noexcept
  {
  return fobj::division(lh, rh);
  }

[[gnu::always_inline]]
constexpr auto operator%=(fixed_t & lh, concepts::arithmetic auto rh) noexcept -> fixed_t &
  {
  lh = fobj::fmod(lh, rh);
  return lh;
  }
  
template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
  requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto operator%(supported_type1 lh, supported_type2 rh) noexcept
  {
  return fobj::fmod(lh, rh);
  }
  
namespace func
  {
  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto abs(std::same_as<fixed_t> auto value) noexcept -> fixed_t
    {
    return fobj::abs(value);
    }

  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto isnan(std::same_as<fixed_t> auto value) noexcept -> bool
    {
    return fobj::isnan(value);
    }

  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto ceil(std::same_as<fixed_t> auto value) noexcept -> fixed_t
    {
    return fobj::ceil(value);
    }

  [[nodiscard, gnu::const, gnu::always_inline]]
  static constexpr auto floor(std::same_as<fixed_t> auto value) noexcept -> fixed_t
    {
    return fobj::floor(value);
    }

  template<std::integral integral_type>
  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto angle_to_radians(integral_type angle) noexcept -> fixed_t
    {
    return fobj::angle_to_radians(angle);
    }

  [[nodiscard]]
  constexpr auto sqrt(std::same_as<fixed_t> auto value) noexcept -> fixed_t
    {
    return fobj::sqrt(value);
    }

  [[nodiscard]]
  constexpr auto hypot(std::same_as<fixed_t> auto lh, std::same_as<fixed_t> auto rh) noexcept -> fixed_t
    {
    return fobj::hypot(lh, rh);
    }

  [[nodiscard, gnu::const]]
  constexpr auto sin(std::same_as<fixed_t> auto rad) noexcept -> fixed_t
    {
    return fobj::sin(rad);
    }

  [[nodiscard, gnu::const]]
  constexpr auto cos(std::same_as<fixed_t> auto rad) noexcept -> fixed_t
    {
    return fobj::cos(rad);
    }

  [[nodiscard, gnu::const]]
  constexpr auto tan(std::same_as<fixed_t> auto rad) noexcept -> fixed_t
    {
    return fobj::tan(rad);
    }

  [[nodiscard, gnu::const]]
  constexpr auto atan(std::same_as<fixed_t> auto value) noexcept -> fixed_t
    {
    return fobj::atan(value);
    }

  [[nodiscard, gnu::const]]
  constexpr auto atan2(std::same_as<fixed_t> auto y, std::same_as<fixed_t> auto x) noexcept -> fixed_t
    {
    return fobj::atan2(y, x);
    }

  [[nodiscard, gnu::const]]
  constexpr auto asin(std::same_as<fixed_t> auto x) noexcept -> fixed_t
    {
    return fobj::asin(x);
    }

  [[nodiscard, gnu::const]]
  constexpr auto acos(std::same_as<fixed_t> auto x) noexcept -> fixed_t
    {
    return fobj::acos(x);
    }

  [[nodiscard, gnu::const]]
  constexpr auto sin_angle(concepts::arithmetic auto angle) noexcept -> fixed_t
    {
    return fobj::sin_angle(angle);
    }

  [[nodiscard, gnu::const]]
  constexpr auto cos_angle(concepts::arithmetic auto angle) noexcept -> fixed_t
    {
    return fobj::cos_angle(angle);
    }

  [[nodiscard, gnu::const]]
  constexpr auto tan_angle(concepts::arithmetic auto angle) noexcept -> fixed_t
    {
    return fobj::tan_angle(angle);
    }
    
  template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
    requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto fmod(supported_type1 lh, supported_type2 rh) noexcept
    {
    return fobj::fmod(lh, rh);
    }
  }  // namespace func
  }  // namespace fixedmath::inline v2
