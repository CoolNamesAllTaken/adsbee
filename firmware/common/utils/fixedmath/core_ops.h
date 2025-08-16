// SPDX-FileCopyrightText: 2020-2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once
#include <cmath>
#include <utility>
#include "types.h"
#include "limits.h"
#include "numbers.h"
#include "detail/common.h"

#include "detail/static_call_operator_prolog.h"

namespace fixedmath::inline v2
  {
//------------------------------------------------------------------------------------------------------
[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto operator-(std::same_as<fixed_t> auto l) noexcept -> fixed_t
  {
  return fix_carrier_t{-l.v};
  }

//------------------------------------------------------------------------------------------------------

struct arithmetic_to_fixed_t
  {
  template<concepts::arithmetic_and_not_fixed arithmetic_type>
  [[nodiscard, gnu::const, gnu::always_inline]]
  ///\returns fixed on success or NaN if source value is out of range
  static_call_operator constexpr auto operator()(arithmetic_type value) static_call_operator_const noexcept -> fixed_t
    {
    if constexpr(std::is_integral_v<arithmetic_type>)
      {
      if(std::cmp_less_equal(value, detail::limits_::max_integral())
         && std::cmp_greater_equal(value, detail::limits_::min_integral())) [[likely]]
        {
        if constexpr(typetraits::is_unsigned_v<arithmetic_type>)
          return fix_carrier_t{detail::unsigned_shift_left_unsigned<16>(value)};
        else
          return fix_carrier_t{detail::unsigned_shift_left_signed<16>(value)};
        }
      return quiet_NaN_result();
      }
    else
      {
      using ft = arithmetic_type;
      if(value < double(detail::limits_::max_integral()) && value > double(detail::limits_::min_integral())) [[likely]]
        return fix_carrier_t(static_cast<fixed_internal>(value * 65536 + (value < ft(0) ? ft(-0.5) : ft(0.5))));

      return quiet_NaN_result();
      }
    }
  };

///\brief Converts an floating point or integral to a fixed_t type
inline constexpr arithmetic_to_fixed_t arithmetic_to_fixed{};

constexpr auto operator""_fix(unsigned long long value) noexcept -> fixed_t
  {
  return arithmetic_to_fixed(static_cast<int64_t>(value));
  }

constexpr auto operator""_fix(long double value) noexcept -> fixed_t
  {
  return arithmetic_to_fixed(static_cast<double>(value));
  }

template<concepts::arithmetic_and_not_fixed arithmethic_type>
constexpr fixed_t::fixed_t(arithmethic_type value) noexcept : v{arithmetic_to_fixed(value).v}
  {
  }

//------------------------------------------------------------------------------------------------------

template<concepts::arithmetic_and_not_fixed arithmethic_type>
struct fixed_to_arithmetic_t
  {
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto value
  ) static_call_operator_const noexcept -> arithmethic_type
    {
    if constexpr(typetraits::is_integral_v<arithmethic_type>)
      {
      fixed_internal tmp{(value.v >> 16) /*+ (( value.v & 0x8000) >> 15)*/};
      using al = std::numeric_limits<arithmethic_type>;
      static constexpr auto integral_min{al::min()};
      static constexpr auto integral_max{al::max()};
      if(std::cmp_greater_equal(tmp, integral_min) && std::cmp_less_equal(tmp, integral_max))
        return static_cast<arithmethic_type>(tmp);
      else
        return std::numeric_limits<arithmethic_type>::quiet_NaN();
      }
    else
      return static_cast<arithmethic_type>(value.v) / arithmethic_type(65536);
    }
  };

///\brief Converts an fixed_t point value to an integral or floating point value.
template<concepts::arithmetic_and_not_fixed arithmethic_type>
inline constexpr fixed_to_arithmetic_t<arithmethic_type> fixed_to_arithmetic{};

template<concepts::arithmetic_and_not_fixed arithmethic_type>
[[nodiscard]]
constexpr fixed_t::operator arithmethic_type() const noexcept
  {
  return fixed_to_arithmetic<arithmethic_type>(*this);
  }

  }  // namespace fixedmath::inline v2

#include "detail/static_call_operator_epilog.h"
