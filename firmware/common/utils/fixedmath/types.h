// SPDX-FileCopyrightText: 2020-2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once

#include "detail/type_traits.h"

#include "detail/static_call_operator_prolog.h"

#define FIXEDMATH_VERSION_MAJOR 2
#define FIXEDMATH_VERSION_MINOR 2
#define FIXEDMATH_VERSION_PATCH 0
#define FIXEDMATH_VERSION_STRING "2.2.0"

namespace fixedmath::inline v2
  {
// the idea behind carrier is to use it as carier of internal int64 value in format of fixed to distinguish it from
// int64 integral type.
struct [[clang::trivial_abi]] fix_carrier_t
  {
  fixed_internal v{};

  constexpr fix_carrier_t() noexcept = default;

  explicit constexpr fix_carrier_t(std::same_as<fixed_internal> auto const & value) noexcept : v{value} {}
  };

///\brief hermetization of fixed value to avoid implicit conversions from int64, long long
struct [[clang::trivial_abi]] fixed_t
  {
  fixed_internal v{};

  template<concepts::arithmetic_and_not_fixed arithmethic_type>
  explicit constexpr operator arithmethic_type() const noexcept;

  constexpr fixed_t() noexcept = default;

  constexpr fixed_t(std::same_as<fix_carrier_t> auto value) noexcept : v{value.v} {}

  explicit constexpr fixed_t(concepts::arithmetic_and_not_fixed auto value) noexcept;
  };

struct as_fixed_t
  {
  static_call_operator constexpr auto operator()(std::same_as<fixed_internal> auto carried
  ) static_call_operator_const noexcept -> fixed_t
    {
    return fix_carrier_t{carried};
    }
  };

///\brief constructs fixed from raw value in internal format
inline constexpr as_fixed_t as_fixed;

[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto operator==(std::same_as<fixed_t> auto l, std::same_as<fixed_t> auto r) noexcept -> bool
  {
  return l.v == r.v;
  }

[[nodiscard, gnu::const, gnu::always_inline]]
constexpr auto operator<=>(std::same_as<fixed_t> auto l, std::same_as<fixed_t> auto r) noexcept
  {
  return l.v <=> r.v;
  }

  }  // namespace fixedmath::inline v2

#include "detail/static_call_operator_epilog.h"
