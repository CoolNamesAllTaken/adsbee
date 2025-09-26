// SPDX-FileCopyrightText: 2020-2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once

#include <cstdint>
#include <concepts>
#include <type_traits>
#include <limits>
#include <cmath>

namespace fixedmath::inline v2
  {
using fixed_internal = int64_t;
using fixed_internal_unsigned = uint64_t;

struct fix_carrier_t;
struct fixed_t;

  }  // namespace fixedmath::inline v2

namespace fixedmath::typetraits
  {
// clang-format off
template<int size> struct signed_type_by_size { };
// template<> struct signed_type_by_size<1> { using type = int8_t; };
template<> struct signed_type_by_size<2> { using type = int16_t; };
template<> struct signed_type_by_size<4> { using type = int32_t; };
template<> struct signed_type_by_size<8> { using type = int64_t; };
template<> struct signed_type_by_size<16>{ using type = int64_t; };

// clang-format on

template<std::size_t Size>
using signed_type_by_size_t = typename signed_type_by_size<Size>::type;

template<typename T>
using promote_to_signed_t = signed_type_by_size_t<(sizeof(T) << 1)>;

template<typename T>
inline constexpr bool is_integral_v = std::is_integral_v<T>;

template<typename T>
inline constexpr bool is_fixed_point_v = std::is_same_v<T, fixed_t>;

template<typename T>
inline constexpr bool is_signed_v = std::is_signed_v<T> || is_fixed_point_v<T>;

template<typename T>
inline constexpr bool is_unsigned_v = std::is_unsigned_v<T>;

template<typename T>
inline constexpr bool is_floating_point_v = std::is_floating_point_v<T> || is_fixed_point_v<T>;

template<typename T>
inline constexpr bool is_arithmetic_v = is_integral_v<T> || is_floating_point_v<T>;

template<typename T>
inline constexpr bool is_arithmetic_and_not_fixed_v = is_arithmetic_v<T> && (!is_fixed_point_v<T>);

template<typename T>
inline constexpr bool is_floating_point_and_not_fixed_v = std::is_floating_point_v<T>;

template<typename T, typename U>
inline constexpr bool is_arithmetic_and_one_is_fixed_v
  = is_arithmetic_v<T> && is_arithmetic_v<U> && (is_fixed_point_v<T> || is_fixed_point_v<U>);

template<typename T, typename U>
inline constexpr bool one_of_is_double_v = std::is_same_v<T, double> || std::is_same_v<U, double>;
  }  // namespace fixedmath::typetraits

namespace fixedmath::inline v2::concepts
  {
using std::integral;
template<typename T>
concept internal_unsigned = std::same_as<T, fixed_internal_unsigned>;

template<typename T>
concept internal = std::same_as<T, fixed_internal>;

template<typename T>
concept fixed_point = typetraits::is_fixed_point_v<T>;

template<typename T>
concept floating_point = typetraits::is_floating_point_v<T>;

template<typename T>
concept arithmetic = typetraits::is_arithmetic_v<T>;

template<typename T>
concept arithmetic_and_not_fixed = typetraits::is_arithmetic_and_not_fixed_v<T>;

template<typename T>
concept floating_point_and_not_fixed = typetraits::is_floating_point_and_not_fixed_v<T>;

template<typename T, typename U>
concept arithmetic_and_one_is_fixed = typetraits::is_arithmetic_and_one_is_fixed_v<T, U>;

template<typename T, typename U>
concept one_of_is_double = typetraits::one_of_is_double_v<T, U>;

  }  // namespace fixedmath::inline v2::concepts

namespace fixedmath::inline v2::detail
  {
using limits_ = std::numeric_limits<fixedmath::fixed_t>;
using flimits_ = std::numeric_limits<float>;
using dlimits_ = std::numeric_limits<double>;
  }  // namespace fixedmath::inline v2::detail
