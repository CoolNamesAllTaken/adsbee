// SPDX-FileCopyrightText: 2020-2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once

#include <cmath>
#include "core_ops.h"
#include <algorithm>

#include "detail/static_call_operator_prolog.h"

namespace fixedmath::inline v2::detail
  {

template<concepts::arithmetic supported_type>
[[nodiscard, gnu::const, gnu::always_inline]]
inline constexpr double promote_to_double(supported_type value) noexcept
  {
  if constexpr(std::same_as<double, supported_type>)
    return value;
  else
    return fixed_to_arithmetic<double>(value);
  }

template<concepts::arithmetic supported_type>
[[nodiscard, gnu::const, gnu::always_inline]]
inline constexpr fixed_t promote_to_fixed(supported_type value) noexcept
  {
  if constexpr(std::same_as<fixed_t, supported_type>)
    return value;
  else
    return arithmetic_to_fixed(value);
  }
  }  // namespace fixedmath::inline v2::detail

namespace fixedmath::inline v2::fobj
  {
namespace detail
  {
  using namespace fixedmath::detail;
  }

//------------------------------------------------------------------------------------------------------
struct abs_t
  {
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto value) static_call_operator_const noexcept
    -> fixed_t
    {
    // cmp     x0, #0                          // =0
    // cneg    x0, x0, mi
    return as_fixed(value.v > 0 ? value.v : -value.v);
    }
  };

inline constexpr abs_t abs;

//------------------------------------------------------------------------------------------------------

struct isnan_t
  {
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto value) static_call_operator_const noexcept
    -> bool
    {
    return abs(value) == quiet_NaN_result();
    }
  };

inline constexpr isnan_t isnan;

//------------------------------------------------------------------------------------------------------

struct rshift_t
  {
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto
    operator()(std::same_as<fixed_t> auto l, int r) static_call_operator_const noexcept -> fixed_t
    {
    if(r >= 0) [[likely]]
      return fix_carrier_t{l.v >> r};
    return quiet_NaN_result();
    }
  };

inline constexpr rshift_t rshift;

//------------------------------------------------------------------------------------------------------

struct lshift_t
  {
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto
    operator()(std::same_as<fixed_t> auto l, int r) static_call_operator_const noexcept -> fixed_t
    {
    using unsigned_fix_internal = std::make_unsigned<fixed_internal>::type;

    if(r >= 0) [[likely]]
      return fix_carrier_t{fixed_internal(
        (((unsigned_fix_internal(l.v)) << r)
         & unsigned_fix_internal(0x7fffffffffffffffull))  // lsh unsigned value and clear overwritten sign bit
        | ((1ull << 63) & unsigned_fix_internal(l.v))     // transfer source sign bit
      )};
    return quiet_NaN_result();
    }
  };

inline constexpr lshift_t lshift;

//------------------------------------------------------------------------------------------------------

struct bit_and_t
  {
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator inline constexpr auto
    operator()(std::same_as<fixed_t> auto l, std::same_as<fixed_t> auto r) static_call_operator_const noexcept
    -> fixed_t
    {
    return fix_carrier_t{l.v & r.v};
    }
  };

inline constexpr bit_and_t bit_and;

//------------------------------------------------------------------------------------------------------

namespace detail
  {
  ///\brief Returns the sum of two fixed_t point values.
  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto fixed_additioni(std::same_as<fixed_t> auto lh, std::same_as<fixed_t> auto rh) noexcept -> fixed_t
    {
    fixed_t result{fix_carrier_t{lh.v + rh.v}};
    if(result >= 0_fix) [[unlikely]]
      {
      if((lh < 0_fix) && (rh < 0_fix)) [[unlikely]]
        return -quiet_NaN_result();
      }
    else
      {
      if((lh > 0_fix) && (rh > 0_fix)) [[unlikely]]
        return quiet_NaN_result();
      }
    return result;
    }

  }  // namespace detail

struct add_t
  {
  ///\brief returns result of addition of to arguments
  ///\note when one of arguments is double precision operation is promoted to double
  template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
    requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto
    operator()(supported_type1 lh, supported_type2 rh) static_call_operator_const noexcept
    {
    if constexpr(typetraits::one_of_is_double_v<supported_type1, supported_type2>)
      return detail::promote_to_double(rh) + detail::promote_to_double(lh);
    else
      return detail::fixed_additioni(detail::promote_to_fixed(lh), detail::promote_to_fixed(rh));
    }
  };

inline constexpr add_t add;

//------------------------------------------------------------------------------------------------------

namespace detail
  {
  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto fixed_subtracti(std::same_as<fixed_t> auto lh, std::same_as<fixed_t> auto rh) noexcept -> fixed_t
    {
    fixed_t result{fix_carrier_t{lh.v - rh.v}};

    if(result >= 0_fix)
      {
      if((lh < 0_fix) && (rh > 0_fix)) [[unlikely]]
        return -quiet_NaN_result();
      }
    else
      {
      if((lh > 0_fix) && (rh < 0_fix)) [[unlikely]]
        return quiet_NaN_result();
      }

    return result;
    }

  }  // namespace detail

struct subtract_t
  {
  ///\brief returns result of addition of to arguments
  ///\note when one of arguments is double precission operation is promoted to double
  template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
    requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto
    operator()(supported_type1 lh, supported_type2 rh) static_call_operator_const noexcept
    {
    if constexpr(typetraits::one_of_is_double_v<supported_type1, supported_type2>)
      return detail::promote_to_double(lh) - detail::promote_to_double(rh);
    else
      return detail::fixed_subtracti(detail::promote_to_fixed(lh), detail::promote_to_fixed(rh));
    }
  };

inline constexpr subtract_t subtract;

//------------------------------------------------------------------------------------------------------
/// \brief Returns the product of two fixed_t point values.

namespace detail
  {
  constexpr bool check_multiply_result(std::same_as<fixed_t> auto result)
    {
    return (
      result < as_fixed(fixed_internal(0x7fffffffffff0000ll))
      || result > as_fixed(fixed_internal(-0x7fffffffffff0000ll))
    );
    }

  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto fixed_multiplyi(std::same_as<fixed_t> auto lh, std::same_as<fixed_t> auto rh) noexcept -> fixed_t
    {
    fixed_t result{fix_carrier_t{lh.v * rh.v}};

    if(check_multiply_result(result)) [[likely]]
      return fix_carrier_t{result.v >> 16};

    return quiet_NaN_result();
    }

  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto fixed_multiply_scalar(std::same_as<fixed_t> auto lh, std::integral auto rh) noexcept -> fixed_t
    {
    fixed_t result{fix_carrier_t{lh.v * promote_type_to_signed(rh)}};

    if(check_multiply_result(result)) [[likely]]
      return result;
    return quiet_NaN_result();
    }

  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto fixed_multiply_scalar(std::integral auto lh, std::same_as<fixed_t> auto rh) noexcept -> fixed_t
    {
    return fixed_multiply_scalar(rh, lh);
    }
  }  // namespace detail

struct multiply_t
  {
  ///\brief returns result of addition of to arguments
  ///\note when one of arguments is double precission operation is promoted to double
  template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
    requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto
    operator()(supported_type1 lh, supported_type2 rh) static_call_operator_const noexcept
    {
    if constexpr(typetraits::one_of_is_double_v<supported_type1, supported_type2>)
      return detail::promote_to_double(lh) * detail::promote_to_double(rh);
    else if constexpr(std::is_integral_v<supported_type1> || std::is_integral_v<supported_type2>)
      return detail::fixed_multiply_scalar(lh, rh);
    else
      return detail::fixed_multiplyi(detail::promote_to_fixed(lh), detail::promote_to_fixed(rh));
    }
  };

inline constexpr multiply_t multiply;

//------------------------------------------------------------------------------------------------------

namespace detail
  {
  constexpr bool check_division_result(std::same_as<fixed_t> auto result)
    {
    return result <= as_fixed(fixed_internal(0x7fffffffffffll))
           && result >= as_fixed(fixed_internal(-0x7fffffffffffll));
    }

  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto fixed_divisionf(std::same_as<fixed_t> auto x, std::same_as<fixed_t> auto y) noexcept -> fixed_t
    {
    if(y.v != 0) [[likely]]
      {
      fixed_t result{as_fixed((x << 16).v / y.v)};
      return result;
      }
    return quiet_NaN_result();  // abort ?
    }

  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto fixed_division_by_scalar(std::same_as<fixed_t> auto lh, std::integral auto rh) noexcept -> fixed_t
    {
    if(rh != 0) [[likely]]
      {
      fixed_t const result = as_fixed(lh.v / detail::promote_type_to_signed(rh));
      return result;
      }
    return quiet_NaN_result();  // abort ?
    }
  }  // namespace detail

struct division_t
  {
  template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
    requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto
    operator()(supported_type1 lh, supported_type2 rh) static_call_operator_const noexcept
    {
    if constexpr(std::is_integral_v<supported_type2>)
      return detail::fixed_division_by_scalar(lh, rh);
    else if constexpr(typetraits::one_of_is_double_v<supported_type1, supported_type2>)
      return detail::promote_to_double(lh) / detail::promote_to_double(rh);
    else
      return detail::fixed_divisionf(detail::promote_to_fixed(lh), detail::promote_to_fixed(rh));
    }
  };

inline constexpr division_t division;

//------------------------------------------------------------------------------------------------------
namespace detail
  {

  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto fixed_modulof(std::same_as<fixed_t> auto x, std::same_as<fixed_t> auto y) noexcept -> fixed_t
    {
    if(y.v != 0) [[likely]]
      {
      fixed_t result{as_fixed(x.v % y.v)};
      return result;
      }
    return quiet_NaN_result();  // abort ?
    }
  }  // namespace detail

struct modulo_t
  {
  template<concepts::arithmetic supported_type1, concepts::arithmetic supported_type2>
    requires concepts::arithmetic_and_one_is_fixed<supported_type1, supported_type2>
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto
    operator()(supported_type1 lh, supported_type2 rh) static_call_operator_const noexcept
    {
    if constexpr(typetraits::one_of_is_double_v<supported_type1, supported_type2>)
      return std::fmod(detail::promote_to_double(lh),detail::promote_to_double(rh));
    else
      return detail::fixed_modulof(detail::promote_to_fixed(lh), detail::promote_to_fixed(rh));
    }
  };

inline constexpr modulo_t fmod;

//------------------------------------------------------------------------------------------------------

struct ceil_t
  {
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto value) static_call_operator_const noexcept
    -> fixed_t
    {
    fixed_internal result{(value.v + 0xffff) & ~((1 << 16ll) - 1)};
    if(value.v < result)
      return as_fixed(result);
    return quiet_NaN_result();
    }
  };

inline constexpr ceil_t ceil;

//------------------------------------------------------------------------------------------------------

struct floor_t
  {
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto value) static_call_operator_const noexcept
    -> fixed_t
    {
    value = as_fixed(value.v & ~((1 << 16) - 1));
    return value;
    }
  };

inline constexpr floor_t floor;

//------------------------------------------------------------------------------------------------------

struct angle_to_radians_t
  {
  ///\brief converts angle 0 - 360 to radians.
  template<std::integral integral_type>
    requires(sizeof(integral_type) > 1)
  [[nodiscard, gnu::const, gnu::always_inline]]
  static_call_operator constexpr auto operator()(integral_type angle) static_call_operator_const noexcept -> fixed_t
    {
    if(angle >= integral_type(0) && angle <= integral_type(360))
      return division(multiply(arithmetic_to_fixed(angle), fixedmath::phi), 180);
    return quiet_NaN_result();
    }
  };

inline constexpr angle_to_radians_t angle_to_radians;

//------------------------------------------------------------------------------------------------------

namespace detail
  {
  ///\brief Square root by abacus algorithm
  [[nodiscard, gnu::const]]
  constexpr auto sqrt_abacus(fixed_t value) noexcept -> fixed_t
    {
    if(value.v < 0 || value.v >= (1ll << 48)) [[unlikely]]
      return std::numeric_limits<fixed_t>::quiet_NaN();

    value.v <<= 16;

    fixed_internal pwr4{detail::highest_pwr4_clz(fixed_internal_unsigned(value.v))};

    fixed_internal result{};
    while(pwr4 != 0)
      {
      if(value.v >= (result + pwr4))
        {
        value.v -= result + pwr4;
        result += pwr4 << 1;
        }
      result >>= 1;
      pwr4 >>= 2;
      }
    return as_fixed(result);
    }
  }  // namespace detail

inline constexpr bool sqrt_constexpr_available = true;

struct sqrt_t
  {
  [[nodiscard]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto value) static_call_operator_const noexcept
    -> fixed_t
    {
    if(std::is_constant_evaluated())
      return detail::sqrt_abacus(value);
    else
      return arithmetic_to_fixed(std::sqrt(fixed_to_arithmetic<double>(value)));
    }
  };

inline constexpr sqrt_t sqrt;

//------------------------------------------------------------------------------------------------------

struct hypot_t
  {
  [[nodiscard]]
  static_call_operator constexpr auto
    operator()(std::same_as<fixed_t> auto lh, std::same_as<fixed_t> auto rh) static_call_operator_const noexcept
    -> fixed_t
    {
    constexpr int prec_ = 16;
    // sqrt(X^2+Y^2) = sqrt( (X/D)^2+(Y/D)^2) * D
    // D = 2^n
    if(lh < 0_fix)
      lh = -lh;
    if(rh < 0_fix)
      rh = -rh;
    uint64_t uhi{static_cast<uint64_t>(lh.v)};
    uint64_t ulo{static_cast<uint64_t>(rh.v)};

    // reorder hi/lo
    if(uhi < ulo)
      detail::swap(uhi, ulo);

    if(uhi == 0) [[unlikely]]
      return 0_fix;
    // check hi for overflow and shift right with d
    else if(uhi >= (1ull << 30))
      {
      int rshbits{48 - std::countl_zero(uhi)};
      uhi >>= rshbits;
      ulo >>= rshbits;
      return as_fixed(sqrt(as_fixed(fixed_internal(uhi * uhi + ulo * ulo) >> prec_)).v << rshbits);
      }
    // else check lo for underflow and shift left with d
    else if(ulo < (1 << 16))
      {
      int lshbits{std::max(std::countl_zero(uhi) - 30, 0) >> 1};
      uhi <<= lshbits;
      ulo <<= lshbits;
      return as_fixed(sqrt(as_fixed(fixed_internal(uhi * uhi + ulo * ulo) >> prec_)).v >> lshbits);
      }
    else
      return sqrt(as_fixed(fixed_internal(uhi * uhi + ulo * ulo) >> prec_));
    }
  };

inline constexpr hypot_t hypot;

//------------------------------------------------------------------------------------------------------
// for trigonometric functions maclurin taylor series are used
// https://en.wikipedia.org/wiki/Taylor_series
namespace detail
  {
  ///\return \ref rad normalized into range -phi/2 .. 3phi/2
  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto sin_range(std::same_as<fixed_t> auto rad) noexcept -> fixed_t
    {
    // maximum performance for values in range thus fixed_unlikely
    if(rad < -fixpidiv2 || rad > add(phi, fixpidiv2)) [[unlikely]]
      {
      rad = as_fixed((fixpidiv2.v + rad.v) % fixpi2.v - fixpidiv2.v);
      if(rad < -fixpidiv2) [[unlikely]]
        rad = as_fixed(rad.v + fixpi2.v);
      }
    return rad;
    }
  }  // namespace detail

struct sin_t
  {
  ///\return sine of value in radians
  /// Y = X - X^3/ 3! + X^5/ 5! - ... + (-1)^(n+1) * X^(2*n-1)/(2n-1)!
  /// X - X^3/ 3! + X^5/ 5! - X^7/7!
  /// X - X^3/6 + x^3*x^2/(6*20) - x^3*x^2*x^2/(6*20*42)
  ///
  /// let X2 = X*X
  /// X * (1 - X2*(1 - X2*(1 - X2/42)/20)/6)
  ///
  /// error is less or equal to X^9/9!
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto rad) static_call_operator_const noexcept
    -> fixed_t
    {
    using detail::mul_;
    rad = detail::sin_range(rad);

    // on arm64 condition is compiled as  subtraction with csel instruction without jump
    //         mov     w9, #9279
    //         movk    w9, #3, lsl #16
    //         cmp     x0, x8
    //         sub     x9, x9, x0
    //         csel    x9, x9, x0, gt
    if(rad > fixpidiv2) [[unlikely]]
      rad = phi - rad;  // inverse of phi/2 .. -phi/2

    // aprox valid for -phi/2 .. phi/2
    static constexpr int prec_ = 16;
    fixed_internal x{rad.v};
    fixed_internal x2{mul_<prec_>(x, x)};
    // reduce number of divisions
    /*
    { x left ( { 1 - x ^ 2 left ( { 1 - x ^ 2 left ( { 1 - x ^ 2 cdot { 1 over 42 } } right ) cdot { 1 over 20 } }
    right ) { 1 over 6 } } right ) } { x left ( { 1 - x ^ 2 left ( { 1 - x ^ 2 left ( { 1 - x ^ 2 cdot { 1 over 2 } {
    1 over 21 } } right ) cdot { 1 over 4 } cdot { 1 over 5 } } right ) { 1 over 2 } cdot { 1 over 3 } } right ) } { x
    left ( { 1 - x ^ 2 left ( { 1 - x ^ 2 { 1 over 21 } left ( { 21 - x ^ 2 cdot { 1 over 2 } } right ) cdot { 1 over
    4 } cdot { 1 over 5 } } right ) { 1 over 2 } cdot { 1 over 3 } } right ) } { x left ( { 1 - x ^ 2 left ( { 1 - x ^
    2 { 1 over { 5 cdot 21 } } left ( { 21 - x ^ 2 cdot { 1 over 2 } } right ) cdot { 1 over 4 } } right ) { 1 over 2
    } cdot { 1 over 3 } } right ) } { x left ( { 1 - x ^ 2 { 1 over { 3 cdot 5 cdot 21 } } left ( { 5 cdot 21 - x ^ 2
    left ( { 21 - x ^ 2 cdot { 1 over 2 } } right ) cdot { 1 over 4 } } right ) { 1 over 2 } } right ) } { x left ( {
    3 cdot 5 cdot 21 - x ^ 2 left ( { 5 cdot 21 - x ^ 2 left ( { 21 - x ^ 2 cdot { 1 over 2 } } right ) cdot { 1 over
    4 } } right ) { 1 over 2 } } right ) { 1 over { 3 cdot 5 cdot 21 } } } { x left ( { 315 - x ^ 2 left ( { 105 - x ^
    2 left ( { 21 - x ^ 2 cdot { 1 over 2 } } right ) cdot { 1 over 4 } } right ) { 1 over 2 } } right ) :315 } { x
    left ( { 315 - x ^ 2 left ( { 105 - x ^ 2 left ( { 42 - x ^ 2 } right ) cdot { 1 over 8 } } right ) { 1 over 2 } }
    right ) :315 }
    */
    static constexpr fixed_internal _42{fixed_internal{42} << prec_};
    static constexpr fixed_internal _105{fixed_internal{105} << (prec_ + prec_ + 3)};
    static constexpr fixed_internal _315{fixed_internal{315} << prec_};
    fixed_internal result{mul_<prec_>(x, _315 - mul_<prec_ + 1 + prec_ + 3>(x2, _105 - x2 * (_42 - x2))) / 315};
    return as_fixed(result);
    }
  };

inline constexpr sin_t sin;

//------------------------------------------------------------------------------------------------------
struct cos_t
  {
  ///\returns cosine of value in radians
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto rad) static_call_operator_const noexcept
    -> fixed_t
    {
    // more effective to use sine than calculate maclurin series for cosine
    // as maclurin series give precise results for -pi/2 .. pi/2
    return sin(add(fixpidiv2, rad));
    }
  };

inline constexpr cos_t cos;

//------------------------------------------------------------------------------------------------------
// tan
// Bernoulli number B 2*n
// 1 1/6
// 2 -1/30
// 3 1/42
// 4 -1/30
// 5 5/66
// 6 -691/2730
// 7 7/6
// 8 -3617/510
// 9 43867/798
namespace detail
  {
  // { { 1 over 6 } { { left ( - 4 right ) ^ 1 left ( 1 - 4 ^ 1 right ) } over fact left ( 2 right ) } x + { - 1 over
  // 30 } { { left ( - 4 right ) ^ 2 left ( 1 - 4 ^ 2 right ) } over fact left ( 2 cdot 2 right ) } x ^ left ( 2 cdot
  // 2 - 1 right ) + { 1 over 42 } { { left ( - 4 right ) ^ 3 left ( 1 - 4 ^ 3 right ) } over fact left ( 2 cdot 3
  // right ) } x ^ left ( 2 cdot 3 - 1 right ) + { - 1 over 30 } cdot { { left ( - 4 right ) ^ 4 left ( 1 - 4 ^ 4
  // right ) } over fact left ( 2 cdot 4 right ) } x ^ left ( { 2 cdot 4 - 1 } right ) + { 5 over 66 } cdot { { left (
  // - 4 right ) ^ 5 left ( 1 - 4 ^ 5 right ) } over fact left ( 2 cdot 5 right ) } x ^ left ( { 2 cdot 5 - 1 } right
  // ) + { - 691 over 2730 } cdot { { left ( - 4 right ) ^ 6 left ( 1 - 4 ^ 6 right ) } over fact left ( 2 cdot 6
  // right ) } x ^ left ( { 2 cdot 6 - 1 } right ) + { 7 over 6 } { { left ( - 4 right ) ^ 7 left ( 1 - 4 ^ 7 right )
  // } over fact left ( 2 cdot 7 right ) } x ^ left ( { 2 cdot 7 - 1 } right ) + { - 3617 over 510 } { { left ( - 4
  // right ) ^ 8 left ( 1 - 4 ^ 8 right ) } over fact left ( 2 cdot 8 right ) } x ^ left ( { 2 cdot 8 - 1 } right ) }

  // { x + { 1 over 3 } x ^ 3 + { 2 over 15 } x ^ 5 + { 17 over 315 } x ^ 7 + { 62 over 2835 } x ^ 9 + { 1382 over
  // 155925 } x ^ 11 + { 21844 over 6081075 } x ^ 13 + { 929569 over 638512875 } x ^ 15 } { x left ( { 1 + { 1 over 3
  // } x ^ 2 + { 2 over 15 } x ^ 4 + { 17 over 315 } x ^ 6 + { 62 over 2835 } x ^ 8 + { 1382 over 155925 } x ^ 10 + {
  // 21844 over 6081075 } x ^ 12 + { 929569 over 638512875 } x ^ 14 } right ) } { x left ( { 1 + { 1 over 3 } x ^ 2
  // left ( { 1 + { 2 over 5 } x ^ 2 + { 17 over 105 } x ^ 4 + { 62 over 945 } x ^ 6 + { 1382 over 51975 } x ^ 8 + {
  // 21844 over 2027025 } x ^ 10 + { 929569 over 212837625 } x ^ 12 } right ) } right ) } { x left ( { 1 + { 1 over 3
  // } x ^ 2 left ( { 1 + { 1 over 5 } x ^ 2 left ( { 2 + { 17 over 21 } x ^ 2 + { 62 over 189 } x ^ 4 + { 1382 over
  // 10395 } x ^ 6 + { 21844 over 405405 } x ^ 8 + { 929569 over 42567525 } x ^ 10 } right ) } right ) } right ) } { x
  // left ( { 1 + { 1 over 3 } x ^ 2 left ( { 1 + { 1 over 5 } x ^ 2 left ( { 2 + { 1 over 21 } x ^ 2 left ( { 17 + {
  // 62 over 9 } x ^ 2 + { 1382 over 495 } x ^ 4 + { 21844 over 19305 } x ^ 6 + { 929569 over 2027025 } x ^ 8 } right
  // ) } right ) } right ) } right ) } { x left ( { 1 + { 1 over 3 } x ^ 2 left ( { 1 + { 1 over 5 } x ^ 2 left ( { 2
  // + { 1 over 21 } x ^ 2 left ( { 17 + { 1 over 9 } x ^ 2 left ( { 62 + { 1382 over 55 } x ^ 2 + { 21844 over 2145 }
  // x ^ 4 + { 929569 over 225225 } x ^ 6 } right ) } right ) } right ) } right ) } right ) } { x left ( { 1 + { 1
  // over 3 } x ^ 2 left ( { 1 + { 1 over 5 } x ^ 2 left ( { 2 + { 1 over 21 } x ^ 2 left ( { 17 + { 1 over 9 } x ^ 2
  // left ( { 62 + { 1 over 55 } x ^ 2 left ( { 1382 + { 21844 over 39 } x ^ 2 + { 929569 over 4095 } x ^ 4 } right )
  // } right ) } right ) } right ) } right ) } right ) } { x left ( { 1 + { 1 over 3 } x ^ 2 left ( { 1 + { 1 over 5 }
  // x ^ 2 left ( { 2 + { 1 over 21 } x ^ 2 left ( { 17 + { 1 over 9 } x ^ 2 left ( { 62 + { 1 over 55 } x ^ 2 left (
  // { 1382 + { 1 over 39 } x ^ 2 left ( { 21844 + { 929569 over 105 } x ^ 4 } right ) } right ) } right ) } right ) }
  // right ) } right ) } right ) } { x left ( { 1 + x ^ 2 left ( { 1 + x ^ 2 left ( { 2 + x ^ 2 left ( { 17 + x ^ 2
  // left ( { 62 + x ^ 2 left ( { 1382 + x ^ 2 left ( { 21844 + { 929569 over 105 } x ^ 4 } right ) :39 } right ) :55
  // } right ) :9 } right ) :21 } right ) :5 } right ) :3 } right ) }
  template<int prec_>
  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto tan_(fixed_internal x) noexcept -> fixed_internal
    {
    fixed_internal x2{mul_<prec_>(x, x)};

    fixed_internal y0_{fix_<prec_>(21844) + 929569 * x2 / 105};
    fixed_internal y1_{fix_<prec_>(1382) + mul_<prec_>(x2, y0_) / 39};
    fixed_internal y2_{fix_<prec_>(62) + mul_<prec_>(x2, y1_) / 55};
    fixed_internal y3_{fix_<prec_>(17) + mul_<prec_>(x2, y2_) / 9};
    fixed_internal y4_{fix_<prec_>(2) + mul_<prec_>(x2, y3_) / 21};
    fixed_internal y5_{fix_<prec_>(1) + mul_<prec_>(x2, y4_) / 5};
    fixed_internal y6_{fix_<prec_>(1) + mul_<prec_>(x2, y5_) / 3};
    fixed_internal res{mul_<prec_>(x, y6_)};
    return res;
    }

  template<int prec_, fixed_internal a, fixed_internal tan_a>
  [[nodiscard, gnu::const]]
  constexpr auto tan2_(fixed_internal b) -> fixed_internal
    {
    constexpr fixed_internal one_{fix_<prec_>(1)};
    b = b - a;
    fixed_internal tan_b{tan_<prec_>(b)};
    return div_<prec_>(tan_a + tan_b, one_ - mul_<prec_>(tan_a, tan_b));
    }

  [[nodiscard, gnu::const, gnu::always_inline]]
  constexpr auto tan_range(fixed_internal x) noexcept -> fixed_internal
    {
    // maximum performance for values in range thus fixed_unlikely
    if(x > fixpidiv2.v) [[unlikely]]
      x = x % phi.v;

    return x;
    }
  }  // namespace detail

struct tan_t
  {
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto rad) static_call_operator_const noexcept
    -> fixed_t
    {
    using detail::div_;
    using detail::tan_;

    static constexpr int prec_ = 16;
    static constexpr int prec_inc = 4;
    static constexpr fixed_internal one_{detail::fix_<prec_>(1)};
    // tan(a+b) = (tan(a) + tan(b)) / (1 - tan(a) tan(b))
    fixed_internal x{rad.v};
    bool sign_{};
    if(x < 0)
      {
      x = -x;
      sign_ = true;
      }
    // normalize the range to phi/2
    x = detail::tan_range(x);

    if(x != fixpidiv2.v) [[likely]]
      {
      fixed_internal res_tan{};
      if(x <= fixpidiv4.v)
        res_tan = tan_<prec_ + prec_inc>(x << prec_inc) >> prec_inc;
      else
        res_tan = div_<prec_>(one_, tan_<prec_ + prec_inc>((fixpidiv2.v << prec_inc) - (x << prec_inc)) >> prec_inc);
      if(sign_)
        res_tan = -res_tan;
      return as_fixed(res_tan);
      }
    else
      return quiet_NaN_result();
    }
  };

inline constexpr tan_t tan;

//------------------------------------------------------------------------------------------------------
// atan
// Y = X - X^3/3 + X^5/5 - X^7/7 + X^9/9 -X^11/11
//  { x - { x ^ 3 over 3 } + { x ^ 5 over 5 } - { x ^ 7 over 7 } + { x ^ 9 over 9 } - { x ^ 11 over 11 } }
// { { 1 over 11 } x left ( { 11 + x ^ 2 left ( { - { 11 over 3 } + x ^ 2 left ( { { 11 over 5 } + x ^ 2 left ( { - {
// 11 over 7 } + x ^ 2 left ( { { 11 over 9 } - x ^ 2 } right ) } right ) } right ) } right ) } right ) }
namespace detail
  {
  // t=x*x
  // 1/11*x(11+t(-11/3+t(11/5+t(-11/7+t(11/9-t)))))
  template<int prec_>
  constexpr auto atan(fixed_internal x) noexcept -> fixed_internal
    {
    fixed_internal const t{mul_<prec_>(x, x)};
    static constexpr fixed_internal _11o9{fix_<prec_>(11) / 9};
    static constexpr fixed_internal _11o7{fix_<prec_>(11) / 7};
    static constexpr fixed_internal _11o5{fix_<prec_>(11) / 5};
    static constexpr fixed_internal _11o3{fix_<prec_>(11) / 3};
    static constexpr fixed_internal _11{fix_<prec_>(11)};

    fixed_internal y{_11o9 - t};
    y = -_11o7 + mul_<prec_>(t, y);
    y = _11o5 + mul_<prec_>(t, y);
    y = -_11o3 + mul_<prec_>(t, y);
    y = _11 + mul_<prec_>(t, y);
    return mul_<prec_>(x, y) / 11;
    }

  // arctan (x) = arctan(c) + arctan((x - c) / (1 + x*c))
  template<int prec_, fixed_internal atanc, fixed_internal c>
  constexpr auto atan_sum(fixed_internal x) -> fixed_internal
    {
    static constexpr fixed_internal one_{fix_<prec_>(1)};
    return atanc + atan<prec_>(div_<prec_>(x - c, one_ + mul_<prec_>(x, c)));
    }
  }  // namespace detail

struct atan_t
  {
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto value) static_call_operator_const noexcept
    -> fixed_t
    {
    using detail::atan;
    using detail::atan_sum;
    //     arctan (-x) = -arctan(x)
    //     arctan (1/x) = 0.5 * pi - arctan(x) [x > 0]
    //     arctan (x) = arctan(c) + arctan((x - c) / (1 + x*c))
    //     arctan(x)' = 1/ (1+x^2)
    static constexpr int prec_ = 16;

    static constexpr fixed_internal _7o16{28672};      // 7/16
    static constexpr fixed_internal atan_7o16{27028};  // 27027,7307005264

    static constexpr fixed_internal _11o16{45056};      // 11/16
    static constexpr fixed_internal atan_11o16{39472};  // 39471,503516301

    static constexpr fixed_internal _19o16{77824};      // 19/16
    static constexpr fixed_internal atan_19o16{57076};  // 57075,52896291

    static constexpr fixed_internal _39o16{159744};     // 19/16
    static constexpr fixed_internal atan_39o16{77429};  // 77429,4473907736

    fixed_internal x{value.v};
    bool sign_{};
    if(x < 0)
      {
      x = -x;
      sign_ = true;
      }
    fixed_internal result{};
    if(x < _7o16)
      result = atan<prec_>(x);
    else if(x < _11o16)
      result = atan_sum<prec_, atan_7o16, _7o16>(x);
    else if(x < _19o16)
      result = atan_sum<prec_, atan_11o16, _11o16>(x);
    else if(x < _39o16)
      result = atan_sum<prec_, atan_19o16, _19o16>(x);
    else
      result = atan_sum<prec_, atan_39o16, _39o16>(x);

    if(!sign_)
      return as_fixed(result);
    return as_fixed(-result);
    }
  };

inline constexpr atan_t atan;

struct atan2_t
  {
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto
    operator()(std::same_as<fixed_t> auto y, std::same_as<fixed_t> auto x) static_call_operator_const noexcept
    -> fixed_t
    {
    if(x > 0_fix)
      return atan(y / x);
    else if(x < 0_fix)
      if(y >= 0_fix)
        return atan(y / x) + phi;
      else  // y < 0
        return atan(y / x) - phi;
    else  // x ==0
      if(y > 0_fix)
        return fixpidiv2;
      else if(y < 0_fix)
        return -fixpidiv2;
      else
        return quiet_NaN_result();
    }
  };

inline constexpr atan2_t atan2;

namespace detail
  {
  // { x + { 1 over 6 } x ^ 3 + { 3 over 40 } x ^ 5 + { 5 over 112 } x ^ 7 + { 35 over 1152 } x ^ 9 + { 63 over 2816 }
  // x ^ 11 } { x left ( { 1 + { 1 over 6 } x ^ 2 + { 3 over 40 } x ^ 4 + { 5 over 112 } x ^ 6 + { 35 over 1152 } x ^
  // 8 + { 63 over 2816 } x ^ 10 } right ) } { x left ( { 1 + { 1 over 6 } x ^ 2 + { 3 over 40 } x ^ 4 + { 5 over 112
  // } x ^ 6 + { 7 over 128 } x ^ 8 left ( { { 5 over 9 } + { 9 over 22 } x ^ 2 } right ) } right ) } { x left ( { 1 +
  // { 1 over 6 } x ^ 2 + { 3 over 40 } x ^ 4 + { 5 over 112 } x ^ 6 + { 7 over 99 } { 1 over 256 } x ^ 8 left ( { 110
  // + 81 x ^ 2 } right ) } right ) } { x left ( { 1 + { 1 over 6 } x ^ 2 + { 3 over 40 } x ^ 4 + { 1 over { 112 cdot
  // 99 } } x ^ 6 left ( { 495 + 49 { 1 over 16 } x ^ 2 left ( { 110 + 81 x ^ 2 } right ) } right ) } right ) } { x
  // left ( { 1 + { 1 over 6 } x ^ 2 + { 1 over { 5 cdot 693 } } { 1 over 8 } x ^ 4 left ( { 693 cdot 3 + { 5 over 2 }
  // x ^ 2 left ( { 495 + 49 { 1 over 16 } x ^ 2 left ( { 110 + 81 x ^ 2 } right ) } right ) } right ) } right ) } { {
  // 1 over 10395 } x left ( { 10395 + { 1 over 2 } x ^ 2 left ( { 3465 + { 3 over 4 } x ^ 2 left ( { 2079 + { 5 over
  // 2 } x ^ 2 left ( { 495 + 49 { 1 over 16 } x ^ 2 left ( { 110 + 81 x ^ 2 } right ) } right ) } right ) } right ) }
  // right ) }
  template<int prec_>
  constexpr auto asin(fixed_internal x) noexcept -> fixed_internal
    {
    fixed_internal x2{mul_<prec_>(x, x)};

    constexpr fixed_internal _35o9{div_<prec_>(fixed_internal{35}, fixed_internal{9}) + 1};
    constexpr fixed_internal _5o7{div_<prec_>(fixed_internal{5}, fixed_internal{7}) + 1};
    constexpr fixed_internal _3o5{div_<prec_>(fixed_internal{3}, fixed_internal{5}) + 1};
    constexpr fixed_internal _1o3{div_<prec_>(fixed_internal{1}, fixed_internal{3})};
    constexpr fixed_internal _1{fix_<prec_>(fixed_internal{1})};
    constexpr fixed_internal _63o11{div_<prec_>(fixed_internal{63}, fixed_internal{11}) + 1};

    fixed_internal y6{_35o9 + mul_<prec_ + 1>(x2, _63o11)};
    fixed_internal y7{_5o7 + mul_<prec_ + 3>(x2, y6)};
    fixed_internal y8{_3o5 + mul_<prec_ + 1>(x2, y7)};
    fixed_internal y9{_1o3 + mul_<prec_ + 2>(x2, y8)};
    fixed_internal y10{_1 + mul_<prec_ + 1>(x2, y9)};

    return mul_<prec_>(x, y10);
    }
  }  // namespace detail

//------------------------------------------------------------------------------------------------------
// asin |X| <= 1
struct asin_t
  {
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto x) static_call_operator_const noexcept
    -> fixed_t
    {
    using detail::asin;
    using detail::set_sign;

    fixed_internal x_{x.v};
    bool sign_{};
    if(x_ < 0)
      {
      x_ = -x_;
      sign_ = true;
      }
    static constexpr fixed_internal _1{(1_fix).v};
    if(x_ <= _1) [[likely]]
      {
      constexpr int ext_prec = 4;
      constexpr int prec = 16 + ext_prec;

      if(x_ <= (0.60_fix).v)
        {
        fixed_internal result{asin<prec>(x_ << ext_prec) >> ext_prec};
        return set_sign(sign_, result);
        }
      else
        {
        // asin(x) = pi/2-2*asin(sqrt((1-x)/2))
        fixed_internal sqr{sqrt(as_fixed((_1 - x_) >> 1)).v};
        fixed_internal result{fixpidiv2.v - (asin<prec>(sqr << ext_prec) >> (ext_prec - 1))};
        return set_sign(sign_, result);
        }
      }
    else
      return quiet_NaN_result();
    }
  };

inline constexpr asin_t asin;

//------------------------------------------------------------------------------------------------------
// acos |X| <= 1
struct acos_t
  {
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto operator()(std::same_as<fixed_t> auto x) static_call_operator_const noexcept
    -> fixed_t
    {
    if(x >= -1_fix && x <= 1_fix) [[likely]]
      return as_fixed(fixpidiv2.v - asin(x).v);
    else
      return quiet_NaN_result();
    }
  };

inline constexpr acos_t acos;

//------------------------------------------------------------------------------------------------------
struct sin_angle_t
  {
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto operator()(concepts::arithmetic auto angle) static_call_operator_const noexcept
    -> fixed_t
    {
    return sin(division(multiply(angle, phi), 180));
    }
  };

inline constexpr sin_angle_t sin_angle;

//------------------------------------------------------------------------------------------------------
struct cos_angle_t
  {
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto operator()(concepts::arithmetic auto angle) static_call_operator_const noexcept
    -> fixed_t
    {
    return cos(division(multiply(angle, phi), 180));
    }
  };

inline cos_angle_t cos_angle;

//------------------------------------------------------------------------------------------------------
struct tan_angle_t
  {
  [[nodiscard, gnu::const]]
  static_call_operator constexpr auto operator()(concepts::arithmetic auto angle) static_call_operator_const noexcept
    -> fixed_t
    {
    return tan(division(multiply(angle, phi), 180));
    }
  };

inline constexpr tan_angle_t tan_angle;

  }  // namespace fixedmath::inline v2::fobj

#include "detail/static_call_operator_epilog.h"
