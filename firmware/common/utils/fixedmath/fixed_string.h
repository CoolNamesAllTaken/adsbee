// SPDX-FileCopyrightText: 2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once

#include "types.h"
#include "core_ops.h"
#include <string>
#include <string_view>
#include <optional>
#include <algorithm>
#include <concepts>
#include <array>
#include "detail/static_call_operator_prolog.h"

namespace fixedmath::inline v2
  {
namespace concepts
  {
  template<typename value_type>
  concept char_1b_type
    = std::same_as<std::remove_cvref_t<value_type>, char> or std::same_as<std::remove_cvref_t<value_type>, char8_t>;

  template<typename value_type>
  concept char_type = char_1b_type<value_type> or std::same_as<std::remove_cvref_t<value_type>, char16_t>
                      or std::same_as<std::remove_cvref_t<value_type>, char32_t>
                      or std::same_as<std::remove_cvref_t<value_type>, wchar_t>;
  }  // namespace concepts

namespace detail
  {
  ///\brief match https://en.cppreference.com/w/cpp/string/byte/isblank but is resistant to signed char UB
  struct isblank_t
    {
    template<concepts::char_type char_type>
    [[nodiscard]]
    static_call_operator constexpr bool operator()(char_type src) static_call_operator_const noexcept
      {
      unsigned c{static_cast<unsigned>(src)};
      return unsigned(' ') == c or unsigned('\t') == c;
      }
    };

  inline constexpr isblank_t isblank;

  ///\brief match https://en.cppreference.com/w/cpp/string/byte/isspace but is resistant to signed char UB
  struct isspace_t
    {
    [[nodiscard]]
    static_call_operator constexpr bool operator()(concepts::char_type auto src) static_call_operator_const noexcept
      {
      unsigned c{static_cast<unsigned>(src)};
      return isblank(src) or unsigned('\n') == c or unsigned('\r') == c or unsigned('\v') == c or unsigned('\f') == c;
      }
    };

  inline constexpr isspace_t isspace;

  ///\brief match https://en.cppreference.com/w/cpp/string/byte/isdigit but is resistant to signed char UB
  struct isdigit_t
    {
    [[nodiscard]]
    static_call_operator constexpr bool operator()(concepts::char_type auto src) static_call_operator_const noexcept
      {
      unsigned c{static_cast<unsigned>(src)};
      return c >= 48u and c <= 57u;
      }
    };

  inline constexpr isdigit_t isdigit;

  // 10^-1 * 2^16 (rounded down)
  inline constexpr std::array<fixed_internal, 14> from_string_powers{
    28147497671066,
    2814749767107,
    281474976711,
    28147497671,
    2814749767,
    281474977,
    28147498,
    2814750,
    281475,
    28148,
    2815,
    281,
    28,
    3
  };

  }  // namespace detail

namespace func
  {
  /// Convert a string to fixed_t without using floating point operations
  /// @param str The string to convert
  /// @return An optional fixed_t, which will be nullopt if the conversion failed
  [[nodiscard]]
  inline constexpr auto from_string(std::string_view str) noexcept -> std::optional<fixed_t>
    {
    // Skip leading whitespace
    size_t start = 0;
    while(start < str.size() and detail::isspace(str[start]))
      ++start;

    if(start == str.size())
      return std::nullopt;

    // Check for NaN
    if(start + 2 < str.size() and (str[start] == 'N' or str[start] == 'n')
       and (str[start + 1] == 'A' or str[start + 1] == 'a') and (str[start + 2] == 'N' or str[start + 2] == 'n'))
      {
      // Skip to the end of "NaN"
      start += 3;

      // Verify there's nothing after "NaN" except whitespace
      while(start < str.size() and detail::isspace(str[start]))
        ++start;

      // If we reached the end, it's a valid NaN
      if(start == str.size())
        return quiet_NaN_result();
      else
        return std::nullopt;
      }

    // Check for sign
    bool negative{false};
    if(str[start] == '-')
      {
      negative = true;
      ++start;
      }
    else if(str[start] == '+')
      ++start;

    if(start >= str.size())
      return std::nullopt;

    // Parse integer part
    fixed_internal int_part{0};
    size_t pos{start};

    while(pos < str.size() and detail::isdigit(str[pos]))
      {
      // Check for overflow
      if(int_part > (std::numeric_limits<fixed_internal>::max() / 10))
        return std::nullopt;

      int_part = int_part * 10 + (str[pos] - '0');
      ++pos;
      }

    // Convert integer part to fixed point (shift left by 16 bits)
    fixed_internal result{int_part << 16};

    // Parse decimal part if exists
    if(pos < str.size() and str[pos] == '.')
      {
      ++pos;

      // 16 bits of precision = 65536 units
      // Each position after decimal point is a power of 10:
      // .1 = 6553.6      * 2^32
      // .01 = 655.36     * 2^32
      // .001 = 65.536    * 2^32
      // etc.
      fixed_internal fraction{0};
      uint8_t i{0};

      while(pos < str.size() and detail::isdigit(str[pos]))
        {
        int digit{str[pos] - '0'};

        // Add digit * current power of 10
        fraction += digit * detail::from_string_powers[i];

        // Next decimal place (divide by 10)
        if(i == detail::from_string_powers.size() - 1)  // Stop if we've reached our precision limit
          break;

        ++pos;
        ++i;
        }

      result += fraction >> 32;
      }

    // After parsing, skip all spaces and digits; if any other char, return nullopt
    while(pos < str.size())
      {
      auto const c{str[pos]};
      if(detail::isspace(c) or detail::isdigit(c))
        ++pos;
      else
        return std::nullopt;
      }

    // Apply sign
    if(negative)
      result = -result;

    return as_fixed(result);
    }

  inline constexpr int from_string_default_precision = 5;

  /// Convert fixed_t to string without using floating point operations
  /// @param value The fixed_t value to convert
  /// @param precision The number of decimal places (default: 5)
  /// @return A string representation of the fixed_t value
  [[nodiscard]]
  constexpr auto to_string(std::same_as<fixed_t> auto value, int precision = from_string_default_precision) noexcept
    -> std::string
    {
    // Check if value is NaN
    if(fobj::isnan(value))
      return "NaN";

    std::string result;

    // Handle negative numbers
    bool const negative{value.v < 0};
    fixed_internal abs_value{negative ? -value.v : value.v};

    // Extract integer part (high 48 bits)
    fixed_internal int_part{abs_value >> 16};

    // Convert integer part to string
    if(int_part == 0)
      result = "0";
    else
      {
      while(int_part > 0)
        {
        result.push_back('0' + static_cast<char>(int_part % 10));
        int_part /= 10;
        }
      std::reverse(result.begin(), result.end());
      }

    // Add decimal point and fractional part if precision > 0
    if(precision > 0)
      {
      result.push_back('.');

      // Extract fractional part (low 16 bits)
      fixed_internal frac_part{abs_value & 0xFFFF};

      // Convert to decimal places
      for(uint32_t i = 0; i != precision; ++i)
        {
        // Multiply by 10
        frac_part *= 10;

        // Extract digit
        char digit{static_cast<char>((frac_part >> 16) % 10)};
        result.push_back('0' + digit);

        // Remove used digit
        frac_part &= 0xFFFF;

        // If remaining fraction is zero, stop
        if(frac_part == 0)
          break;
        }

      // Remove trailing zeros
      while(result.back() == '0' and result[result.size() - 2] != '.')
        result.pop_back();
      }

    // Add negative sign if needed
    if(negative)
      result.insert(result.begin(), '-');

    return result;
    }
  }  // namespace func

struct from_string_t
  {
  [[nodiscard]]
  static_call_operator constexpr auto operator()(std::string_view str) static_call_operator_const noexcept
    -> std::optional<fixed_t>
    {
    return func::from_string(str);
    }
  };

struct to_string_t
  {
  [[nodiscard]]
  static_call_operator constexpr auto
    operator()(std::same_as<fixed_t> auto value, int precision = 6) static_call_operator_const noexcept -> std::string
    {
    return func::to_string(value, precision);
    }
  };

///\brief Converts a string to fixed_t
inline constexpr from_string_t from_string{};

///\brief Converts a fixed_t to string
inline constexpr to_string_t to_string{};

  }  // namespace fixedmath::inline v2

#include "detail/static_call_operator_epilog.h"
