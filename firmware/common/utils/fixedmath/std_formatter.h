// SPDX-FileCopyrightText: 2020-2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once
#include "math.h"
#include "fixed_string.h"
#include <format>
#include <algorithm>
#include <charconv>

namespace fixedmath::inline v2::detail
  {
template<typename iterator>
struct ctx_parse_res
  {
  int precision;
  iterator out;
  };

template<typename iterator>
[[nodiscard]]
constexpr auto ctx_parse(iterator it, iterator const end) -> ctx_parse_res<iterator>
  {
  int precision = fixedmath::func::from_string_default_precision;
  if(it != end and *it != '}')
    {
    int local_prec{};
    do
      {
      if(detail::isdigit(*it))
        local_prec = local_prec * 10 + (*it - '0');
      else if(*it == '}')
        break;
      else [[unlikely]]
        throw std::format_error("Invalid fixed_t precision format");
      ++it;
      } while(it != end);
    if(local_prec > 16) [[unlikely]]
      throw std::format_error("Invalid fixed_t precision format");
    precision = local_prec;
    }
  return ctx_parse_res{precision, it};
  }
  }  // namespace fixedmath::inline v2::detail

template<>
struct std::formatter<fixedmath::fixed_t>
  {
  int precision = fixedmath::func::from_string_default_precision;

  template<typename ParseContext>
  constexpr auto parse(ParseContext & ctx) -> decltype(ctx.begin())
    {
    fixedmath::detail::ctx_parse_res const res{fixedmath::detail::ctx_parse(ctx.begin(), ctx.end())};
    precision = res.precision;
    return res.out;
    }

  template<typename FormatContext>
  auto format(fixedmath::fixed_t const & value, FormatContext & ctx) const -> decltype(ctx.out())
    {
    auto const formatted{fixedmath::func::to_string(value, precision)};
    return std::copy(formatted.begin(), formatted.end(), ctx.out());
    }
  };
