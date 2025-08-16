// SPDX-FileCopyrightText: 2020-2024 Artur Bać
// SPDX-License-Identifier: BSL-1.0
// SPDX-PackageHomePage: https://github.com/arturbac/fixed_math

#pragma once
#include "math.h"
#include "fixed_string.h"

#include <iostream>
#include <string>
#include <limits>

namespace fixedmath
  {
// Output stream operator overload, using to_string instead of double conversion
inline std::ostream & operator<<(std::ostream & outstr, fixed_t src)
  {
  if(fobj::isnan(src))
    {
    outstr << "NaN";
    }
  else
    {
    // Get the current precision setting of the output stream
    int precision = static_cast<int>(outstr.precision());
    outstr << to_string(src, precision);
    }
  return outstr;
  }

// Input stream operator overload, parsing string to fixed_t
inline std::istream & operator>>(std::istream & instr, fixed_t & dst)
  {
  // Save the current state of the input stream for recovery in case of failure
  std::ios::iostate old_state = instr.rdstate();
  std::streampos old_pos = instr.tellg();

  // Skip leading whitespace
  instr >> std::ws;

  // Check for special value "NaN"
  char peek = instr.peek();
  if(peek == 'N' || peek == 'n')
    {
    std::string nan_str;
    instr >> nan_str;

    // Case-insensitive check for "NaN"
    if(nan_str.size() == 3 && (nan_str[0] == 'N' || nan_str[0] == 'n') && (nan_str[1] == 'A' || nan_str[1] == 'a')
       && (nan_str[2] == 'N' || nan_str[2] == 'n'))
      {
      dst = quiet_NaN_result();
      return instr;
      }
    else
      {
      // Not a valid NaN, restore stream state
      instr.seekg(old_pos);
      instr.setstate(old_state);
      }
    }

  // Read the numerical part
  std::string input;
  instr >> input;

  if(instr.fail())
    return instr;

  // Use from_string function to convert string to fixed_t
  auto result = from_string(input);

  if(result)
    {
    dst = *result;
    }
  else
    {
    // Conversion failed, set failure flag, restore original position
    instr.seekg(old_pos);
    instr.setstate(old_state | std::ios::failbit);
    }

  return instr;
  }
  }  // namespace fixedmath
