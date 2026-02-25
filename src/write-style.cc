/* Copyright (C) 2017, 2021-2026 Hans Åberg.

   This file is part of MLI, MetaLogic Inference.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */


#include "write-style.hh"
#include "pragmas.hh"


namespace mli {

  std::recursive_mutex write_mutex;
  

  const char* num_subs[] = {"₀", "₁", "₂", "₃", "₄", "₅", "₆", "₇", "₈", "₉"};
  const char* num_sups[] = {"⁰", "¹", "²", "³", "⁴", "⁵", "⁶", "⁷", "⁸", "⁹"};


  std::string to_index(index ix, int64_t k, bool z) {
    std::string r;

    if (k == 0) {
      if (!z)  return std::string();
      r += ix == superscript? "⁰" : "₀";
      return r;
    }

    if (k < 0) {
      r += ix == superscript? "⁻" : "₋";
      k = -k;
    }

    const char** nums = ix? num_sups : num_subs;

    std::string s = std::to_string(k);

    for (auto& i: s)
      r += nums[i - '0'];

    return r;
  }


  // Converts an initial sequence of subscript symbols ₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎
  // to the normal (ASCII range).
  std::string subscript_to_string(const std::string& x) {
    std::string r;

    size_t k = 0;

    // The subscript symbols are in the UTF-8 range E2 82 80 – E2 82 8E,
    // so use a position index p = 0–1 to identify E2 82, and when p = 2,
    // mask out 0xF0, to get a number, which is valid if it is less than 0xF.
    // Then convert to the corresponding ASCII symbol.

    size_t p = 0;

    for (auto& i: x) {
      if (p == 0 && i == '\xE2' || p == 1 && i == '\x82') {
        ++p;
        continue;
      }

      if (p == 2 && (i & '\xF0') == '\x80') {
        int a = (i & '\x0F');

        if (a == 0xF)
          break;

        if (a < 0xA)
          r += (char)(a + '0');
        else
        switch (a) {
          case 0xA: r += '+'; break;
          case 0xB: r += '-'; break;
          case 0xC: r += '='; break;
          case 0xD: r += '('; break;
          case 0xE: r += ')'; break;
        }

        p = 0;
        continue;
      }

      break;
    }

    return r;
  }


  // Converts an initial sequence of superscript symbols ⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾
  // to the normal (ASCII range).
  std::string superscript_to_string(const std::string& x) {
    std::string r;

    size_t k = 0;

    // The superscript symbols are in the UTF-8 range E2 81 B0 – E2 81 BE,
    // except for ¹ C2 B9, ² C2 B2, ³ C2 B3.
    // so use a position index p = 0–1 to identify E2 82, and when p = 2,
    // mask out 0xF0, to get a number, which is valid if it is less than 0xF.
    // Then convert to the corresponding ASCII symbol.

    size_t p = 0;
    bool is_C2 = false;

    for (auto& i: x) {

      if (p == 0 && i == '\xE2' || p == 1 && i == '\x81') {
        ++p;
        continue;
      }

      if (p == 0 && i == '\xC2') {
        is_C2 = true;
        ++p;
        continue;
      }

      if (p == 1 && is_C2) {
        switch (i) {
          case '\xB9': r += '1'; break;
          case '\xB2': r += '2'; break;
          case '\xB3': r += '3'; break;
          default: return r;
        }

        p = 0;
        is_C2 = false;

        continue;
      }

      if (p == 2 && (i & '\xF0') == '\xB0') {
        int a = (i & '\x0F');

        if (a == 0xF)
          break;

        if (a < 0xA)
          r += (char)(a + '0');
        else
        switch (a) {
          case 0xA: r += '+'; break;
          case 0xB: r += '-'; break;
          case 0xC: r += '='; break;
          case 0xD: r += '('; break;
          case 0xE: r += ')'; break;
        }

        p = 0;
        continue;
      }

      break;
    }

    return r;
  }


} // namespace mli

