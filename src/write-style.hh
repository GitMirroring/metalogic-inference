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

#pragma once

#include <string>
#include <iostream>
#include <sstream>

#include <mutex>
#include <thread>


namespace mli {

  // For thread write locks, typically using in an environment
  // { std::lock_guard<std::recursive_mutex> guard(write_mutex); /* write */ }
  // ensuring that the thread local recursive locks are properly unnested.
  extern std::recursive_mutex write_mutex;


  enum : uint32_t {
    trace_none            = 0x0,
    trace_all             = ~trace_none,
    trace_bit             = 0x1,
    trace_null            = (trace_bit << 0),
    trace_empty           = (trace_bit << 1),
    trace_result          = (trace_bit << 2),
    trace_proof           = (trace_bit << 3),
    trace_solve           = (trace_bit << 4),
    trace_prooftree       = (trace_bit << 5),
    trace_unify           = (trace_bit << 6),
    trace_split           = (trace_bit << 7),
    trace_substitute      = (trace_bit << 8),
    trace_statement       = (trace_bit << 9),
    trace_database        = (trace_bit << 10),
    trace_formula_type    = (trace_bit << 11),
    trace_unspecializable = (trace_bit << 12),
    trace_variable_type   = (trace_bit << 13),
    trace_variable_label  = (trace_bit << 14),
    trace_structure_type  = (trace_bit << 15),
    trace_thread          = (trace_bit << 16),
    trace_level           = (trace_bit << 17),
    trace_logic           = (trace_bit << 18)
  };

  using trace_type = uint32_t;
  inline trace_type trace_value = trace_none;


  enum write_style {
    // Statements:
    write_proof_margin_level = 0x0F,  // Margin level for proof: 0, ..., 15.
    write_proof_margin_tab = 0xF0,    // Number of spaces for each margin level: 0, ..., 15.
    tabs2 = (2 << 4),                 // Margin tab = 2 spaces.
    write_bit = 0x0100,               // Lowest bit of write mask.
    write_name = write_bit << 0,      // `1.7'
    write_type = write_bit << 1,      // theorem 1.7
    write_statement = write_bit << 2, // theorem 1.7. ⊢ A ⇒ A.
    write_unproved = write_bit << 3,  // theorem 1.7 [*unproved*]. ⊢ A ⇒ A.
    write_proof = write_bit << 4,     // With proof.
    write_proof_indent = write_bit << 5, // Proof lines indented relative statement.

    write_proof_end_newline = write_bit << 7, // '\n' before "##."

    write_function_map_reverse = write_bit << 8,   // Reverse: 𝒇 ↤ 𝒙
    write_function_composition_reverse = write_bit << 9, // Reverse: (𝒇 • 𝒈)(𝒂) ≔ 𝒈(𝒇(𝒂))

    write_substitution_mapto_reverse = write_bit << 10, // Reverse: ~[a ↤ x]A
    write_substitution_composition_reverse = write_bit << 11, // Reverse: (f o g)(x) = g(f(x)).
    write_default =
        0         // Proof margin level.
      | tabs2
      | write_name | write_type | write_statement | write_unproved
      | write_proof | write_proof_indent
  };


  enum index { subscript, superscript };

  struct hide_zero_t {};
  constexpr hide_zero_t hide_zero{};


  // Write integer k as subscript or superscript index. If k == 0 and z false, return empty string.
  std::string to_index(index ix, int64_t k, bool z = true);

  // Write integer k as subscript or superscript index, with last argument hide_zero, if k == 0 return empty string.
  inline std::string to_index(index ix, int64_t k, hide_zero_t) { return to_index(ix, k, false); }


  // Write x as superscript (resp. subscript) if sup is true (resp. false).
  // If x == 0 and z false, return empty string.
  inline std::string to_scriptstring(int x, bool z, bool sup) { return to_index((index)sup, x, z); }


  // Converts an initial sequence of subscript symbols ₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎
  // to the normal (ASCII range).
  std::string subscript_to_string(const std::string& x);

  // Converts an initial sequence of superscript symbols ⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾
  // to the normal (ASCII range).
  std::string superscript_to_string(const std::string& x);


  class spaces {
    int margin_, tab_;
  public:
    spaces(int margin, int tab) : margin_(margin), tab_(tab) {}
    friend std::ostream& operator<<(std::ostream&, const spaces&);
  };


  inline std::ostream& operator<<(std::ostream& os, const spaces& sp) {
    for (int j = 0; j < sp.margin_ * sp.tab_; ++j)  os << ' ';
    return os;
  }


  // Number of UTF-8 characters of a valid UTF-8 string, by counting the leading
  // bytes, that is, those not having the high bits 10.
  inline std::size_t length_utf8(const std::string& x) {
    std::size_t k = 0;

    for (char i: x)
      if ((i & 0xC0) != 0x80)
        ++k;

    return k;
  }


  // Extends UTF-8 by setting length of x > 0x7FFFFFFF to 6, thus
  // admitting 6 byte regular expressins for these numbers.
  inline size_t u8length(uint32_t x) {
    if (x <= 0x0000007F) return 1;
    if (x <= 0x000007FF) return 2;
    if (x <= 0x0000FFFF) return 3;
    if (x <= 0x001FFFFF) return 4;
    if (x <= 0x03FFFFFF) return 5;
    // The following line makes x > 0x7FFFFFFF admissable, as 6 byte sequences:
    return 6;
  }


  // Converting a Unicode code point value to a UTF-8 string.
  // Throws exception if t = true and k exceeds Unicode maximum 0x0010ffffu.
  // If t = false, all uint32_t values of k are accepted, up to 6 bytes.
  inline std::string to_utf8(uint32_t k, bool t = true) {
    if (t && k > 0x10ffffu) {
      std::stringstream ss;
      ss << std::hex << k;
      throw std::runtime_error("Value 0x" + ss.str() + " exceeds Unicode maximum 0x0010ffffu.");
    }

    size_t n = u8length(k); // Number of bytes required.
    std::string r(n, '\0'); // String of n bytes.

    // Builds the UTF-8 string starting with the last, least significant octet:

    for (int i = n - 1; i > 0; --i) {
      r[i] = k & 0x3f | 0x80;
      k >>= 6;
    }

    switch (n) {
      case 1: r[0] = k; break;
      case 2: r[0] = k | 0xc0; break;
      case 3: r[0] = k | 0xe0; break;
      case 4: r[0] = k | 0xf0; break;
      case 5: r[0] = k | 0xf8; break;
      case 6: r[0] = k | 0xfc; break;
    }

    return r;
  }


} // namespace mli

