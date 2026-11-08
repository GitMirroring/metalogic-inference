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


#include <cstdint>
#include <functional>
#include <iostream>
#include <string>
#include <tuple>

#include <compare>

namespace mli {
  class ordering;
}

namespace std {
  // Not defined in C++20:
  // Lexical ordering of tuples starting at index i:
#define USE_TUPLE_COMPARE 1

#if USE_TUPLE_COMPARE
  template <std::size_t i, class... A, class... B>
  mli::ordering operator<=>(const std::tuple<A...>& x, const std::tuple<B...>& y);
#endif

} // namespace std


namespace mli {

  // Classes for four-way comparison:
  // class ordering = {unordered, less, gtreater, equal}, allowing simultaneously giving
  // the values r(x, y) and r(y, x) of binary relations r.
  // The class comparison defines all possible comparison operators from these class ordering values.
  //
  // The eventually added C++ three-way comparison is too unstructured and limited
  // for use in stricter logical contexts.

  // A (binary) relation R on a set A is a subset of A × A, and define x R y ≔ (x, y) ∈ R, so
  // x R y ∈ 𝔹 ≔ bool, i.e. R is a binary predicate function A × A → 𝔹.
  // Then there are four possible values for the pair (x R y, y R x) ∈ 𝔹 × 𝔹, which are given names
  // as though R is identical to ≤:
  //  (x R y) (y R x)  result      symbol
  //   false   false   unordered     ⋚̸
  //   true    false   less          <
  //   false   true    greater       >
  //   true    true    equal         =
  //
  // The class ordering has the comparison values: unordered ⋚̸, less <, greater >, equal =.
  // It is used to indicate the result of a comparison function compare(x, y), which
  // then gives simultanous information about the values x R y and y R x.
  // Changing the argument order compare(x, y) ⤳ compare(y, x), then preserves the
  // values equal, unordered, and interchanges the values less, greater.
  // Formally, if ι: ordering → ordering is the function (an involution) defined by
  //   equal ↦ equal, unordered ↦ unordered, less ↦ greater, greater ↦ less
  // then ι(compare(x, y)) = compare(y, x) for all x, y.
  // A comparison function compare(x, y) is assumed to fulfill this requirement.

  //
  /* Comparison values, as in class ordering: unordered ⋚̸, less <, greater >, equal =.
    The class comparison, defining the various comparison operators, consists of the
    set of all Boolean functions on this set, so there are 2^4 = 16 such functions:
        ⋚̸  <  >  =
     𝕗  0  0  0  0   false                   false
     𝕥  1  1  1  1   true                    true
     <  0  1  0  0   less                    x < y
     ≮  1  0  1  1   not less              !(x < y)
     ≤  0  1  0  1   less or equal           x <= y
     ≰  1  0  1  0   not less or equal     !(x <= y)
     >  0  0  1  0   greater                 x > y
     ≯  1  1  0  1   not greater           !(x > y)
     ≥  0  0  1  1   greater or equal        x >= y
     ≱  1  1  0  0   not greater or equal  !(x >= y)
     =  0  0  0  1   equal                   x = y
     ≠  1  1  1  0   not equal               x != y
     ≶  0  1  1  0   less or greater       (x < y) || (x > y)
     ≸  1  0  0  1   not less or greater   !(x < y) && !(x > y)
     ⋚  0  1  1  1   ordered               (x <= y) || (x >= y)
     ⋚̸  1  0  0  0   unordered             !(x <= y) && !(x >= y)
   */

  // type relation: total order, partial order.

  class ordering;
  class comparison;

  // Class for comparison values: unordered ⋚̸, less <, greater >, equal =.
  class ordering {
    uint8_t c_ = 0x0;  // Comparison value.

  public:

    ordering() = default;

    constexpr explicit ordering(uint8_t const& x) : c_(x) {}

    constexpr operator uint8_t() const { return c_; }

    constexpr comparison operator~() const;


    // Constructor that translates the two comparisons x <= y and y <= x into a class ordering value:
    //   y <= x   x <= y   result
    //   false    false    unordered
    //   false    true     less
    //   true     false    greater
    //   true     true     equal
    //
    // Classical C comparison value converted to class ordering value is given
    // by ordering(x, 0), derived from operator x <= y, with values:
    //   x < 0 ↦ less, x == 0 ↦ equal, x > 0 ↦ greater
    template<class A>
    constexpr ordering(const A& x, const A& y);

    template<class A, class Less_equal>
    ordering(const A& x, const A& y, Less_equal comp) : c_(comp(x, y) + (comp(y, x) << 1)) {}


    // Constructor that translates the two comparisons x < y and y < x into a class ordering value:
    //   y < x    x < y    result
    //   false    false    equal
    //   false    true     less
    //   true     false    greater
    //   true     true     unordered
    // The last entry, x < y and y < x both true, is strictly an error, but
    // is added for completeness.
    //
    // Classical C comparison value converted to class ordering value is given
    // by ordering(x, 0, 0), derived from operator x < y, with values:
    //   x < 0 ↦ less, x == 0 ↦ equal, x > 0 ↦ greater
    template<class A>
    constexpr ordering(const A& x, const A& y, int);

    // Conversion constructors from C++20 ordering types:
    ordering(std::partial_ordering x) : ordering((x <= 0) + ((x >= 0) << 1)) {}
    ordering(std::strong_ordering x) : ordering((x <= 0) + ((x >= 0) << 1)) {}
    ordering(std::weak_ordering x) : ordering((x <= 0) + ((x >= 0) << 1)) {}

    // Lexicographical order, as in {x0 <=> y0, …}.
    ordering(std::initializer_list<ordering> xs);

    // Lexicographical order, using operator<=>.
    template <class Iterator1, class Iterator2>
    ordering(Iterator1 first1, Iterator1 last1,
                    Iterator2 first2, Iterator2 last2);

    // Lexicographical order, using a comparison function returning a value of type ordering.
    template <class Iterator1, class Iterator2, class Compare>
    ordering(Iterator1 first1, Iterator1 last1,
                    Iterator2 first2, Iterator2 last2,
                    Compare compare);

    friend class comparison;

    friend constexpr bool operator==(ordering const&, ordering const&);
    friend constexpr bool operator!=(ordering const&, ordering const&);

    friend constexpr ordering operator!(ordering const&);
    friend constexpr ordering operator||(ordering const&, ordering const&);
    friend constexpr ordering operator&&(ordering const&, ordering const&);
  };

  constexpr ordering unordered(0x0);
  constexpr ordering less(0x1);
  constexpr ordering greater(0x2);
  constexpr ordering equal(0x3);

  constexpr bool operator==(ordering const& x, ordering const& y) { return (x.c_ == y.c_); }
  constexpr bool operator!=(ordering const& x, ordering const& y) { return (x.c_ != y.c_); }

  constexpr ordering operator!(ordering const& x) { return ordering(~x.c_); }
  constexpr ordering operator||(ordering const& x, ordering const& y) { return ordering(x.c_ | y.c_); }
  constexpr ordering operator&&(ordering const& x, ordering const& y) { return ordering(x.c_ & y.c_); }


  inline ordering::ordering(std::initializer_list<ordering> xs) {
    for (auto& i: xs) {
      *this = i;
      if (*this != equal) return;
    }
  }


  template <class Iterator1, class Iterator2>
  ordering::ordering(Iterator1 first1, Iterator1 last1,
                  Iterator2 first2, Iterator2 last2) {
    for (; first1 != last1 && first2 != last2; ++first1, ++first2) {
      *this = *first1 <=> *first2;
      if (*this != equal) return;
    }

    *this = (first1 != last1) <=> (first2 != last2);
  }


  // Lexicographical order, using a comparison function returning a value of type ordering.
  template <class Iterator1, class Iterator2, class Compare>
  ordering::ordering(Iterator1 first1, Iterator1 last1,
                  Iterator2 first2, Iterator2 last2,
                  Compare compare) {
    for (; first1 != last1 && first2 != last2; ++first1, ++first2) {
      *this = compare(*first1, *first2);
      if (*this != equal) return;
    }

    *this = (first1 != last1) <=> (first2 != last2);
  }


  inline std::ostream& operator<<(std::ostream& os, ordering const& x) {
    switch (x) {
      case unordered:
        os << "⋚̸"; break;
      case less:
        os << "<"; break;
      case equal:
        os << "="; break;
      case greater:
        os << ">"; break;
    };

    return os;
  }


  // Classical C comparison value converted to class ordering value:
  //  x < 0 ~> less, x == 0 ~> equal, x > 0 ~> greater.
  template<class A>
  inline ordering sgn(A const& x) { return x <=> A(); }


  // Class comparison: Producing the set of all possible comparison operators
  // that can be derived from the class ordering comparison values.
  // All 0xf mask values are possible, with each bit representing a class ordering
  // value, giving rise to the following table:
  // bit   0 1 2 3
  // value ⋚̸ < > =
  class comparison {
    uint8_t r_;  // Comparison operator value.

  public:
    comparison() = delete;

    constexpr explicit comparison(uint8_t const& x) : r_(x) {}

    constexpr comparison(ordering const& x) : r_(1 << x.c_) {}

    constexpr operator uint8_t() const { return r_; }

    // Producing the boolean comparison value from a comparison value:
    constexpr bool operator()(ordering const& x) const { return r_ & comparison(x).r_; }


    // Producing the comparison operator given a comparison function compare<A>(x, y).
    // E.g., f ≔ comparison(less|equal)(compare<A>) is the operator<= associated with compare,
    // used as f(x, y).
    template<class A>
    std::function<bool(A, A)> operator()(std::function<ordering(A, A)> f)
    { return [this, f](A x, A y){return r_ & comparison(f(x, y)).r_;}; }


    // The 0xf is a mask, ensuring that the return is a class comparison value:
    constexpr comparison operator~() const { return comparison(~r_ & 0xf); }

    // Return true if unorderd bit set.
    constexpr bool negated() const { return 0x1 & r_; }

    friend class ordering;

    friend constexpr comparison operator|(comparison const& x, comparison const& y);
    friend constexpr comparison operator&(comparison const& x, comparison const& y);

    friend constexpr bool operator==(comparison const& x, comparison const& y);
    friend constexpr bool operator!=(comparison const& x, comparison const& y);
  };


  inline std::ostream& operator<<(std::ostream& os, comparison const& x) {
    switch (x) {
      case 0: os << "𝕗"; break;
      case 8: os << "="; break;
      case 4: os << ">"; break;
      case 12: os << "≥"; break;
      case 2: os << "<"; break;
      case 10: os << "≤"; break;
      case 6: os << "≶"; break;
      case 14: os << "⋚"; break;
      case 1: os << "⋚̸"; break;
      case 9: os << "≸"; break;
      case 5: os << "≰"; break;
      case 13: os << "≮"; break;
      case 3: os << "≱"; break;
      case 11: os << "≯"; break;
      case 7: os << "≠"; break;
      case 15: os << "𝕥"; break;

      default: os << (int)(uint8_t)(x); break;
    };

    return os;
  }


  constexpr comparison operator|(comparison const& x, comparison const& y) { return comparison(x.r_ | y.r_); }
  constexpr comparison operator&(comparison const& x, comparison const& y) { return comparison(x.r_ & y.r_); }

  constexpr comparison ordering::operator~() const { return ~comparison(*this); }


  constexpr bool operator==(comparison const& x, comparison const& y) { return x.r_ == y.r_; }
  constexpr bool operator!=(comparison const& x, comparison const& y) { return x.r_ != y.r_; }


  // Added in ordering to avoid conflict conversions with ordering::operator uint8_t():

  constexpr comparison operator|(ordering const& x, ordering const& y) { return comparison(x) | y; }
  constexpr comparison operator|(ordering const& x, comparison const& y) { return comparison(x) | y; }
  constexpr comparison operator|(comparison const& x, ordering const& y) { return x | comparison(y); }

  constexpr comparison operator&(ordering const& x, ordering const& y) { return comparison(x) & y; }
  constexpr comparison operator&(ordering const& x, comparison const& y) { return comparison(x) & y; }
  constexpr comparison operator&(comparison const& x, ordering const& y) { return x & comparison(y); }


  std::ostream& operator<<(std::ostream& os, comparison const& x);


  constexpr comparison is_unordered(unordered);
  constexpr comparison is_ordered(~unordered);
  constexpr comparison is_less(less);
  constexpr comparison is_greater(greater);
  constexpr comparison is_equal(equal);
  constexpr comparison is_not_less(~less);
  constexpr comparison is_not_greater(~greater);
  constexpr comparison is_not_equal(~equal);
  constexpr comparison is_less_equal(less|equal);
  constexpr comparison is_less_greater(less|greater);
  constexpr comparison is_greater_equal(greater|equal);
  constexpr comparison is_not_less_equal(~(less|equal));
  constexpr comparison is_not_less_greater(~(less|greater));
  constexpr comparison is_not_greater_equal(~(greater|equal));



#if 0
#if 1
  template<class A>
  constexpr bool operator==(A const& x, A const& y) { return is_equal(x <=> y); }

  template<class A>
  constexpr bool operator!=(A const& x, A const& y) { return is_not_equal(x <=> y); }
#else
  template<class A, class B>
  constexpr bool operator==(A const& x, B const& y) { return is_equal(x <=> y); }

  template<class A, class B>
  constexpr bool operator!=(A const& x, B const& y) { return is_not_equal(x <=> y); }
#endif

  template<class A>
  constexpr bool operator<(A const& x, A const& y) { return is_less(x <=> y); }

  template<class A>
  constexpr bool operator>(A const& x, A const& y) { return is_greater(x <=> y); }

  template<class A>
  constexpr bool operator<=(A const& x, A const& y) { return is_less_equal(x <=> y); }

  template<class A>
  constexpr bool operator>=(A const& x, A const& y) { return is_greater_equal)(x <=> y); }
#endif

  // As the operator<= called here may reference operator<= defined via the class comparison
  // its defininition must be later:
  template<class A>
  constexpr ordering::ordering(const A& x, const A& y) : c_((x <= y) + ((y <= x) << 1)) {}

  template<class A>
  constexpr ordering::ordering(const A& x, const A& y, int) : c_((!(y < x)) + ((!(x < y)) << 1)) {}

} // namespace mli


namespace std {

#if USE_TUPLE_COMPARE
  // Lexical ordering of tuples starting at index i:
  template <std::size_t i, class... A, class... B>
  mli::ordering operator<=>(const std::tuple<A...>& x, const std::tuple<B...>& y) {
    constexpr std::size_t a = std::tuple_size<std::tuple<A...>>::value;
    constexpr std::size_t b = std::tuple_size<std::tuple<B...>>::value;

    if constexpr (i != std::min(a, b)) {
      mli::ordering r = get<i>(x) <=> get<i>(y);
      if (r != mli::equal) return r;
      return operator<=><i+1>(x, y);
    }

    // Index out of bounds; sizes determine the return:
    return a <=> b;
  }

  // Lexical ordering of tuples.
  template <class... A, class... B>
  mli::ordering operator<=>(const std::tuple<A...>& x, const std::tuple<B...>& y) {
    return operator<=><0>(x, y);
  }
#endif

} // namespace std


