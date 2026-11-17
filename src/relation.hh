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
  // Classes for four-way comparison:
  class ordering;
  class comparison;

  constexpr bool is_unordered(ordering x);
  constexpr bool is_ordered(ordering x);
  constexpr bool is_less(ordering x);
  constexpr bool is_greater(ordering x);
  constexpr bool is_equal(ordering x);
  constexpr bool is_not_less(ordering x);
  constexpr bool is_not_greater(ordering x);
  constexpr bool is_not_equal(ordering x);
  constexpr bool is_less_equal(ordering x);
  constexpr bool is_less_greater(ordering x);
  constexpr bool is_greater_equal(ordering x);
  constexpr bool is_not_less_equal(ordering x);
  constexpr bool is_not_less_greater(ordering x);
  constexpr bool is_not_greater_equal(ordering x);

  // Lexical ordering of tuples.
  // Use syntax mli::operator<=>(t0, t1) if t0 <=> t1 conflicts with std::operator<=>. The results
  // are the same if no class ordering value “undordered” occurs and the tuples have the same size,
  // as the latter downgrades x <=> y to x < y and y < x and assumes x == y if both are false.
  template <class... A, class... B>
  mli::ordering operator<=>(const std::tuple<A...>& x, const std::tuple<B...>& y);


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


  // Class for comparison values: unordered ⋚̸, less <, greater >, equal =.
  class ordering {
    uint8_t c_ = 0x0;  // Comparison value.

  public:
    static const ordering unordered;
    static const ordering less;
    static const ordering greater;
    static const ordering equal;


    ordering() = default;

    constexpr explicit ordering(uint8_t const& x) : c_(x) {}

    constexpr explicit operator uint8_t() const { return c_; }

    constexpr comparison operator~() const;


    // Constructor that translates the two comparisons x <= y and y <= x into a class ordering value:
    //   value       y <= x   x <= y   identities expressed in C++
    //   unordered   false    false    x ⋚̸ y  ≔ !(x <= y) && !(y <= x)
    //   less        false    true     x < y  ≔ (x <= y) && !(y <= x)
    //   greater     true     false    x > y  ≔ !(x <= y) && (y <= x)
    //   equal       true     true     x == y ≔ (x <= y) && (y <= x)
    //
    // Also converts C comparison value int to class ordering value
    // by ordering(x, 0), derived from operator x < y, with values:
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
    // by ordering(x, 0), derived from operator x < y, with values:
    //   x < 0 ↦ less, x == 0 ↦ equal, x > 0 ↦ greater
    // or alternatively convert integral values to std::strong_ordering using
    //   x <=> 0
    // which in turn is convertible to class ordering.
    template<class A>
    constexpr ordering(const A& x, const A& y, int);

    // Conversion constructors from C++20 ordering types:
    ordering(std::partial_ordering x) : ordering((x <= 0) + ((x >= 0) << 1)) {}
    ordering(std::strong_ordering x) : ordering((x <= 0) + ((x >= 0) << 1)) {}
    ordering(std::weak_ordering x) : ordering((x <= 0) + ((x >= 0) << 1)) {}

    // Conversion to std::partial_ordering:
    constexpr operator std::partial_ordering() const;

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

  constexpr ordering ordering::unordered(0x0);
  constexpr ordering ordering::less(0x1);
  constexpr ordering ordering::greater(0x2);
  constexpr ordering ordering::equal(0x3);

  constexpr ordering unordered = ordering::unordered;
  constexpr ordering less = ordering::less;
  constexpr ordering greater = ordering::greater;
  constexpr ordering equal = ordering::equal;

  // std::tuple hardcodes std::partial_ordering via std::common_comparison_category
  constexpr ordering::operator std::partial_ordering() const {
    switch (c_) {
      case (uint8_t)ordering::unordered: return std::partial_ordering::unordered;
      case (uint8_t)ordering::less: return std::partial_ordering::less;
      case (uint8_t)ordering::greater: return std::partial_ordering::greater;
      case (uint8_t)ordering::equal: return std::partial_ordering::equivalent;
    };
    return ordering();
  }


  constexpr bool operator==(ordering const& x, ordering const& y) { return (x.c_ == y.c_); }
  constexpr bool operator!=(ordering const& x, ordering const& y) { return (x.c_ != y.c_); }


  constexpr ordering operator!(ordering const& x) { return ordering(~x.c_); }
  constexpr ordering operator||(ordering const& x, ordering const& y) { return ordering(x.c_ | y.c_); }
  constexpr ordering operator&&(ordering const& x, ordering const& y) { return ordering(x.c_ & y.c_); }


  // Defining a partial order on class ordering, compatible with C when int value is used as ordering:
  // “less” < “equal” < “greater”, with “unordered” equal to itself, but unordered with other values,
  // corresponding to int values: “less” ↔ < 0, “equal” ↔ = 0, “greater” ↔ > 0. and no representation
  // for “unordered”.
  constexpr ordering operator<=>(const ordering& x, const ordering& y) {
    if (x == y) return equal;
    if (x == unordered || y == unordered) return unordered;
    if (x == less) return less;
    if (x == greater) return greater;
    // Now x == equal, so if y == less, return greater, and y == greater, return less.
    if (y == less) return greater;
    return less;
  }

  // operator== and operator!= are defined above.
  constexpr bool operator<(const ordering& x, const ordering& y) { return is_less(x <=> y); }
  constexpr bool operator>(const ordering& x, const ordering& y) { return is_greater(x <=> y); }
  constexpr bool operator<=(const ordering& x, const ordering& y) { return is_less_equal(x <=> y); }
  constexpr bool operator>=(const ordering& x, const ordering& y) { return is_greater_equal(x <=> y); }


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
    switch ((uint8_t)x) {
      case (uint8_t)ordering::unordered:
        os << "⋚̸"; break;
      case (uint8_t)ordering::less:
        os << "<"; break;
      case (uint8_t)ordering::equal:
        os << "="; break;
      case (uint8_t)ordering::greater:
        os << ">"; break;
    };

    return os;
  }


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


  constexpr bool is_unordered(ordering x)         { return (comparison(unordered))(x); };
  constexpr bool is_ordered(ordering x)           { return (comparison(~unordered))(x); };
  constexpr bool is_less(ordering x)              { return (comparison(less))(x); };
  constexpr bool is_greater(ordering x)           { return (comparison(greater))(x); };
  constexpr bool is_equal(ordering x)             { return (comparison(equal))(x); };
  constexpr bool is_not_less(ordering x)          { return (comparison(~less))(x); };
  constexpr bool is_not_greater(ordering x)       { return (comparison(~greater))(x); };
  constexpr bool is_not_equal(ordering x)         { return (comparison(~equal))(x); };
  constexpr bool is_less_equal(ordering x)        { return (comparison(less|equal))(x); };
  constexpr bool is_less_greater(ordering x)      { return (comparison(less|greater))(x); };
  constexpr bool is_greater_equal(ordering x)     { return (comparison(greater|equal))(x); };
  constexpr bool is_not_less_equal(ordering x)    { return (comparison(~(less|equal)))(x); };
  constexpr bool is_not_less_greater(ordering x)  { return (comparison(~(less|greater)))(x); };
  constexpr bool is_not_greater_equal(ordering x) { return (comparison(~(greater|equal)))(x); };


#if 0
  template<class A>
  constexpr bool operator==(A const& x, A const& y) { return is_equal(x <=> y); }

  template<class A>
  constexpr bool operator!=(A const& x, A const& y) { return is_not_equal(x <=> y); }

  template<class A>
  constexpr bool operator<(A const& x, A const& y) { return is_less(x <=> y); }

  template<class A>
  constexpr bool operator>(A const& x, A const& y) { return is_greater(x <=> y); }

  template<class A>
  constexpr bool operator<=(A const& x, A const& y) { return is_less_equal(x <=> y); }

  template<class A>
  constexpr bool operator>=(A const& x, A const& y) { return is_greater_equal(x <=> y); }
#endif


  // As the operator<= called here may reference operator<= defined via the class comparison
  // its definition must be later:
  template<class A>
  constexpr ordering::ordering(const A& x, const A& y) : c_((x <= y) + ((y <= x) << 1)) {}

  template<class A>
  constexpr ordering::ordering(const A& x, const A& y, int) : c_((!(y < x)) + ((!(x < y)) << 1)) {}


  // Helper function to operator<=>:
  template <class T, class U, size_t... I>
  ordering tuple_compare(const T& x, const U& y, std::index_sequence<I...>) {
    ordering result = ordering::equal;
    static_cast<void>(((result = ordering(std::get<I>(x), std::get<I>(y)), result != ordering::equal) || ...));
    return result;
  }

  // Lexical ordering of tuples.
  template <class... A, class... B>
  ordering operator<=>(const std::tuple<A...>& x, const std::tuple<B...>& y) {
    ordering result = ordering::equal;
    if constexpr (sizeof...(A) <= sizeof...(B))
      result = tuple_compare(x, y, std::index_sequence_for<A...>{});
    else
      result = tuple_compare(x, y, std::index_sequence_for<B...>{});

    return result == ordering::equal? sizeof...(A) <=> sizeof...(B) : result;
  }

} // namespace mli


