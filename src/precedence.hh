/* Copyright (C) 2017, 2021-2024 Hans Åberg.

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

#include <limits>
#include <climits>
#include <cstdint>

#include <initializer_list>
#include <list>
#include <map>
#include <unordered_set>
#include <string>
#include <vector>

#include "exception.hh"


#define NEW_PREC 1


namespace mli {

  // The fixity specifies the sides on which the operator may be closed or open:
  // infix    both sides open
  // prefix   first closed, last open
  // postfix  first open, last closed
  // enfix    both sides closed
  // When writing an expression, it suffices to write parentheses around
  // an argument that appears on an open side and is open on the opposite
  // side and has lower precedence. E.g., in a*(b + c), '*' is open right,
  // '+' is open left, and '+' has lower precedence than '*'.
  enum class assoc : uint8_t {
    infix, prefix, postfix, enfix, left, right
  };


  enum argument_position : uint8_t {
    first, middle, last
  };


  class precedence_t {
  public:
    static constexpr uint32_t precedence_default = std::numeric_limits<uint32_t>::max();

    uint32_t p_ = precedence_default;   // Precedence number.

    // Associativity, specifying relation between first and last argument precedences.
    assoc a_ = assoc::enfix;


    constexpr precedence_t(uint32_t x, assoc a = assoc::enfix)
     : p_(x), a_(a) {}

    constexpr precedence_t(assoc a = assoc::enfix)
     : a_(a) {}


    // True if x as argument of *this in the indicated position ap requires grouping
    // like "()", "{}", etc., in writeout.
    bool argument(argument_position ap, const precedence_t& x) const;

    friend bool operator<(const precedence_t& x, const precedence_t& y);
  };


  inline bool operator<(const precedence_t& x, const precedence_t& y) { return x.p_ < y.p_; }


  class operator_t {
  public:
    // The fixity specifies the sides on which the operator may be closed or open:
    // infix    both sides open
    // prefix   first closed, last open
    // postfix  first open, last closed
    // enfix    both sides closed
    // When writing an expression, it suffices to write parentheses around
    // an argument that appears on an open side and is open on the opposite
    // side and has lower precedence. E.g., in a*(b + c), '*' is open right,
    // '+' is open left, and '+' has lower precedence than '*'.
    enum fixity : uint8_t {
      infix = 0x0, prefix = 0x1, postfix = 0x2, enfix = prefix | postfix
    };

    std::vector<std::string> ns_;   // Name of components.
    fixity f_ = enfix;              // Fixity: whether delimited front and/or back.

    operator_t() = default;

    operator_t(const std::vector<std::string>& ns, fixity f) : ns_(ns), f_(f) {}

    template<class IIter>
    operator_t(IIter i0, IIter i1, fixity f) : ns_(i0, i1), f_(f) {}

    operator_t(std::initializer_list<std::string> ns, fixity f) : ns_(ns), f_(f) {}

    // size ≔ number of components delimiting the arguments
    // arity ≔ number of arguments
    // offset ≔ size - arity, 0 for prefix/postfix, -1 for infix, +1 for enfix.
    int offset() const { return (f_ & prefix) + (f_ & postfix) - 1; }
    int size() const { return ns_.size(); }
    int arity() const { return ns_.size() - offset(); }

    void write(std::ostream&) const;
  };


  class precedence_table {
  public:
    using precedence_type = uint32_t;

    static constexpr precedence_type precedence_default = std::numeric_limits<precedence_type>::max();

    using precedence_list = std::list<precedence_type>;
    using predecence_iterator = precedence_list::iterator;

    // Helper containers to compute the precedence numbers:
    precedence_list ps_;     // List of precedences.

    // Operator precedence table.
    std::map<std::string, std::pair<predecence_iterator, precedence_t>> op_;


    precedence_table() = default;

    void compute(); // Compute precedence numbers before comparison.

    // Insert operator x with lowest resp. highest precedence:
    void push_bottom(const std::string& x, assoc a);
    void push_top(const std::string& x, assoc a);

    // Insert below, at, or above, the precedence of x the operator y with associativity a.
    void insert_below(const std::string& x, const std::string& y, assoc a);
    void insert_at(const std::string& x, const std::string& y, assoc a);
    void insert_above(const std::string& x, const std::string& y, assoc a);

    bool erase(const std::string&);

    // Find precedence of x, or throw exception if not available.
    precedence_t find(const std::string& x);

    void write(std::ostream&) const;
  };


  extern precedence_table precedence_table_;


  enum class precedence_number : uint32_t {
    first = 10,

    inference_ml_2,

    predicate_argument_ml_1,

    inference,
    formula_definition,

    formula_sequence,

    metaor,
    metaand,
    metanot,

    predicate_argument,
    logic,

    free,

    identical,
    term_definition,

    quantizer,  // all x: ...

    equivalent,
    implies,
    impliedby = implies,
    logical_or,
    logical_and,
    logical_not,

    simple_quantizer,  // all x A

    equal,
    not_equal = equal,

    less,
    greater = less,
    less_or_equal = less,
    greater_or_equal = less,

    not_less = less,
    not_greater = less,
    not_less_or_equal = less,
    not_greater_or_equal = less,

    divides,
    not_divides = divides,

    function_argument,
    tuple,

    subset,
    proper_subset = subset,
    superset = subset,
    proper_superset = subset,

    in,
    not_in = in,

    is_set,
    member_list_set,
    implicit_set = member_list_set,

    set_union,
    set_intersection,
    set_difference = set_intersection,

    set_complement,

    set_union_operator,
    set_intersection_operator,

    mapto,

    vector,
    list,
    bracket,
    list_concat,

    factorial,
    plus,
    minus = plus,
    mult,
    divide = mult,
    unary_minus,

    formula_substitution,
    substitution_formula,

    last,
  };


  // Precedence p, associativity a, fixity f:
  #define op_prec(p, a) \
    constexpr precedence_t p ## _oprec = \
      precedence_t((uint32_t)precedence_number::p, a)

  op_prec(inference_ml_2, assoc::infix);

  op_prec(predicate_argument_ml_1, assoc::enfix);
  op_prec(inference, assoc::infix);

  op_prec(formula_definition, assoc::infix);

  op_prec(formula_sequence, assoc::left);

  op_prec(metaor, assoc::left);
  op_prec(metaand, assoc::left);
  op_prec(metanot, assoc::prefix);

  op_prec(predicate_argument, assoc::enfix);
  op_prec(logic, assoc::enfix);

  op_prec(free, assoc::infix);

  op_prec(identical, assoc::infix);
  op_prec(term_definition, assoc::infix);

  op_prec(quantizer, assoc::prefix);

  op_prec(equivalent, assoc::left);
  op_prec(implies, assoc::infix);
  op_prec(impliedby, assoc::infix);
  op_prec(logical_or, assoc::left);
  op_prec(logical_and, assoc::left);
  op_prec(logical_not, assoc::prefix);

  op_prec(simple_quantizer, assoc::prefix);

  op_prec(less, assoc::left);
  op_prec(greater, assoc::left);
  op_prec(less_or_equal, assoc::left);
  op_prec(greater_or_equal, assoc::left);

  op_prec(not_less, assoc::left);
  op_prec(not_greater, assoc::left);
  op_prec(not_less_or_equal, assoc::left);
  op_prec(not_greater_or_equal, assoc::left);

  op_prec(equal, assoc::left);
  op_prec(not_equal, assoc::left);

  op_prec(divides, assoc::left);
  op_prec(not_divides, assoc::left);

  op_prec(function_argument, assoc::enfix);
  op_prec(tuple, assoc::enfix);

  op_prec(subset, assoc::infix);
  op_prec(proper_subset, assoc::infix);
  op_prec(superset, assoc::infix);
  op_prec(proper_superset, assoc::infix);

  op_prec(in, assoc::infix);
  op_prec(not_in, assoc::infix);

  op_prec(is_set, assoc::prefix);
  op_prec(member_list_set, assoc::enfix);
  op_prec(implicit_set, assoc::enfix);

  op_prec(set_union, assoc::left);
  op_prec(set_intersection, assoc::left);
  op_prec(set_difference, assoc::left);

  op_prec(set_complement, assoc::prefix);

  op_prec(set_union_operator, assoc::prefix);
  op_prec(set_intersection_operator, assoc::prefix);

  op_prec(mapto, assoc::infix);

  op_prec(vector, assoc::enfix);
  op_prec(list, assoc::enfix);
  op_prec(bracket, assoc::enfix);

  op_prec(list_concat, assoc::left);

  op_prec(factorial, assoc::postfix);

  op_prec(plus, assoc::left);
  op_prec(minus, assoc::left);
  op_prec(mult, assoc::left);
  op_prec(divide, assoc::left);
  op_prec(unary_minus, assoc::prefix);

  op_prec(formula_substitution, assoc::postfix);
  op_prec(substitution_formula, assoc::postfix);

  #undef op_prec

} // namespace mli

