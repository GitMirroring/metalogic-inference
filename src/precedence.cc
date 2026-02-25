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


#include <iostream>

#include "precedence.hh"


namespace mli {

  precedence_table precedence_table_;

  void write_op(const operator_t& op) {
    op.write(std::cout);
    std::cout << ": " << op.arity() << " + " << op.offset() << " = " << op.size() << "\n";
  }


  void precedence_init() {


    std::vector<std::string> ns0 = {"-"};
    std::vector<std::string> ns1 = {"<", ">"};
    std::vector<std::string> ns2 = {"?", ":"};
    std::vector<std::string> ns3 = {"if", "then"};
    std::vector<std::string> ns4 = {"if", "then", "else"};
    std::vector<std::string> ns5 = {"if", "then", "fi"};
    std::vector<std::string> ns6 = {"if", "then", "else", "fi"};
    std::vector<std::string> ns7 = {"++"};


    std::vector<std::string> ns = ns7;

    operator_t op0(ns, operator_t::infix);
    operator_t op1(ns, operator_t::prefix);
    operator_t op2(ns, operator_t::postfix);
    operator_t op3(ns, operator_t::enfix);

    write_op(op0);
    write_op(op1);
    write_op(op2);
    write_op(op3);


#if 0
    precedence_table_.push_top("metapredicate_argument", assoc::enfix);

    precedence_table_.push_top("metainference", assoc::infix);
    precedence_table_.push_top("metaformula_sequence", assoc::left);

    precedence_table_.push_top("inference", assoc::infix);
    precedence_table_.push_top("formula_definition", assoc::infix);

    precedence_table_.push_top("formula_sequence", assoc::left);

    precedence_table_.push_top("metaor", assoc::left);
    precedence_table_.push_top("metaand", assoc::left);
    precedence_table_.push_top("metanot", assoc::prefix);

    precedence_table_.push_top("predicate_argument", assoc::enfix);

    precedence_table_.push_top("free", assoc::infix);

    precedence_table_.push_top("identical", assoc::infix);
    precedence_table_.push_top("term_definition", assoc::infix);

    precedence_table_.push_top("quantizer", assoc::prefix);

    precedence_table_.push_top("equivalent", assoc::left);
    precedence_table_.push_top("implies", assoc::infix);
    precedence_table_.insert_at("implies", "impliedby", assoc::infix);
    precedence_table_.push_top("logical_or", assoc::left);
    precedence_table_.push_top("logical_and", assoc::left);
    precedence_table_.push_top("logical_not", assoc::prefix);

    precedence_table_.push_top("simple_quantizer", assoc::prefix);

    precedence_table_.push_top("less", assoc::left);
    precedence_table_.insert_at("less", "greater", assoc::left);
    precedence_table_.insert_at("less", "less_or_equal", assoc::left);
    precedence_table_.insert_at("less", "greater_or_equal", assoc::left);

    precedence_table_.insert_at("less", "not_less", assoc::left);
    precedence_table_.insert_at("less", "not_greater", assoc::left);
    precedence_table_.insert_at("less", "not_less_or_equal", assoc::left);
    precedence_table_.insert_at("less", "not_greater_or_equal", assoc::left);

    precedence_table_.push_top("equal", assoc::left);
    precedence_table_.insert_at("equal", "not_equal", assoc::left);

    precedence_table_.push_top("function_argument", assoc::enfix);

    precedence_table_.push_top("subset", assoc::infix);
    precedence_table_.insert_at("subset", "proper_subset", assoc::infix);
    precedence_table_.insert_at("subset", "superset", assoc::infix);
    precedence_table_.insert_at("subset", "proper_superset", assoc::infix);

    precedence_table_.push_top("in", assoc::infix);
    precedence_table_.insert_at("in", "not_in", assoc::infix);

    precedence_table_.push_top("is_set", assoc::prefix);
    precedence_table_.push_top("member_list_set", assoc::enfix);
    precedence_table_.insert_at("member_list_set", "implicit_set", assoc::enfix);

    precedence_table_.push_top("set_union", assoc::left);
    precedence_table_.push_top("set_intersection", assoc::left);
    precedence_table_.insert_at("set_intersection", "set_difference", assoc::left);

    precedence_table_.push_top("set_complement", assoc::prefix);

    precedence_table_.push_top("set_union_operator", assoc::prefix);
    precedence_table_.push_top("set_intersection_operator", assoc::prefix);

    precedence_table_.push_top("mapto", assoc::infix);

    precedence_table_.push_top("vector", assoc::enfix);
    precedence_table_.push_top("list", assoc::enfix);
    precedence_table_.push_top("bracket", assoc::enfix);

    precedence_table_.push_top("list_concat", assoc::left);

    precedence_table_.push_top("factorial", assoc::postfix);

    precedence_table_.push_top("plus", assoc::left);
    precedence_table_.insert_at("plus", "minus", assoc::left);
    precedence_table_.push_top("mult", assoc::left);
    precedence_table_.insert_at("mult", "divide", assoc::left);
    precedence_table_.push_top("unary_minus", assoc::prefix);

    precedence_table_.push_top("substitution_formula", assoc::infix);

#if 0
    precedence_table_.erase("divide");
    precedence_table_.erase("mult");
    precedence_table_.erase("mapto");
#endif

    std::cout << "Precedence table:\n" << std::flush;
    precedence_table_.write(std::cout);


    std::string op = "greater";

    std::cout << "Find " << op << ": ";
    auto p = precedence_table_.find(op);
    std::cout << p.p_ << " " << (uint32_t)p.a_ << std::endl;

#endif
  }


  bool precedence_t::argument(argument_position ap, const precedence_t& x) const {
    if (ap == first) {
      if (x.a_ == assoc::postfix || x.a_ == assoc::enfix || a_ == assoc::prefix || a_ == assoc::enfix)
        return false; // Last argument of x or first of y is delimited.

      if (x.p_ < p_)  return true;
      if (x.p_ > p_)  return false;

      // Now precedences of x and y are equal, x has no postfix and y no prefix
      // components; so associativity will decide:
      if (a_ == assoc::left)
        return false;

      return true;
    }

    if (ap == middle) {
      // In a middle argument, only enfix operators of < precedence need no bracketing.
      if (x.a_ == assoc::enfix)
        return false; // Argument of x is delimited.

      if (x.p_ <= p_)
        return true;

      return false;
    }

    if (ap == last) {
      if (x.a_ == assoc::prefix || x.a_ == assoc::enfix || a_ == assoc::postfix || a_ == assoc::enfix)
        return false; // First argument of x or last of y is delimited.

      if (x.p_ < p_)  return true;
      if (x.p_ > p_)  return false;

      // Now precedences of x and y are equal, x has no postfix and y no prefix
      // components; so associativity will decide:
      if (a_ == assoc::right)
        return false;

      return true;
    }

    return false;
  }


  void operator_t::write(std::ostream& os) const {
    bool it0 = true;

    for (auto& i: ns_) {
      if (it0) {
       it0 = false;
       if (f_ == infix || f_ == postfix)
        os << "* ";
      }
      else
        os << " * ";

      os << i;
    }

    if (f_ == infix || f_ == prefix)
      os << " *";

  }


  void precedence_table::compute() {
    uint32_t k = 1;

    for (auto i = ps_.begin(); i != ps_.end(); ++i, ++k)
      *i = k;

    for (auto& i: op_)
      i.second.second.p_ = *i.second.first;
  }


  void precedence_table::push_bottom(const std::string& x, assoc a) {
    auto p = op_.insert({x, {{}, {a}}});

    if (p.second == false)
      throw precedence_error("precedence_table::push_bottom: operator name " + x + " already exists in table.");

    ps_.push_front(0);
    p.first->second.first = ps_.begin();
    compute();
  }


  void precedence_table::push_top(const std::string& x, assoc a) {
    auto p = op_.insert({x, {{}, {a}}});

    if (p.second == false)
      throw precedence_error("precedence_table::push_top: operator name " + x + " already exists in table.");

    auto i = ps_.insert(ps_.end(), precedence_default);
    p.first->second.first = i;
    compute();
  }


  void precedence_table::insert_below(const std::string& x0, const std::string& x, assoc a) {
    auto px = op_.insert({x, {{}, {a}}});

    if (px.second == false)
      throw precedence_error("precedence_table::insert_below: operator name " + x + " already exists in table.");

    auto iy = op_.find(x0);

    if (iy == op_.end())
      throw precedence_error("precedence_table::insert_below: operator name " + x0 + " does not exist in table.");

    auto i = ps_.insert(iy->second.first, iy->second.second.p_);
    px.first->second.first = i;
    compute();
  }


  void precedence_table::insert_at(const std::string& x0, const std::string& x, assoc a) {
    auto px = op_.insert({x, {{}, {a}}});

    if (px.second == false)
      throw precedence_error("precedence_table::insert_at: operator name " + x + " already exists in table.");

    auto iy = op_.find(x0);

    if (iy == op_.end())
      throw precedence_error("precedence_table::insert_at: operator name " + x0 + " does not exist in table.");

    px.first->second.first = iy->second.first;
    compute();
  }


  void precedence_table::insert_above(const std::string& x0, const std::string& x, assoc a) {
    auto px = op_.insert({x, {{}, {a}}});

    if (px.second == false)
      throw precedence_error("precedence_table::insert_above: operator name " + x + " already exists in table.");

    auto iy = op_.find(x0);

    if (iy == op_.end())
      throw precedence_error("precedence_table::insert_above: operator name " + x0 + " does not exist in table.");

    auto i = ps_.insert(++predecence_iterator(iy->second.first), iy->second.second.p_);
    px.first->second.first = i;
    compute();
  }


  bool precedence_table::erase(const std::string& x) {
    // First find x in op_, and if present, check it there is more than one operator
    // using this precedence, if not, remove it and recompute precedences.
    auto ix = op_.find(x);

    if (ix == op_.end())
      return false;

    auto ip = ix->second.first;

    op_.erase(ix);

    for (auto& i: op_)
      if (i.second.first == ip)
        return true;  // Some other operator also has this precedence.

    // Now x was only operator with this precednec, so remove it:
    ps_.erase(ip);
    compute();
    return true;
  }


  precedence_t precedence_table::find(const std::string& x) {
    auto ix = op_.find(x);

    if (ix == op_.end())
      throw precedence_error("precedence_table::find: operator name " + x + " does not exist in table.");

    return ix->second.second;
  }


  void precedence_table::write(std::ostream& os) const {
#if 1
    // Reverse map, precedence to set of operator names:
    std::multimap<precedence_t, std::string> pn;

    for (auto& i: op_)
      pn.insert({i.second.second, i.first});

    uint32_t p = 0;

    bool it0 = true;
    bool it1 = true;

    for (auto& i: pn) {
      if (i.first.p_ != p) {
        it1 = false;
        p = i.first.p_;
        if (it0) it0 = false; else os << "\n";
        os << i.first.p_ << ": ";
      }
      if (it1) os << " "; else it1 = true;
      os << i.second << "/" << (uint32_t)i.first.a_;
    }

    os << std::endl;
#else
    for (auto& i: op_)
      os << i.first << " " << *i.second.first << " "
         << i.second.second.p_ << " "
         << (uint32_t)i.second.second.a_
         << std::endl;
#endif
  }

} // namespace mli
