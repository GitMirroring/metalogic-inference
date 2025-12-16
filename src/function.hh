/* Copyright (C) 2017, 2021-2025 Hans Åberg.

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

#include "MLI.hh"

#include "substitution.hh"


namespace mli {

  // Class for function 𝒙 ↦ 𝑨, where in evaluation only the free variables of
  // are substituted: (𝒙 ↦ 𝑨)(𝒕) ≔ 𝑨[𝒙 ⤇ 𝒕].
  // Apart from being a base class, function() also represents the
  // identity function.
  class function : public nonempty_formula {
  public:
    new_copy(function);
    new_move(function);

    virtual bool is_identity() const { return true; }


    // Function evaluation.
    // Translates a function application expression into a formula using substitions:
    //   id(𝒕) ≔ 𝒕
    //   (𝒙 ↦ 𝑨)(𝒕) ≔ 𝑨[𝒙 ⤇ 𝒕]
    //   (𝒇 ∘ 𝒈)(𝒕) ≔ 𝒇(𝒈(𝒕))
    virtual val<formula> operator()(val<formula>) const;

    formula::type get_formula_type() const override { return formula::logic; }

    virtual kleenean has(const val<variable>&, occurrence) const { return false; }
    virtual void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const {}


    // Find the set of variables varied in the function.
    virtual void get_varied(std::set<val<variable>>&, metalevel_t) const {}

    // Variables varied of a premise vs, variables varied in reduction vrs, associated
    // with the formulas set variable fsv, and offset m, the position in the substituted premise
    // at where the varied variables should be inserted.
    virtual void get_varied(varied_type& vvs, varied_type& vrs, const variable& fsv, size_type m) const {}


    virtual kleenean free_for(const val<formula>&, const val<variable>&,
      std::set<val<variable>>&, std::list<val<variable>>&) const { return true; }

    void unspecialize(depth, bool) override {}
    void unspecialize(std::set<val<variable>>&, bool) override {}

    val<formula> substitute(const val<substitution>&, substitute_environment) const override { return *this; }

    virtual void set_bind(bind&, name_variable_table&) {}

    virtual alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

  #if 0  // Defined in class formula:
    virtual split_formula split(unify_environment, const val<variable>&, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;
  #endif

    // One has *this = innermost()*without(), and innermost() of the form
    // [x↦t] or equal to I:
    virtual val<function> innermost() const { return *this; }
    virtual val<function> without() const { return *this; }

    // One has *this = within()*outermost(), and outermost() of the form
    // [x↦t] or equal to I:
    virtual val<function> outermost() const { return *this; }
    virtual val<function> within() const { return *this; }

    virtual order compare(const unit&) const;

    virtual void write(std::ostream& os, write_style) const { os << "id"; }
  };


  class function_map : public function {
  public:
    val<variable> variable_;
    val<formula> formula_;

  public:
    function_map() {}

    new_copy(function_map);
    new_move(function_map);

    function_map(const val<variable>& i, const val<formula>& t)
     : variable_(i), formula_(t) {}


    // Function evaluation, (𝒙 ↦ 𝒇)(𝒂) ≔ 𝒇[𝒙 ⤇ 𝒂].
    val<formula> operator()(val<formula> x) const override;

    bool is_identity() const override { return variable_ == formula_; }

    formula::type get_formula_type() const override { return formula::meta; }

    void set_bind(bind&, name_variable_table&) override;
    val<formula> rename(level, degree) const override;
    val<formula> add_exception_set(variable_map&) const override;

    kleenean has(const val<variable>&, occurrence) const override;
    void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const override;

    kleenean free_for(const val<formula>& f, const val<variable>& x,
      std::set<val<variable>>& s, std::list<val<variable>>& bs) const override;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<val<variable>>&, bool) override;

    val<formula> substitute(const val<substitution>&, substitute_environment) const override;

    virtual alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    virtual split_formula split(unify_environment, const val<variable>&, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    val<function> innermost() const override;
    val<function> without() const override;
    val<function> outermost() const override;
    val<function> within() const override;

    order compare(const unit&) const override;

    precedence_t precedence() const override { return formula_->precedence(); }

    void write(std::ostream& os, write_style ws) const override;
  };


  class function_composition : public function {
    val<function> inner_ = val<function>(make);
    val<function> outer_ = val<function>(make);

  public:
    function_composition() = default;

    new_copy(function_composition);
    new_move(function_composition);

    function_composition(const val<function>& outer, const val<function>& inner)
     : outer_(outer), inner_(inner) {}

    // Function evaluation, (𝒇 ∘ 𝒈)(𝒂) ≔ 𝒇(𝒈(𝒂)).
    val<formula> operator()(val<formula> x) const override { return outer_(inner_(x)); }

    bool is_identity() const override { return inner_->is_identity() && outer_->is_identity(); }

    formula::type get_formula_type() const override { return formula::logic; }

    // Variable renumbering:
    void set_bind(bind&, name_variable_table&) override;
    val<formula> rename(level, degree) const override;
    val<formula> add_exception_set(variable_map&) const override;

    // Free variables:
    kleenean has(const val<variable>&, occurrence) const override;
    void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const override;

    kleenean free_for(const val<formula>& f, const val<variable>& x,
      std::set<val<variable>>& s, std::list<val<variable>>& bs) const override;

    // Fixed variables:
    void unspecialize(depth, bool) override;
    void unspecialize(std::set<val<variable>>&, bool) override;

    // Substitution:
    val<formula> substitute(const val<substitution>&, substitute_environment) const override;

    // Unification:
    alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    split_formula split(unify_environment, const val<variable>&, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    val<function> innermost() const override;
    val<function> without() const override;
    val<function> outermost() const override;
    val<function> within() const override;

    // Comparison, needed for unification and database lookup.
    order compare(const unit&) const override;

    // Writing:
    precedence_t precedence() const override { return precedence_t(); }

    void write(std::ostream& os, write_style ws) const override;
  };


  // Reverse function composition f * g = f ∙ g ≔ g ∘ f of functions f, g, in functional
  //   prefix notation: (f ∙ g)(x) = (g ∘ f)(x) ≔ g(f(x))
  //   postfix notation: (x)(f ∙ g) = (x)(g ∘ f) ≔ g(f(x))
  val<function> operator*(const val<function>& f, const val<function>& g);


  // Used for explicit function expressions A[x ⤇ t], formally a pair (A, s)
  // where A is a formula and s = [x ⤇ t] an explicit function. Unification is particularly
  // complicated for this type: u(A[x ⤇ t], B) involvs finding all subexpressions of B
  // unifying with t with a set S occurrences in. Any subset of S can be replaced by
  // x to give a possible A. In addition, if t is unspecialized, then so must this
  // property be forwarded to x.
  class function_application : public nonempty_formula {
  public:
    val<function> function_; // Initializes to the default function id.
    val<formula> formula_;

    function_application() = default;

    function_application(const val<function>& f, const val<formula>& x) : function_(f), formula_(x) {}

    new_copy(function_application);
    new_move(function_application);

    formula::type get_formula_type() const override;

    // Variable renumbering:
    void set_bind(bind&, name_variable_table&) override;
    val<formula> rename(level, degree) const override;
    val<formula> add_exception_set(variable_map&) const override;

    // Free variables:
    kleenean has(const val<variable>&, occurrence) const override;
    void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const override;

    kleenean free_for(const val<formula>& f, const val<variable>& x,
      std::set<val<variable>>& s, std::list<val<variable>>& bs) const override;

    // Fixed variables:
    void unspecialize(depth, bool) override;
    void unspecialize(std::set<val<variable>>&, bool) override;

    // Substitution:
    val<formula> substitute(const val<substitution>&, substitute_environment) const override;

    // Unification:
    alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    split_formula split(unify_environment, const val<variable>&, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    order compare(const unit&) const override;

    // Writing:
    precedence_t precedence() const override;

    void write(std::ostream& os, write_style) const override;
  };

} // namespace mli

