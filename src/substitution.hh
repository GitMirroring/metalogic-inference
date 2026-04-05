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

#include "MLI.hh"
#include "definition.hh"
#include "precedence.hh"

#include <map>
#include <set>
#include <vector>
#include <deque>
#include <tuple>


namespace mli {


  /* A substitution is a function mapping variables to formulas of the same
  object type as the variable, i.e., variable describing terms are mapped to
  terms, etc. It is then extended via the functions A::substitute() to a mapping
  of formulas to formulas of matching formula type.

    substitution()  the identity substitution; maps a variable x to itself viewed
                    as a formula.
    variable_substitution(x, f)
                    the substitution that maps the variable x to the formula f.
    s(f)            extends the substituion s to the formula f.
    s1 + s2         the composition (s1 o s2)(x) := s1(s2(x)).
    s1 * s2         the composition (s1 * s2)(x) := s2(s1(x)).
  */


  // Apart from being a base class, substitution() also represents the
  // identity substitution.
  class substitution : public nonempty_formula {
  public:
    new_copy(substitution);
    new_move(substitution);

    virtual bool is_identity() const { return true; }

    virtual val<formula> substitute_variable(const val<variable>& x, substitute_environment) const
    { return val<formula>(x); }

    // Extends the substitution *this to a function, mapping formulas to formulas:
    virtual val<formula> operator()(const val<formula>& x) const;

    formula::type get_formula_type() const override { return formula::meta; }

    virtual kleenean has(const val<variable>&, occurrence) const { return false; }
    virtual void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const {}


    // Find the set of variables varied in the substitution.
    virtual void get_varied(std::set<val<variable>>&, metalevel_t) const {}

    // Variables varied of a premise vs, variables varied in reduction vrs, associated
    // with the formulas set variable fsv, and offset m, the position in the substituted premise
    // at where the varied variables should be inserted.
    virtual void get_varied(varied_type& vvs, varied_in_reduction_type& vrs, const variable& fsv, size_type m) const {}


    virtual kleenean free_for(const val<formula>&, const val<variable>&, 
      std::set<val<variable>>&, std::list<val<variable>>&) const { return true; }

    void unspecialize(depth, bool) override {}
    void unspecialize(std::set<val<variable>>&, bool) override {}

    virtual val<formula> substitute(const val<substitution>&, substitute_environment) const { return *this; }

    virtual void set_bind(bind&, name_variable_table&) {}

    virtual alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

  #if 0  // Defined in class formula:
    virtual split_formula split(unify_environment, const val<variable>&, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;
  #endif

    // One has *this = innermost()*without(), and innermost() of the form
    // [x↦t] or equal to I:
    virtual val<substitution> innermost() const { return *this; }
    virtual val<substitution> without() const { return *this; }

    // One has *this = within()*outermost(), and outermost() of the form
    // [x↦t] or equal to I:
    virtual val<substitution> outermost() const { return *this; }
    virtual val<substitution> within() const { return *this; }

    virtual order compare(const unit&) const;

    virtual void write(std::ostream& os, write_style) const { os << "I"; }
  };


  class variable_substitution : public substitution {
  public:
    val<variable> variable_;
    val<formula> formula_;

    // A substitution from a premise to a conclusion only substitutes
    // free occurrences if explicit, a varied variable in case not
    // representing the identity.
    bool premise_to_conclusion_ = false;
    bool is_varied_ = false;

    size_type premise_index_ = 0;
    size_type conclusion_index_ = 0;

    varied_type varied_;
    varied_in_reduction_type varied_in_reduction_;


  public:
    variable_substitution() {}

    new_copy(variable_substitution);
    new_move(variable_substitution);


    variable_substitution(const val<variable>& i, const val<formula>& t)
     : variable_(i), formula_(t) {}

    variable_substitution(const val<variable>& i, const val<formula>& t,
      const varied_type& vs, const varied_in_reduction_type& vrs)
     : variable_(i), formula_(t), varied_(vs), varied_in_reduction_(vrs) {}

    variable_substitution(const val<variable>& i, const val<formula>& t, size_type px, size_type cx, bool v)
     : variable_(i), formula_(t), premise_index_(px),
       premise_to_conclusion_(true), conclusion_index_(cx), is_varied_(v) {}


    virtual bool is_identity() const { return variable_ == formula_; }

    virtual val<formula> substitute_variable(const val<variable>& x, substitute_environment) const;

    formula::type get_formula_type() const override { return formula::meta; }

    virtual void set_bind(bind&, name_variable_table&);
    virtual val<formula> rename(level, degree) const;
    virtual val<formula> add_exception_set(variable_map&) const override;

    virtual kleenean has(const val<variable>&, occurrence) const;
    virtual void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const;


    // A substitution of limited variables is varied if it comes from a premise to a conclusion,
    // is explicit, and does not represent the identity substitution. However, variable::unify
    // only sets is_varied_ if also is_explicit_ && premise_to_conclusion_ is true, so a check
    // for the latter is not required here.
    bool is_varied() const { return is_varied_; }

    void get_varied(std::set<val<variable>>& vs, metalevel_t ml) const override {
      if (is_varied() && ml == variable_->metalevel_)
        vs.insert(variable_);
    }

    void get_varied(varied_type& vvs, varied_in_reduction_type& vrs, const variable& fsv, size_type m) const override {
      if (*variable_ == fsv) {
        for (auto& i: varied_)
          for (auto& j: i.second)
            for (auto& k: j.second)
              vvs[i.first][j.first + m].insert(k);

          for (auto& j: varied_in_reduction_)
            for (auto& k: j.second)
                vrs[j.first + m].insert(k);
      }
    }

    virtual kleenean free_for(const val<formula>& f, const val<variable>& x, 
      std::set<val<variable>>& s, std::list<val<variable>>& bs) const;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<val<variable>>&, bool) override;

    virtual val<formula> substitute(const val<substitution>&, substitute_environment) const;

    virtual alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual split_formula split(unify_environment, const val<variable>&, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual val<substitution> innermost() const;
    virtual val<substitution> without() const;
    virtual val<substitution> outermost() const;
    virtual val<substitution> within() const;

    virtual order compare(const unit&) const;

    virtual precedence_t precedence() const { return formula_->precedence(); }

    virtual void write(std::ostream& os, write_style ws) const;
  };


  class explicit_substitution : public substitution {
  public:
    val<variable> variable_;
    val<formula> formula_;

  public:
    explicit_substitution() {}

    new_copy(explicit_substitution);
    new_move(explicit_substitution);


    explicit_substitution(const val<variable>& i, const val<formula>& t)
     : variable_(i), formula_(t) {}


    virtual bool is_identity() const { return variable_ == formula_; }

    virtual val<formula> substitute_variable(const val<variable>& x, substitute_environment) const;

    virtual alternatives unify_substitution2(const val<formula>&, unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    formula::type get_formula_type() const override { return formula::meta; }

    virtual void set_bind(bind&, name_variable_table&);
    virtual val<formula> rename(level, degree) const;
    virtual val<formula> add_exception_set(variable_map&) const override;

    virtual kleenean has(const val<variable>&, occurrence) const;
    virtual void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const;

    virtual kleenean free_for(const val<formula>& f, const val<variable>& x,
      std::set<val<variable>>& s, std::list<val<variable>>& bs) const;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<val<variable>>&, bool) override;

    virtual val<formula> substitute(const val<substitution>&, substitute_environment) const;

    virtual alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual split_formula split(unify_environment, const val<variable>&, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual val<substitution> innermost() const;
    virtual val<substitution> without() const;
    virtual val<substitution> outermost() const;
    virtual val<substitution> within() const;

    virtual order compare(const unit&) const;

    virtual precedence_t precedence() const { return formula_->precedence(); }

    virtual void write(std::ostream& os, write_style ws) const;
  };


  class substitution_composition : public substitution {
    val<substitution> inner_ = val<substitution>(make);
    val<substitution> outer_ = val<substitution>(make);

  public:
    substitution_composition() = default;

    new_copy(substitution_composition);
    new_move(substitution_composition);

    substitution_composition(const val<substitution>& outer, const val<substitution>& inner)
     : outer_(outer), inner_(inner) {}

    virtual bool is_identity() const { return inner_->is_identity() && outer_->is_identity(); }

    virtual val<formula> substitute_variable(const val<variable>& x, substitute_environment vt) const;

    formula::type get_formula_type() const override { return formula::meta; }

    // Variable renumbering:
    virtual void set_bind(bind&, name_variable_table&);
    virtual val<formula> rename(level, degree) const;
    virtual val<formula> add_exception_set(variable_map&) const override;

    // Free variables:
    virtual kleenean has(const val<variable>&, occurrence) const;
    virtual void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const;


    void get_varied(std::set<val<variable>>& vs, metalevel_t ml) const override
    { inner_->get_varied(vs, ml); outer_->get_varied(vs, ml); }

    void get_varied(varied_type& vvs, varied_in_reduction_type& vrs, const variable& fsv, size_type m) const override
    { inner_->get_varied(vvs, vrs, fsv, m); outer_->get_varied(vvs, vrs, fsv, m); }


    virtual kleenean free_for(const val<formula>& f, const val<variable>& x, 
      std::set<val<variable>>& s, std::list<val<variable>>& bs) const;

    // Fixed variables:
    void unspecialize(depth, bool) override;
    void unspecialize(std::set<val<variable>>&, bool) override;

    // Substitution:
    virtual val<formula> substitute(const val<substitution>&, substitute_environment) const;

    // Unification:
    virtual alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;
    
    virtual split_formula split(unify_environment, const val<variable>&, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual val<substitution> innermost() const;
    virtual val<substitution> without() const;
    virtual val<substitution> outermost() const;
    virtual val<substitution> within() const;

    // Comparison, needed for unification and database lookup.
    virtual order compare(const unit&) const;

    // Writing:
    virtual precedence_t precedence() const { return precedence_t(); }

    virtual void write(std::ostream& os, write_style ws) const;
  };


  // Composition objects f * g = f ∙ g ≔ g ∘ f of substitutions viewed as functions f, g (as described above),
  // i.e., written in prefix notation as (f ∙ g)(x) = (g ∘ f)(x) ≔ g(f(x)), and in postfix notation
  // written (x)(f ∙ g) = (x)(g ∘ f) ≔ g(f(x)).
  // Variable substitutions f, g are written postfix, so A f g = A (f*g)
  val<substitution> operator*(const val<substitution>& f, const val<substitution>& g);


  // Used for explicit substitution expressions A[x ⤇ t], formally a pair (A, s)
  // where A is a formula and s = [x ⤇ t] an explicit substitution. Unification is particularly
  // complicated for this type: u(A[x ⤇ t], B) involvs finding all subexpressions of B
  // unifying with t with a set S occurrences in. Any subset of S can be replaced by
  // x to give a possible A. In addition, if t is unspecialized, then so must this
  // property be forwarded to x.
  class substitution_formula : public nonempty_formula {
  public:
    val<explicit_substitution> substitution_; // Initializes to default substitution, i.e., I.
    val<formula> formula_;


    substitution_formula() = default;

    substitution_formula(const val<explicit_substitution>& s, const val<formula>& f)
     : substitution_(s), formula_(f) {}


    new_copy(substitution_formula);
    new_move(substitution_formula);

    virtual formula::type get_formula_type() const;

    // Variable renumbering:
    virtual void set_bind(bind&, name_variable_table&);
    virtual val<formula> rename(level, degree) const;
    virtual val<formula> add_exception_set(variable_map&) const override;

    // Free variables:
    virtual kleenean has(const val<variable>&, occurrence) const;
    virtual void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const;

    virtual kleenean free_for(const val<formula>& f, const val<variable>& x,
      std::set<val<variable>>& s, std::list<val<variable>>& bs) const;

    // Fixed variables:
    void unspecialize(depth, bool) override;
    void unspecialize(std::set<val<variable>>&, bool) override;

    // Substitution:
    virtual val<formula> substitute(const val<substitution>&, substitute_environment) const;

    // Unification:
    virtual alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;


    // Helper functions, for special types of unification:

    // Type 1: 𝐮(𝑨[𝒙 ⤇ 𝒕], 𝑩[𝒚 ⤇ 𝒖]) = 𝐮(𝒙, 𝒚).𝐮(𝑨, 𝑩).𝐮(𝒕, 𝒖).
    alternatives unify1(unify_environment, const substitution_formula&, unify_environment, database*, level, degree_pool&, direction) const;

    // Type 2. 𝐮(𝑨[𝒙 ⤇ 𝒕], 𝑩) = 𝐮(𝒕, 𝒱).𝐮(𝑨, 𝑩[𝒱 ↦ 𝒙]) where 𝒱 is a disjoint set of subformulas of 𝑩.
    // The cases 𝒱 = ∅ and 𝒱 = {𝑩} are allowed, in the latter case, 𝒕 and 𝑩 must be of the same type.
    alternatives unify2(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;


    virtual split_formula split(unify_environment, const val<variable>&, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    // Comparison, needed for unification and database lookup.
    virtual order compare(const unit&) const;

    // Writing:
    virtual precedence_t precedence() const;

    virtual void write(std::ostream& os, write_style) const;
  };


  class alternative : public unit {
  public:
    val<substitution> substitution_;  // Initializes to default substitution, i.e., I.
    val<formula> goal_;

#if NEW_PROVED
    // For writing out the proof. The component statement_ is the statement used in the
    // unification, and definitions_ is the set of definitions. The substatements are
    // the statements used implicitly, like for logic, not required explicitly but shown
    // to allow for a more detailed examination of the proof.
    struct statement_data {
      val<statement> statement_;
      std::vector<val<statement>> definitions_;
      std::deque<val<statement>> substatements_;
    };

    std::map<size_type, statement_data> labelstatements_;
#else
    // For writing out the proof. First pair component is the statement used in the object
    // formula unification, the second component is the set of definitions and substatements used,
    // if any. A substatement is an implicit statement, like for logic, which is noy required
    // for the proof, but show to allow for a more detailed examination of the proof.
    std::map<size_type, std::pair<val<statement>, std::vector<val<statement>>>> labelstatements_;
#endif

    alternative() = default;
    
    new_copy(alternative);
    new_move(alternative);

    alternative(const val<substitution>& s) : substitution_(s) {}
    alternative(const val<formula>& g) : goal_(g) {}
    alternative(const val<substitution>& s, const val<formula>& g)
     : substitution_(s), goal_(g) {}

    virtual alternative& label(const val<statement>&, level);           // For statements.
    virtual alternative& label(const val<statement>&, level, degree);   // For definitions and deductions.
    virtual alternative& sublabel(const val<statement>&, level);        // For substatements.

    alternative add_goal(const val<formula>& x) const;

    alternative add_premise(const val<formula>& x, metalevel_t,
      const varied_type& vs, const varied_in_reduction_type& vrs) const;

    virtual size_type metasize() const { return goal_->metasize(); }

    val<substitution> operator*() { return substitution_; }
    const val<substitution> operator*() const { return substitution_; }

    val<formula> substitute_variable(const val<variable>& x, substitute_environment vt) const
    { return substitution_->substitute_variable(x, vt); }

    val<formula> operator()(const val<formula>& x) const { return (*substitution_)(x); }

    void write(std::ostream&, write_style) const;
    
    // Combine substitutions and conditions (goals) as of old x followed by new y.
    // That is, in right hand notation, if x = (s, a), y = (t, b), then
    // x*y = (s*t, (a)t * b) where s*t is substition composition, s inner and t outer,
    // and (a)t is t applied to a.
    // This is the semidirect product 𝒮 ⋉ ℱ of the monoid 𝒮 of the set of
    // substitutions acting on the monoid ℱ the set of formula sequences.
    friend alternative operator*(const alternative& x, const alternative& y);
  };


  class alternatives : public unit {
  public:
    using container_type = std::list<alternative>;
    using size_type = container_type::size_type;
    using iterator = container_type::iterator;
    using const_iterator = container_type::const_iterator;
    using reverse_iterator = container_type::reverse_iterator;
    using const_reverse_iterator = container_type::const_reverse_iterator;

    container_type alternatives_;  

    alternatives() = default;

    new_copy(alternatives);
    new_move(alternatives);

    alternatives(const alternative& x)
     : alternatives_(1, x) {}

    explicit alternatives(const val<formula>& f)
     : alternatives_(1, alternative(f)) {}

    alternatives(const val<substitution>& s)
     : alternatives_(1, alternative(s)) {}
    
    alternatives(const val<substitution>& s, const val<formula>& g)
     : alternatives_(1, alternative(s, g)) {}

    alternatives(const val<variable_substitution>& s)
     : alternatives(val<substitution>(s)) {}

    alternatives(const val<explicit_substitution>& s)
     : alternatives(val<substitution>(s)) {}


    iterator               begin() { return alternatives_.begin(); }
    const_iterator         begin() const { return alternatives_.begin(); }
    iterator               end() { return alternatives_.end(); }
    const_iterator         end() const { return alternatives_.end(); }
    reverse_iterator       rbegin() { return alternatives_.rbegin(); }
    const_reverse_iterator rbegin() const { return alternatives_.rbegin(); }
    reverse_iterator       rend() { return alternatives_.rend(); }
    const_reverse_iterator rend() const { return alternatives_.rend(); }

    virtual bool empty() const { return alternatives_.empty(); }
    virtual size_type size() const { return alternatives_.size(); }

    virtual bool operator!() const { return alternatives_.empty(); }

    virtual void clear() { return alternatives_.clear(); }

    iterator erase(iterator i) { return alternatives_.erase(i); }

    virtual alternatives& label(const val<statement>&, level);          // For statements.
    virtual alternatives& label(const val<statement>&, level, degree);  // For definitions.
    virtual alternatives& sublabel(const val<statement>&, level);       // For substatements.
#if UNIFY_FALSE
    virtual alternatives& sublabel(const std::string& ls, val<formula> x, level lv) {
      return sublabel(val<statement>(make, ls, x), lv);
    }

    virtual alternatives& sublabel(const std::string& ls, level lv) {
      return sublabel(val<statement>(make, ls, val<formula>{}), lv);
    }
#endif

    virtual alternatives& push_back(const alternative& a);
    virtual alternatives& append(const alternatives& as);
    
    virtual const alternative& front() const { return alternatives_.front(); }
    virtual alternative& front() { return alternatives_.front(); }

    virtual alternative pop_front() {
      alternative a = alternatives_.front(); alternatives_.pop_front(); return a; }

    alternatives add_goal(const val<formula>& x) const;

    alternatives add_premise(const val<formula>& x, metalevel_t,
      const varied_type& vs, const varied_in_reduction_type& vrs) const;


    // For use in recursive computations of unify:
    // Each *this list alternative substitution s is applied to x and y,
    // computing unify(s(x), s(y)), and these returns are combined into a
    // single alternatives return value.
    virtual alternatives unify(const val<formula>& x, unify_environment tx, const val<formula>& y, unify_environment ty, database*, level, degree_pool&, direction, expansion = expand) const;

    // For use in the unification of binder expressions. unify_binder() differs from the recursive
    // unify() in that the substitution of variables is not kept in the total substitution.
    virtual alternatives unify_binder(
      const val<formula>& x, unify_environment tx,
      const val<formula>& y, unify_environment ty,
      database*, level, degree_pool&, direction) const;

    virtual void write(std::ostream&, write_style) const;

    // Combine substitutions and conditions (goals) as of old x followed by new y.
    friend alternatives operator*(const alternatives& x, const alternatives& y);
  };


  // Frequent alternatives:
  extern const alternatives O;  // No alternatives.
  extern const alternatives I;  // Identity substitution.


  // Combine substitutions and condition (goals) as of old x followed by new y, i.e., the goals
  // of x and y are concatenated with the substitution of y applied to the goal of x
  // and the substitution of x becomes the inner and the one of y the outer.
  alternative operator*(const alternative& x, const alternative& y);

  // Combining the x*y of the single alternatives contained in x and y:
  alternatives operator*(const alternatives& x, const alternatives& y);


  alternative merge(const alternative& x, const alternative& y,
    const val<formula>& h, const val<formula>& b, metalevel_t ml,
    const varied_type& vs, const varied_in_reduction_type& vrs);

  alternatives merge(const alternatives& x, const alternatives& y,
    const val<formula>& h, const val<formula>& b, metalevel_t ml,
    const varied_type& vs, const varied_in_reduction_type& vrs);


  class proof : public unit {
  public:
    using container_type = std::list<alternative>;
    using size_type = container_type::size_type;
    using iterator = container_type::iterator;
    using const_iterator = container_type::const_iterator;
    using reverse_iterator = container_type::reverse_iterator;
    using const_reverse_iterator = container_type::const_reverse_iterator;

    val<formula> goal_;
    container_type proof_;
    bool conditional_ = false; // True if not all statements used have a strict proof.

    proof() = default;

    new_copy(proof);
    new_move(proof);

    proof(const val<formula>& x) : goal_(x) {}

    void push_front(const alternative&);
    void push_back(const alternative&);

    // Search the statements of the alternatives, and set conditional_
    // to true if not all have a strict proof.
    void set_conditional();

    bool is_conditional() const { return conditional_; }

    virtual void write(std::ostream&, write_style) const;
  };


  // A proof container.
  using proofs = std::list<proof>;

#define NEW_SUBFORMULAS 1

#if NEW_SUBFORMULAS
  class subformulas {
  public:
    using value_type = std::pair<val<formula>, std::set<val<variable>>>;
    using container_type = std::list<value_type>;
    using iterator = container_type::iterator;
    using const_iterator = container_type::const_iterator;
    using reverse_iterator = container_type::reverse_iterator;
    using const_reverse_iterator = container_type::const_reverse_iterator;

    container_type formulas_;  

    subformulas() = default;

    subformulas(const val<formula>& f)
     : formulas_(1, {f, {}}) {}

    subformulas(const val<formula>& f, const std::set<val<variable>>& vs)
     : formulas_(1, {f, {vs}}) {}


    bool operator!() const { return formulas_.empty(); }
    void clear() { formulas_.clear(); }

    iterator begin() { return formulas_.begin(); }
    const_iterator begin() const { return formulas_.begin(); }
    iterator end() { return formulas_.end(); }
    const_iterator end() const { return formulas_.end(); }
    reverse_iterator rbegin() { return formulas_.rbegin(); }
    const_reverse_iterator rbegin() const { return formulas_.rbegin(); }
    reverse_iterator rend() { return formulas_.rend(); }
    const_reverse_iterator rend() const { return formulas_.rend(); }

    void push_back(const val<formula>& f) {
      formulas_.push_back({f, {}});
    }

    void push_back(const val<formula>& f, const std::set<val<variable>>& vs) {
      formulas_.push_back({f, vs});
    }

    void append(const subformulas& x) {
      formulas_.insert(formulas_.end(), x.formulas_.begin(), x.formulas_.end());
    }

    const value_type& front() const { return formulas_.front(); }
    value_type& front() { return formulas_.front(); }
    value_type pop_front() {
      value_type v = formulas_.front(); formulas_.pop_front(); return v; }

    void write(std::ostream& os, write_style ws) const;
  };
#else
  class subformulas {
  public:
    using value_type = val<formula>;
    using container_type = std::list<value_type>;
    using iterator = container_type::iterator;
    using const_iterator = container_type::const_iterator;
    using reverse_iterator = container_type::reverse_iterator;
    using const_reverse_iterator = container_type::const_reverse_iterator;

    container_type formulas_;  

    subformulas() = default;

    subformulas(const val<formula>& f)
     : formulas_(1, f) {}

    bool operator!() const { return formulas_.empty(); }
    void clear() { formulas_.clear(); }

    iterator begin() { return formulas_.begin(); }
    const_iterator begin() const { return formulas_.begin(); }
    iterator end() { return formulas_.end(); }
    const_iterator end() const { return formulas_.end(); }
    reverse_iterator rbegin() { return formulas_.rbegin(); }
    const_reverse_iterator rbegin() const { return formulas_.rbegin(); }
    reverse_iterator rend() { return formulas_.rend(); }
    const_reverse_iterator rend() const { return formulas_.rend(); }

    void push_back(const val<formula>& f) {
      formulas_.push_back(f);
    }
    void append(const subformulas& x) {
      formulas_.insert(formulas_.end(), x.formulas_.begin(), x.formulas_.end());
    }

    const value_type& front() const { return formulas_.front(); }
    value_type& front() { return formulas_.front(); }
    value_type pop_front() {
      value_type v = formulas_.front(); formulas_.pop_front(); return v; }

    void write(std::ostream& os, write_style ws) const;
  };
#endif

  inline std::ostream& operator<<(std::ostream& os, const subformulas& x) {
    x.write(os, write_default);  return os;
  }


  // List of pairs (fs, f), where fs are subformulas and f a formula:
  // Starting with a formula 𝑩 and a variable 𝒙, the 'split' function produces
  // a list of (fs, f), where fs is a list of disjoint subformulas of 𝑩, and f is
  // the formula achieved by replacing each fs with 𝒙.
  // If all subformulas fs unify with 𝑡 in 𝑨[𝒙 ↦ 𝑡], then f is a valid 𝑨.
  class split_formula {
  public:
    using value_type = std::tuple<subformulas, val<formula>, std::set<val<variable>>>;

    using container_type = std::list<value_type>;
    using iterator = container_type::iterator;
    using const_iterator = container_type::const_iterator;
    using reverse_iterator = container_type::reverse_iterator;
    using const_reverse_iterator = container_type::const_reverse_iterator;

    container_type sequence_;
    alternatives alternatives_;

    split_formula() = default;
    
    split_formula(const val<formula>& f)
     : sequence_(1, value_type(subformulas(), f, {})) {}
    
    split_formula(const val<formula>& fs, const val<formula>& f)
     : sequence_(1, value_type(subformulas(fs), f, {})) {}
    
    split_formula(const subformulas& fs, const val<formula>& f)
     : sequence_(1, value_type(fs, f, {})) {}

    split_formula(const subformulas& fs, const val<formula>& f, const std::set<val<variable>>& vs)
     : sequence_(1, value_type(fs, f, vs)) {}


    bool operator!() const { return sequence_.empty(); }
    void clear() { sequence_.clear(); }

    iterator begin() { return sequence_.begin(); }
    const_iterator begin() const { return sequence_.begin(); }
    iterator end() { return sequence_.end(); }
    const_iterator end() const { return sequence_.end(); }
    reverse_iterator rbegin() { return sequence_.rbegin(); }
    const_reverse_iterator rbegin() const { return sequence_.rbegin(); }
    reverse_iterator rend() { return sequence_.rend(); }
    const_reverse_iterator rend() const { return sequence_.rend(); }

    void push_back(const val<formula>& f) {
      sequence_.push_back(value_type(subformulas(), f, {}));
    }

    void push_back(const val<formula>& fs, const val<formula>& f) {
      sequence_.push_back(value_type(subformulas(fs), f, {}));
    }

    void push_back(const subformulas& fs, const val<formula>& f) {
      sequence_.push_back(value_type(fs, f, {}));
    }

#if NEW_SUBFORMULAS
    void push_back(const val<formula>& fs, const val<formula>& f, const std::set<val<variable>>& vs) {
      sequence_.push_back(value_type(subformulas({fs, vs}), f, vs));
    }
#else
    void push_back(const val<formula>& fs, const val<formula>& f, const std::set<val<variable>>& vs) {
      sequence_.push_back(value_type(subformulas(fs), f, vs));
    }
#endif

    void push_back(const subformulas& fs, const val<formula>& f, const std::set<val<variable>>& vs) {
      sequence_.push_back(value_type(fs, f, vs));
    }


    void append(const split_formula& x) {
      sequence_.insert(sequence_.end(), x.sequence_.begin(), x.sequence_.end());
    }

    const value_type& front() const { return sequence_.front(); }
    value_type& front() { return sequence_.front(); }
    value_type pop_front() {
      value_type v = sequence_.front(); sequence_.pop_front(); return v; }

    void write(std::ostream& os, write_style ws) const;
  };


  inline std::ostream& operator<<(std::ostream& os, const split_formula& x) {
    x.write(os, write_default);  return os;
  }


  // Precondition: iterator is not end, that is, no index component is end.
  template<class Con, class Iter>
  void increment(Con& vs, Iter& is) {

    auto i = vs.rbegin();

    for (auto k = is.rbegin(); k != is.rend(); ++k, ++i) {
      ++*k;

      // If k is the first element, let *k remain 'end' as a marker.
      if (*k != i->end() || k == std::prev(is.rend()))
        break;

      *k = i->begin();
    }
  }


  template<class Con, class Iter>
  bool is_end(Con& vs, Iter& is) {
    // The iterator is 'end' if first component is 'end', so check that one.
    return (*is.begin() == vs.begin()->end());
  }


  // Container is a sequence container with value_type = val<formula>.
  // Construct is a class, such as a lambda, that converts a Container to the split class.
  template<class Container, class Construct>
  split_formula split(
    const Container& as, const Construct& c, unify_environment ta,
    const val<variable>& x, const val<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) {

    if (trace_value & trace_split) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);

      std::clog << "Begin split(";

      bool iter0 = true;

      for (auto& a: as) {
        if (iter0) iter0 = false;
        else
          std::clog << " : ";

        std::clog << a;
      }

      std::clog << "), replacement "
        << x << ", condition: " << t
        << std::endl;
    }

    split_formula sf; // Return value;

    std::list<split_formula> sfs;

    for (auto& a: as)
      sfs.push_back(a->split(ta, x, t, tt, dbp, lv, sl, dr));


    if (trace_value & trace_split) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);

      std::clog << "split(";

      bool iter0 = true;

      for (auto& a: as) {
        if (iter0) iter0 = false;
        else
          std::clog << " : ";

        std::clog << a;
      }

      std::clog << "), replacement " << x << ", condition: " << t << ":\n";

      size_t k = 0;

      for (auto& i: sfs) {
        std::clog << "  sf[" << std::to_string(k) << "]:\n" << i << std::endl;
        ++k;
      }

      std::clog << std::endl;
    }


    std::list<split_formula::container_type::iterator> is;

    for (auto& i: sfs)
      is.push_back(i.sequence_.begin());

    for (; !is_end(sfs, is); increment(sfs, is)) {
      subformulas fs;
      std::remove_cvref_t<decltype(as)> bs;
      std::set<val<variable>> vs;

      for (auto& i: is) {
        fs.append(std::get<0>(*i));

        bs.push_back(std::get<1>(*i));

        vs.insert(std::get<2>(*i).begin(), std::get<2>(*i).end());
      }

      val<formula> f = c(bs);


      if (trace_value & trace_split) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);
        std::clog << "  construct ";

        bool iter0 = true;

        for (auto& i: is) {
          if (iter0) iter0 = false;
          else
            std::clog << " : ";

          std::clog << std::get<1>(*i);
        }

        std::clog << std::endl;
        std::clog << "    " << f << "\n  concatenate: " << std::flush;

        iter0 = true;

        for (auto& i: is) {
          if (iter0) iter0 = false;
          else
            std::clog << " + ";

          std::clog << std::get<0>(*i);
        }

        std::clog << " = " << fs << std::endl;
      }


      if (!!fs)
        sf.push_back(fs, f, vs);
    }

    return sf;
  }


  // Precondition: iterator is not end, that is, no index component is end.
  template<class Con, std::size_t N>
  struct Split {
    static void increment(Con& vs) {
      ++std::get<N-1>(vs).second;

      if (std::get<N-1>(vs).second != std::get<N-1>(vs).first.sequence_.end())
        return;

      std::get<N-1>(vs).second = std::get<N-1>(vs).first.sequence_.begin();

      Split<Con, N-1>::increment(vs);
    }

    static bool is_end(Con& vs) {
      // The iterator is 'end' if first component is 'end', so check that one.
      if (std::get<N-1>(vs).second == std::get<N-1>(vs).first.sequence_.end())
        return true;

      return Split<Con, N-1>::is_end(vs);
    }
  };


  // Precondition: iterator is not end, that is, no index component is end.
  template<class Con>
  struct Split<Con, 1> {
    static void increment(Con& vs) {
      ++std::get<0>(vs).second;
    }

    static bool is_end(Con& vs) {
      // The iterator is 'end' if first component is 'end', so check that one.
      return (std::get<0>(vs).second == std::get<0>(vs).first.sequence_.end());
    }
  };


  struct print_sfs {
    print_sfs(size_t) {}

    template<typename A, typename... As>
    print_sfs(size_t k, A& a, As&... as) {
      std::clog << "  sf[" << std::to_string(k) << "]:\n" << a.first << std::endl;
      print_sfs(k + 1, as...);
    }

    template<typename A, typename... As>
    print_sfs(A& a, As&... as) : print_sfs(0, a, as...) {}
  };


  struct print_sfs_formulas {
    print_sfs_formulas() {}

    template<typename A>
    print_sfs_formulas(A& a) {
      std::clog << std::get<1>(*a.second) << std::flush;
    }

    template<typename A0, typename A1, typename... As>
    print_sfs_formulas(A0& a0, A1& a1, As&... as) {
      std::clog << std::get<1>(*a0.second) << " : " << std::flush;
      print_sfs_formulas(a1, as...);
    }
  };


  struct split_value_to_subformulas_list {
    std::list<subformulas> list_;

    template<typename... A>
    split_value_to_subformulas_list(A&... as) {
      list_ = std::list<subformulas>({std::get<0>(*as.second)...});
    }
  };


  struct split_value_to_variable_set {
    std::set<val<variable>> set_;

    template<typename... A>
    split_value_to_variable_set(A&... as) {
      auto vss = std::list<std::set<val<variable>>>({std::get<2>(*as.second)...});
      for (auto& i: vss)
        set_.insert(i.begin(), i.end());
    }
  };


  template<class B>
  struct split_value_to_formula_tuple {
    B tuple_;

    template<typename... A>
    split_value_to_formula_tuple(A&... as) {
      tuple_ = std::make_tuple(std::get<1>(*as.second)...);
    }
  };


  template<typename... A, class Construct>
  split_formula split(
    const Construct& c, unify_environment ta,
    const val<variable>& x, const val<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl,
    direction dr, A... as) {

    std::list<val<formula>> as1; // For trace_split writing only.

    if (trace_value & trace_split) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);

      as1 = {as...};

      std::clog << "Begin split(";

      bool iter0 = true;

      for (auto& a: as1) {
        if (iter0) iter0 = false;
        else
          std::clog << " : ";

        std::clog << a << std::flush;
      }

      std::clog << "), replacement "
        << x << ", condition: " << t
        << std::endl;
    }


    split_formula sf; // Return value;

    // Make std::tuple<split_formula,...>.
    auto 𝜆0 = [&](const val<formula>& y) {
      split_formula sf = y->split(ta, x, t, tt, dbp, lv, sl, dr);
      // The pair must hold sf, as sf.sequence_.begin() refers to sf.sequence_, false in a copy of sf.
      return std::make_pair(std::move(sf), sf.sequence_.begin());
    };

    std::tuple<A...> tp(as...);
    using argument_tuple_type = decltype(tp);

    auto sfs = std::make_tuple(𝜆0(as)...);
    using sfs_type = decltype(sfs);


    if (trace_value & trace_split) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);

      std::clog << "split(";

      bool iter0 = true;

      for (auto& a: as1) {
        if (iter0) iter0 = false;
        else
          std::clog << " : ";

        std::clog << a;
      }

      std::clog << "), replacement " << x << ", condition: " << t << ":\n";

      std::make_from_tuple<print_sfs>(sfs);

      std::clog << std::endl;
    }


    using Split_type = Split<decltype(sfs), std::tuple_size_v<sfs_type>>;

    for (; !Split_type::is_end(sfs); Split_type::increment(sfs)) {
      auto 𝜆1 = [&](const std::pair<split_formula, split_formula::container_type::iterator>& p) {
        return *p.second;
      };

      std::list<subformulas> fss = std::make_from_tuple<split_value_to_subformulas_list>(sfs).list_;

      subformulas fs;

      for (auto& i: fss)
        fs.append(i);


      argument_tuple_type bs = std::make_from_tuple<split_value_to_formula_tuple<argument_tuple_type>>(sfs).tuple_;

      val<formula> f = std::apply(c, bs);


      std::set<val<variable>> vs = std::make_from_tuple<split_value_to_variable_set>(sfs).set_;


      if (trace_value & trace_split) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);
        std::clog << "  construct ";

        std::make_from_tuple<print_sfs_formulas>(sfs);

        std::clog << std::endl;
        std::clog << "    " << f << "\n  concatenate: " << std::flush;

        bool iter0 = true;

        for (auto& i: fss) {
          if (iter0) iter0 = false;
          else
            std::clog << " + ";

          std::clog << i;
        }

        std::clog << " = " << fs << std::endl;
      }


      if (!!fs)
        sf.push_back(fs, f, vs);
    }

    return sf;
  }


  template<class Construct>
  split_formula split(const val<formula>& a0, const Construct& c, unify_environment ta,
    const val<variable>& x, const val<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl,
    direction dr) {

      return split(c, ta, x, t, tt, dbp, lv, sl, dr, a0);
  }


  template<class Construct>
  split_formula split(const std::tuple<val<formula>, val<formula>>& a, const Construct& c, unify_environment ta,
    const val<variable>& x, const val<formula>& t, unify_environment tt, database* dbp, level lv, degree_pool& sl, direction dr) {

    return split(c, ta, x, t, tt, dbp, lv, sl, dr, std::get<0>(a), std::get<1>(a));
  }

} // namespace mli

