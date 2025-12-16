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


namespace mli {

  class abbreviation : public nonempty_formula {
    precedence_t precedence_;
  public:
    // defined_ ≔ definer_; definiendum ≔ definiens.
    val<formula> defined_;    // Definiendum, what is defined.
    val<formula> definer_;    // Definiens, what defines.
    val<formula> condition_;  // condition_ ⊢ x ≔ y.

    formula::type type_ = formula::logic;

    // The parameters, i.e., the variables that in A ≔ B only occur in B, and not in A.
    // These should be unspecializable in proof as to not generate faulty proofs.
    // For example, in an induction, writing
    //   definition d. predicate 𝐴  term 𝒙, 𝒚. 𝐴(𝒚) ≔ 𝒙 + 𝒚 = 𝒚 + 𝒙.
    // a proof of the statement 𝐴(𝒚) will allow 𝒙 to be set to say 0 if not 𝒙 is held
    // unspecializable, resulting in an unintended proof of the more special 0 + 𝒚 = 𝒚 + 0.
    std::set<val<variable>> parameters_;


    abbreviation() = default;

    new_copy(abbreviation);
    new_move(abbreviation);


    abbreviation(const val<formula>& x, const val<formula>& y, const val<formula>& c,
      formula::type t, const precedence_t& p)
     : defined_(x), definer_(y), condition_(c), type_(t), precedence_(p) {
      parameters(parameters_);
    }

    // Find the parameters, i.e., the variables that in A ≔ B only occur in B, and not in A.
    void parameters(std::set<val<variable>>& ps) {
      definer_->contains(ps, occurrence::declared);
      std::set<val<variable>> vs;
      defined_->contains(vs, occurrence::declared);
      for (auto& i: vs)
        ps.erase(i);
    }

    void set(formula::type t) { type_ = t; }
    void set(precedence_t p) { precedence_ = p; }

    virtual formula::type get_formula_type() const { return type_; }

    virtual alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;  

    // An abbreviation D, given by A ≔ B, unifies by
    //   u_D(x, y) ⤳ u(x, A)*u(B, y)|u(A, y)*u(x, B)
    virtual alternatives unify(const val<formula>& x, unify_environment tx, const val<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const override;


    virtual kleenean has(const val<variable>&, occurrence) const;
    virtual void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const;

    virtual kleenean free_for(const val<formula>& f, const val<variable>& x, 
      std::set<val<variable>>& s, std::list<val<variable>>& bs) const;

    void unspecialize(depth, bool) override;
    void unspecialize(std::set<val<variable>>&, bool) override;

    virtual val<formula> rename(level, degree) const;
    virtual val<formula> add_exception_set(variable_map&) const override;
    virtual val<formula> substitute(const val<substitution>&, substitute_environment) const;

    virtual void set_bind(bind&, name_variable_table&);

    virtual order compare(const unit&) const;

    virtual precedence_t precedence() const { return precedence_; }
    virtual void write(std::ostream&, write_style) const;
  };


  class definition : public statement {
  public:
    definition() = default;

    new_copy(definition);
    new_move(definition);

    definition(const std::string& name, const val<abbreviation>& d)
     : statement(name, d) {}

    virtual statement_type get_statement_type() const { return a_definition; }

    virtual alternatives unify(const val<formula>& x, unify_environment tx, const val<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const override;

    // Proving & solving.
    virtual kleenean is_proved() const override { return true; }

    virtual void write(std::ostream&, write_style) const;
  };

} // namespace mli


