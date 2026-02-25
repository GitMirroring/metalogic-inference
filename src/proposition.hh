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

#include "substitution.hh"
#include "database.hh"


namespace mli {

  class supposition : public statement {
  public:
    enum type { postulate_, conjecture_, implicit_ };
    type type_ = postulate_;
    
    bool write_postulate_ = false;

    supposition() : type_(postulate_) {}

    new_copy(supposition);
    new_move(supposition);

    supposition(type tp, const std::string& name, const val<formula>& st, bool wp = false)
     : type_(tp), statement(name, st), write_postulate_(wp) {}

    virtual val<formula> rename(level, degree) const;
    virtual val<formula> add_exception_set(variable_map&) const override;
    virtual val<formula> substitute(const val<substitution>&, substitute_environment) const;

    virtual void declared(std::set<val<variable>>&) const;
      
    // Statement access:
    virtual statement_type get_statement_type() const { return a_proposition; }

    // Proving & solving.
    virtual kleenean is_proved() const override { return (type_ == postulate_); }

    virtual void unspecialize(depth d, bool b) { statement_->unspecialize(d, b); }

    // Variable renumbering:
    virtual void set_bind(bind& b, name_variable_table& vs) { statement_->set_bind(b, vs); }

    virtual void write(std::ostream&, write_style) const;
  };


  class implicit_premise : public nonempty_formula {
  public:
    new_copy(implicit_premise);
    new_move(implicit_premise);

    virtual void write(std::ostream& os, write_style) const override
    { os << ". ⊢"; }
  };


  class premise : public statement {
  public:
    bool is_component_ = false;

    size_type premise_index_ = 0;
    size_type conclusion_index_ = 0;

    varied_type varied_;


    // Creates an implicit premise which only unifies with itself.
    // By contrast, premise({}) = premise(val<formula>()) creates an implicit premise
    // of an empty formula, which may unify with formula sequence variables and inferences,
    // that latter by unifying its head against its body.
    premise();
    premise(size_type);


    // Delegating constructor:
    // The limited variables of the body are made specializable and independent
    // (semantically distinct) from the original; ordinary variables kept unchanged.
    //   nm  name to be used, empty for an implict premise
    //   b   the full body or the part (formula sequence component) to be used
    // The premise is unindexed if c is false, and if c is true, k is the formula sequence index.
    premise(const std::string& nm, const val<formula>& b, varied_type vs, size_type k = 0, bool c = false);


    // The following constructors name from statement when applicable; otherwise,
    // an implicit premise is created:

    // Uses the full body of the inference as premise.
    premise(const val<formula>& x)
     : premise(x->name(), x->body()->rename(), dyn_cast<inference&>(x->get_formula()).varied_) {}

    // Uses the inference body formula sequence component k as premise.
    premise(const val<formula>& x, size_type k)
     : premise(x->name(), x->body()->get_formula(k)->rename(), dyn_cast<inference&>(x->get_formula()).varied_, k, true) {}


    premise(const premise& x, size_type k)
     : premise(x.name(), x.get_formula(k), x.varied_, k, true) {}



    new_copy(premise);
    new_move(premise);

    virtual alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const override;

    void unspecialize(depth d, bool b) override;
    void unspecialize(std::set<val<variable>>& ps, bool b) override;

    val<formula> rename(level = 0, degree = 0) const override;

    // False if an explictly given premise, and true when a marker for expanding an
    // implicitly given premise. The premise is implicit exactly when the name is empty.
    // So return true exactly when the name is non-empty.
    bool expand_premise(level) const override { return name().empty(); }

    // Proving & solving.
    virtual kleenean is_proved() const override { return true; }

    virtual void write(std::ostream&, write_style) const;
  };


  class proof_line : public statement {
  public:
    val<database> database_;    // Database to be used when proving formula_.
    bool concluding_;           // True if formula_ is theorem result or conclusion, otherwise false.
    depth depth_;               // Proof/(sub)theorem nesting depth.
    std::list<proof> proofs_;   // Found proofs.
    bool strict_ = false;       // True if at least one proof is strict.


    proof_line() : depth_(0) {}

    new_copy(proof_line);
    new_move(proof_line);

    proof_line(const std::string& name, const val<formula>& f, const val<database>& d,
      bool concluding, depth dp)
     : statement(name, f), database_(d),
       concluding_(concluding), depth_(dp) {}

    virtual val<formula> rename(level, degree) const;
    virtual val<formula> add_exception_set(variable_map&) const override;
    virtual val<formula> substitute(const val<substitution>&, substitute_environment) const;

    virtual void declared(std::set<val<variable>>&) const;

    bool concluding() const { return concluding_; }

    // Statement access:
    virtual statement_type get_statement_type() const { return a_proposition; }

    // Proving & solving.
    virtual void prove(size_type n) override;
    virtual kleenean is_proved() const override;

    void set_strict();

    bool is_strict() const { return strict_; }

    virtual void unspecialize(depth, bool);

    virtual void write(std::ostream&, write_style) const;
  };


  class theorem : public statement {
  public:
    using proof_list_type = std::list<ref4<statement>>;
    using size_type = proof_list_type::size_type;
    using iterator = proof_list_type::iterator;
    using const_iterator = proof_list_type::const_iterator;

    enum type { lemma_, proposition_, theorem_, corollary_, claim_ };

    type type_ = theorem_;          // Type: theorem, lemma etc.
    val<database> theory_;          // Theory used, with axioms and proved statements.
    proof_list_type proof_lines_;   // Proof.

    size_t concluding_ = 0;       // Count of concluding proof lines, which may or may not be proved.
    size_t proved_lines_ = 0;     // Count of proved concluding proof lines.
    size_t proof_count_ = 0;      // Total number of concluding proofs; can be higher than one per proof line.
    bool proved_all_ = false;     // True if all subproofs successfully proved; otherwise false.
    depth depth_ = 0;             // Proof/(sub)theorem nesting depth.
    bool strict_ = false;         // True if at least one proof is strict.

    theorem() {}

    new_copy(theorem);
    new_move(theorem);

    theorem(type tp, const std::string& name, 
      const val<formula>& st, const ref1<theory>& th, depth dp)
     : type_(tp), statement(name, st), theory_(th), depth_(dp) {}

    virtual val<formula> rename(level, degree) const;
    virtual val<formula> add_exception_set(variable_map&) const override;
    virtual val<formula> substitute(const val<substitution>&, substitute_environment) const;

    virtual void declared(std::set<val<variable>>&) const;

    val<database> get_theory() const { return theory_; }
    
    // Append a proof line with no local variables, which is also the return value:
    ref4<statement> push_back(const std::string& name, const val<formula>& f, const val<database>& d,
        bool concluding, depth dp) {
      ref4<statement> st = val<proof_line>(make, name, f, d, concluding, dp);
      proof_lines_.push_back(st);
      if (concluding) concluding_ += 1;
      return st;
    }
      
    // Append a statement, like a substatement with proof:
    ref4<statement> push_back(const ref4<statement>& st)  {
      proof_lines_.push_back(st);
      return st;
    }

    virtual statement_type get_statement_type() const { return a_proposition; }

    virtual void prove(size_type n) override;
    virtual kleenean is_proved() const override;

    bool is_strict() const { return strict_; }

    virtual void unspecialize(depth, bool);

    virtual void write(std::ostream&, write_style) const;
  };


  class statement_substitution : public statement {
  public:
    ref4<statement> statement_;
    val<substitution> substitution_;

    statement_substitution() = default;

    new_copy(statement_substitution);
    new_move(statement_substitution);

    statement_substitution(const ref4<statement>& p, const val<substitution>& s)
     : statement_(p), substitution_(s) { statement_->formula::set_bind(); }

    virtual void declared(std::set<val<variable>>& vs) const { statement_->declared(vs); }

    virtual statement_type get_statement_type() const { return a_proposition; }

    virtual void prove(size_type n) override { statement_->prove(n); }
    virtual kleenean is_proved() const override { return statement_->is_proved(); }

    virtual void unspecialize(depth d, bool b) { statement_->unspecialize(d, b); }

    // Variable renumbering:
    virtual void set_bind(bind& b, name_variable_table& vs) { statement_->set_bind(b, vs); substitution_->set_bind(b, vs); }

    virtual void write(std::ostream&, write_style) const;
  };

} // namespace mli


