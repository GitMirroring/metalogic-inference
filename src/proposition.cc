/* Copyright (C) 2017, 2021-2023 Hans Åberg.

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

#include "proposition.hh"


namespace mli {

  ref<formula> supposition::rename(level lv, degree sl) const {
    ref<supposition> rp(make, *this);
    rp->statement_ = statement_->rename(lv, sl);
    return rp;
  }


  ref<formula> supposition::add_exception_set(variable_map& vm) const {
    ref<supposition> rp(make, *this);
    rp->statement_ = statement_->add_exception_set(vm);
    return rp;
  }


  ref<formula> supposition::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<supposition> rp(make, *this);
    rp->statement_ = statement_->substitute(s, vt);
    return rp;
  }


  void supposition::declared(std::set<ref<variable>>& vs) const {
    statement_->contains(vs, occurrence::declared);
  }


  void supposition::write(std::ostream& os, write_style ws) const {
    bool show_type = ws & write_type;
    bool show_name = ws & write_name;
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;
    if (show_type)
      switch (type_) {
        case postulate_: {
          if (write_postulate_) { os << "postulate"; break; }

          if (statement_->is_axiom())
            os << "axiom";
          else if (statement_->is_rule())
            os << "rule";
          else
            os << "postulate";

          break;
      }
        case conjecture_:  os << "conjecture"; break;
        case implicit_:  os << "implicit"; break;
      }

    if (show_type && show_name)
      os << " ";

    if (show_name)
      os << name_;

    if ((show_type || show_name) && show_statement)
      os << ". ";

    if (show_statement) {
      std::set<ref<variable>> vs;
      declared(vs);
      write_variable_declaration(vs, os);
      os << "\n  ";
      statement_->write(os, ws);
      os << ".";
    }
  }


  // Implementation of class premise.

  premise::premise() : statement("", ref<implicit_premise>(make)) {}

  premise::premise(size_type k)
   : statement("", ref<implicit_premise>(make)), premise_index_(k), is_component_(true) {}


  premise::premise(const std::string& nm, const ref<formula>& b, varied_type vs, size_type k, bool c) :
    statement(nm, b), premise_index_(k), is_component_(c) {
#if 1
    // If a named premise is created, it comes from a statement indicated
    // in the parser, so its varibles are unspecialized, and will not
    // become specialized, so therefore the variables are specialized here
    // by first making a copy of the variables to make sure it does
    // not interference with the unspecialization in the statements it
    // comes from.
    //
    // When statement specialization is made pure, this code is not needed.
#if 1
    if (b->empty())
      return;
#else
    if (b->empty() || nm.empty())
      return;
#endif

    std::set<ref<variable>> ovs, lvs, fsvs;

    b->contains(ovs, occurrence::not_limited);
    b->contains(lvs, occurrence::limited);
    b->contains(lvs, occurrence::formula_sequence);

    std::set<ref<variable>> lvs1, ovs1;

    // Make copies to avoid mutation corruption:
    for (auto& i: lvs)
      lvs1.insert(i->rename());

    for (auto& i: ovs)
      ovs1.insert(i->rename());

    // Unspecialization is set in the premise, a copy of the body of x:
    statement_->unspecialize(lvs1, false);
    statement_->unspecialize(ovs1, true);

    // Copy and make specializable the varied variables:
    for (auto& i: vs)
      for (auto& j: i.second)
        for (auto& k: j.second) {
          ref<variable> v = k->rename();
          v->unspecializable_ = false;

          // Variables with no free occurrence in the premise are not varied, and removed:
          kleenean kl = b->has(v, occurrence::free);

          if (kl == false)
            continue;

          (varied_)[i.first][j.first].insert(v);
        }
#endif
  }


  alternatives premise::unify(unify_environment tx, const ref<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {

    // Make sure the premise unify_environment gets a separate bound variables table:
    // Mark the unify environment as premise:
    unify_environment tx1(fact, tx.metalevel_);

    metalevel_t xm = metalevel();
#if 0
    // A higher inference metalevel of *this raises the environment metalevel:
    if (xm > tx.metalevel_)
      tx1.metalevel_ = xm;
#endif

    tx1.is_premise_ = true;
    tx1.premise_index_ = premise_index_;
    tx1.conclusion_index_ = tx.conclusion_index_;

    statement_->contains(tx1.premise_variables_, occurrence::limited);

    alternatives as;

    formula_sequence* xsp = ref_cast<formula_sequence*>(statement_);

    if (xsp != nullptr) {
      size_type n = 0;

      for (auto& ix: xsp->formulas_) {
        unify_environment tx2 = tx1;
        tx2.premise_index_ = n;

        alternatives bs = ref<premise>(make, *this, n)->unify(tx2, y, ty, dbp, lv, sl, dr);

        alternatives cs;

        // For alternative, make sure its varied variables are a subset of the inference
        // varied variables, as otherwise the substituion introduces hidden varied variables.
        for (auto& i: bs.alternatives_) {
          std::set<ref<variable>> vs;
          i.substitution_->get_varied(vs, xm);

          bool b = vs.empty();

          if (!b) {
            auto k = varied_.find(0);

            if (k != varied_.end()) {
              auto l = k->second.find(n);

              if (l != k->second.end())
                b = std::includes(l->second.begin(), l->second.end(), vs.begin(), vs.end(), precedes());
            }
          }

          if (!b)
            continue;

          cs.push_back(i);
        }

        as.append(cs);
        ++n;
      }
    }
    else {
      alternatives bs = mli::unify(statement_, tx1, y, ty, dbp, lv, sl, dr);

      // For alternative, make sure its varied variables are a subset of the inference
      // varied variables, as otherwise the substitution introduces hidden varied variables.
      for (auto& i: bs.alternatives_) {
        std::set<ref<variable>> vs;
        i.substitution_->get_varied(vs, xm);

        bool b = vs.empty();

        if (!b) {
          auto k = varied_.find(0);

          if (k != varied_.end()) {
            auto l = k->second.find(premise_index_);

            if (l != k->second.end())
              b = std::includes(l->second.begin(), l->second.end(), vs.begin(), vs.end(), precedes());
          }
        }

        if (!b)
          continue;

        as.push_back(i);
      }

      as = as.label(this, lv);
    }

    return as;
  }


  void premise::unspecialize(depth d, bool b) {
    statement_->unspecialize(d, b);
  }


  void premise::unspecialize(std::set<ref<variable>>& ps, bool b) {
    statement_->unspecialize(ps, b);
  }


  ref<formula> premise::rename(level lv, degree sl) const {
#if 1
    return this;
#else
    premise* rp = this->new_p();
    ref<formula> rt(rp);
    rp->statement_ = statement_->rename(lv, sl);

    for (auto& i: varied_)
      for (auto& j: i.second)
        for (auto& k: j.second)
          (rp->varied_)[i.first][j.first].insert(k->rename(lv, sl));

    return rt;
#endif
  }


  void premise::write(std::ostream& os, write_style ws) const {
    bool show_type = ws & write_type;
    bool show_name = ws & write_name;
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;

    // Even though "premise" is the type, it will always be needed in writeouts, whereas
    // the name of the statement which it belongs is normally not needed.
    // So always write "premise", and add name if both type and name is requested:
    os << "premise";

    if (show_name) {
      if (name_.empty())
        os << " ⊢"; // The name for an implicit premise.
      else
        os << " " << name();

      if (is_component_)
        os << to_index(subscript, premise_index_);
    }

    if ((show_type || show_name) && show_statement)
      os << ". ";

    if (show_statement) {
      std::set<ref<variable>> vs;
      declared(vs);
      write_variable_declaration(vs, os);
      os << "\n  ";
      statement_->write(os, ws);

      if (!varied_.empty()) {

        os << " ⊢⁽";

      bool i0 = true;

      for (auto& i: varied_) {
        if (i0) i0 = false;
        else os << ";";

        if (varied_.size() != 1 || i.first != 0)
          os << to_index(superscript, i.first) << " ";

        bool j0 = true;

        for (auto& j: i.second) {
          if (j0) j0 = false;
          else os << ",";

          if (varied_.size() != 1 || !(i.second.size() == 1 && j.first == 0))
            os << to_index(superscript, j.first) << " ";

          bool k0 = true;

          for (auto& k: j.second) {
            if (k0) k0 = false; else os << " ";
            os << k;
          }
        }
      }

        os << "⁾";
      }
      os << ".";
    }
  }


  // Implementation of class proof_line.

  ref<formula> proof_line::rename(level lv, degree sl) const {
    ref<proof_line> rp(make, *this);
    rp->statement_ = statement_->rename(lv, sl);
    return rp;
  }


  ref<formula> proof_line::add_exception_set(variable_map& vm) const {
    ref<proof_line> rp(make, *this);
    rp->statement_ = statement_->add_exception_set(vm);
    return rp;
  }


  ref<formula> proof_line::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<proof_line> rp(make, *this);
    rp->statement_ = statement_->substitute(s, vt);
    return rp;
  }


  void proof_line::declared(std::set<ref<variable>>& vs) const {
    std::set<ref<variable>> vs0;
    statement_->contains(vs0, occurrence::declared);
    std::set<ref<variable>>::iterator i;
    for (i = vs0.begin(); i != vs0.end(); ++i) {
      const variable* vp = i->data();
      if (vp == 0)  continue;
      if (vp->depth_ == depth_)
        vs.insert(*i);
    }
  }

#define NEW_PROOF 0

  void proof_line::prove(size_type n) {
    if (trace_value & trace_result) {
      std::clog << "Proving ";
      write(std::clog, write_style(write_name | write_statement));
      std::clog << std::flush;
      std::clog << "\n" << std::flush;
    }

    // Make proofline statement variables unspecializable in course of proof:
    // The depth of these variables is one higher than that of the theorem
    // statement variables.
    // The variables are made specializable again after the proof has been written out,
    // to show, if traced, which ones are unspecializable in proof.

#if NEW_PROOF
    // Make an independent copy:
#if 1
    ref<formula> st = this->rename(0, 0);
#else
    // debug-mli
    ref<formula> st = statement_->rename();
#endif

    // Make theorem statement variables unspecializable in course of proof:
    st->unspecialize(depth_, true);

#if 1
    // debug-mli
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "proof_line::prove B0: " << *this << std::endl;
      std::clog << "proof_line::prove B1: " << statement_ << std::endl;
      std::clog << "proof_line::prove B2: " << st << std::endl;
    }
#endif

    proofs_ = mli::prove(st, *database_, n);
    set_strict();

    if (trace_value & trace_result) {
      std::set<ref<variable>> vs;
      st->contains(vs, occurrence::any); // Find variables:
      write_variables(std::clog, write_default, vs);
      std::clog << "\n" << std::flush;
      write_proofs(std::clog, proofs_);
      std::clog << std::endl;
  #if 0
      // One might here show the variables that get new values by the
      // substitutions, but currently, the free variables are unspecialized in proof,
      // though some bound variables will get unspecialized new values.
      // If implemented, the function call should be:
      show_solution(std::clog, write_default, vs, proofs_);
  #endif
    }
#else
    unspecialize(depth_, true);

    proofs_ = mli::prove(this, *database_, n);

    set_strict();

    if (trace_value & trace_result) {
      std::set<ref<variable>> vs;
      statement_->contains(vs, occurrence::any); // Find variables:
      write_variables(std::clog, write_default, vs);
      std::clog << "\n" << std::flush;
      write_proofs(std::clog, proofs_);
      std::clog << std::endl;
  #if 0
      // One might here show the variables that get new values by the
      // substitutions, but currently, the free variables are unspecialized in proof,
      // though some bound variables will get unspecialized new values.
      // If implemented, the function call should be:
      show_solution(std::clog, write_default, vs, proofs_);
  #endif
    }

    unspecialize(depth_, false);
#endif
  }


    kleenean proof_line::is_proved() const {
      if (proofs_.empty())
        return false;

      return (is_strict()? (kleenean)true : undefined);
    }


  void proof_line::set_strict() {
    // The proof line is strict if at least one proofs is:
    strict_ = false;

    for (auto& i: proofs_)
      if (!i.is_conditional()){
        strict_ = true;
        break;
      }
  }


  void proof_line::unspecialize(depth x, bool y) {
    statement_->unspecialize(x, y);
  }


  void proof_line::write(std::ostream& os, write_style ws) const {
    bool show_type = ws & write_type;
    bool show_name = ws & write_name;
    bool show_statement = ws & write_statement;
    bool show_unproved = ws & write_unproved;
    bool show_proof = ws & write_proof;
    int proof_margin = (ws & write_proof_margin_level); // Value with indent.
    if (!(ws & write_proof_indent) && proof_margin > 0)  --proof_margin;
    int proof_tab = (ws & write_proof_margin_tab) >> 4;

    // A proof line named "result" is written as "result by…" without a dot '.'
    // after "result", so it should have its name suppressed.
    // Any proof line can be concluding by holding the statement formula,
    // and if the name is different from "result" it should be shown, though.
    // So only a concluding proof line named "result" should have its
    // name suppressed.
    if (concluding_ && show_statement && name_ == "result")
      show_name = false;
    os << spaces(proof_margin, proof_tab);
    if (show_name)
      os << name_;


    kleenean p = is_proved();

    if (show_unproved && p != true) {
      if (show_name && show_statement)
        os << " ";
      if (show_statement) {
        if (p == undefined)
          os << "[*conditional*]";
        else
          os << "[*unproved*]";
        if (!show_name)  os << " "; // Because no "." will be output.
      }
    }

    if (show_name && show_statement)
      os << ". ";
    if (show_statement) {
      // For a concluding proof line, name_ is currently "conclusion" or "result",
      // so use that, rather than the concluding_ variable alone:
      if (concluding_ && (name_ == "conclusion" || name_ == "result"))
        os << name_;
      else {
        // An ordinarily named proof line can become
        if (concluding_)
          os << "[*concluding*] ";
        std::set<ref<variable>> vs;
        declared(vs);
        if (!vs.empty()) {
          write_variable_declaration(vs, os);
          os << "\n  ";
          os << spaces(proof_margin, proof_tab);
        }
        os << statement_;
      }
      if (show_proof && !database_->empty()) {
        os << " by ";
        database_->write(os, write_style(write_name));
      }

      os << ".";

      if (ws & write_proof)
        if (proofs_.size() == 1) {
          os << " — ";
          if (proofs_.front().is_conditional())
            os << "[*conditional*] ";
          proofs_.front().write(os, write_style(write_name));
          os << ".";
        }
        else
          for (auto& i: proofs_) {
            os << spaces(proof_margin, proof_tab);
            os << "\n— ";
            if (i.is_conditional())
              os << "[*conditional*] ";
            i.write(os, write_style(write_name));
            os << ".";
          }
    }
  }


  // Implementation of class theorem.

  ref<formula> theorem::rename(level lv, degree sl) const {
    ref<theorem> rp(make, *this);
    rp->statement_ = statement_->rename(lv, sl);
    return rp;
  }


  ref<formula> theorem::add_exception_set(variable_map& vm) const {
    ref<theorem> rp(make, *this);
    rp->statement_ = statement_->add_exception_set(vm);
    return rp;
  }


  ref<formula> theorem::substitute(const ref<substitution>& s, substitute_environment vt) const {
    ref<theorem> rp(make, *this);
    rp->statement_ = statement_->substitute(s, vt);
    return rp;
  }


  void theorem::declared(std::set<ref<variable>>& vs) const {
    std::set<ref<variable>> vs0;
    statement_->contains(vs0, occurrence::declared);
    std::set<ref<variable>>::iterator i;
    for (i = vs0.begin(); i != vs0.end(); ++i) {
      const variable* vp = i->data();
      if (vp == 0)  continue;
      if (vp->depth_ == depth_)
        vs.insert(*i);
    }
  }

#define NEW_UNSPECIALIZABLE 1
#define NEW_PROVE 0 // Cf. NEW_PROOF above.

  // The theorem is proved if it has a successful, non-empty proof,
  // where the last proved formula is the one of the theorem conclusion.
  // This assumes that each line of the proof is proved by axioms,
  // premises of the theorem conclusion, and earlier proved formulas
  // of the proof.
  void theorem::prove(size_type n) {
    if (trace_value & trace_result) {
      std::clog << "\nProving ";
      write(std::clog, write_style(write_name | write_type | write_statement));
      std::clog << "\n" << std::flush;
    }

    proved_lines_ = 0;
    proved_all_ = false;
    bool successful_so_far = true; // Detects if one proof line is failing;

#if NEW_PROVE
    // Make an independent copy:
    ref<formula> st = statement_->rename();

    // Make theorem statement variables unspecializable in course of proof:
    st->unspecialize(depth_, true);

    // debug-mli
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::cout << "theorem::prove B0: " << *this << std::endl;
      std::cout << "theorem::prove B1: " << statement_ << std::endl;
      std::cout << "theorem::prove B2: " << st << std::endl;
    }
#endif

#if 1 // debug.hh
    // Make theorem statement variables unspecializable in course of proof:
    unspecialize(depth_, true);
#endif


#if 0
    // Make an independent copy of proof lines:
    proof_list_type pls;

    for (auto& i: proof_lines_) {
      pls.push_back(i->rename());
      pls.back()->unspecialize(depth_, true);
    }

    iterator i, i0 = pls.begin(), i1 = pls.end();
    iterator j = proof_lines_.begin();

    for (i = i0; i != i1; ++i, ++j) {
      if (!(*i)->prove(n))
        successful_so_far = false;

      // Count the number of proved concluding proof lines, which can be 0 or more:
      proof_line* plp = ref_cast<proof_line*>(*i);
      if (plp != 0 && plp->concluding() && plp->is_proved())
        proved_lines_ += 1;

      ref_cast<proof_line*>(*j)->proofs_ = plp->proofs_;
    }
#else

#if 0
    if (proof_lines_.empty()) {
      proofs_ = database_->prove(statement_, n);
      if (!proofs_())
        proved_lines_ += 1;
    }
    else
#endif

    // Set the strict value to true if there is at least one strict proof:
    strict_ = false;

    for (auto& i: proof_lines_) {
#if NEW_PROVE
      ref<statement> pl = i->rename();

      pl->prove(n);
      if (pl->is_proved() == false)
        successful_so_far = false;

      // Count the number of proved concluding proof lines, and
      // the total number of proofs, which can be higher than one per proof line:
      proof_line* plp = ref_cast<proof_line*>(pl);
#else
      i->prove(n);
      if (i->is_proved() == false)
        successful_so_far = false;

      // Count the number of proved concluding proof lines, and
      // the total number of proofs, which can be higher than one per proof line:
      proof_line* plp = ref_cast<proof_line*>(i);
#endif

      if (plp != nullptr && plp->concluding()) {
        size_t k = plp->proofs_.size();
        proved_lines_ += (k > 0);
        proof_count_ += k;
        if (plp->is_proved() == true)
          strict_ = true;
      }
    }
#endif

#if 1 // debug.hh
    unspecialize(depth_, false);
#endif

    proved_all_ = successful_so_far;
  }


  kleenean theorem::is_proved() const {
    if (proved_lines_ == 0)
      return false;

    return (is_strict()? (kleenean)true : undefined);
  }


  void theorem::unspecialize(depth x, bool y) {
    // It is necessary to unspecialize the statement itself for the correct
    // labelling in the writeout of the proof, though not for
    // the correct proof, as the concluding proof lines hold their own copy
    // and do not directly reference the statement.
    // But the implementation is not entirely pure, as the proof lines
    // can hold a reference, not a copy, to variables in the statement.
    // If that happens, the statement variables will be specializable again
    // when the corresponding proof line become specializable again.
#if 1
    statement_->unspecialize(x, y);
#endif

#if 0 // debug.hh
    std::cout << "theorem::unspecialize:\n" << *this << "\n"; // debug.hh
#endif

#if 0 // debug.hh
    // Only unspecialize the variable unspecialized in the statement:
    std::set<ref<variable>> vs;
    statement_->contains(vs, occurrence::unspecialized);

#if 0 // debug.hh
    std::cout << "R(" << x << ") ";
    for (auto i: vs)
      std::cout << i << " ";
    std::cout << std::endl;
#endif

    iterator i, i0 = proof_lines_.begin(), i1 = proof_lines_.end();
    for (i = i0; i != i1; ++i) {
      (*i)->unspecialize(vs, y);
    }

#if 0 // debug.hh
    std::cout << "S(" << x << "):\n";
    for (auto i: proof_lines_)
      std::cout << i << "\n";
    std::cout << std::flush;
#endif

#else
    for (auto& i: proof_lines_)
      i->unspecialize(x, y);
#endif
  }


  void theorem::write(std::ostream& os, write_style ws) const {
    bool show_type = ws & write_type;
    bool show_name = ws & write_name;
    bool show_statement = ws & write_statement;
    bool show_unproved = ws & write_unproved;
    bool show_proof = ws & write_proof;

    int proof_margin = (ws & write_proof_margin_level);
    int proof_tab = (ws & write_proof_margin_tab) >> 4;
    int new_proof_margin = (proof_margin < 15)? proof_margin + 1 : proof_margin;
    write_style new_ws = write_style(new_proof_margin | (ws & ~write_proof_margin_level));

    os << spaces(proof_margin, proof_tab);
    if (show_type) 
      switch (type_) {
        case lemma_:       os << "lemma"; break;
        case proposition_: os << "proposition"; break;
        case theorem_:     os << "theorem"; break;
        case corollary_:   os << "corollary"; break;
        case claim_:       os << ""; break; // Explicit "claim" is deprecated.
      };
    if (show_type && show_name && type_ != claim_)
      os << " ";
    if (show_name)
      os << name_;

    kleenean p = is_proved();

    if (show_unproved && p != true) {
      if ((show_type || show_name) && show_statement)
        os << " ";
      if (show_statement){
        if (p == undefined)
          os << "[*conditional*]";
        else
          os << "[*unproved*]";
      }
    }

    if ((show_type || write_name) && show_statement)
      os << ". ";

    if (show_statement) {
      std::set<ref<variable>> vs;
      declared(vs);
      if (!vs.empty()) {
        write_variable_declaration(vs, os);
        os << "\n  ";
        if (type_ == claim_)
          os << spaces(proof_margin, proof_tab);
      }
      statement_->write(os, ws);
    }

    if (show_statement && show_proof)
      os << "\n";

    if (show_proof) {
      if (proof_lines_.empty()) {
        os << spaces(proof_margin, proof_tab) << "∎";
        return;
      }

      if (proof_lines_.size() == 1) {
        proof_line* plp = ref_cast<proof_line*>(proof_lines_.back());

        if (plp != 0 && plp->concluding()) {
          os << spaces(proof_margin, proof_tab) << proof_lines_.front();
          return;
        }
      }

      // Writing compound proof of more than one proof line:

      os << spaces(proof_margin, proof_tab) << "proof\n";

      const_iterator i, i0 = proof_lines_.begin(), i1 = proof_lines_.end();
      for (i = i0; i != i1; ++i) {
        if (i != i0)  os << "\n";
        (*i)->write(os, new_ws);
      }

      proof_line* plp = ref_cast<proof_line*>(proof_lines_.back());

      if (plp == 0 || !plp->concluding()) {
        os << "\n" << spaces(proof_margin, proof_tab);
        os << "[* Last proof line is not concluding, thus unused in proof. *]";
      }

      if (concluding_ == 0) {
        os << "\n" << spaces(proof_margin, proof_tab);
        os << "[* No concluding proof line. *]";
      }
      else {
        if (concluding_ > 1) {
          os << "\n" << spaces(proof_margin, proof_tab);
          os << "[* Number of concluding proof lines: " << std::to_string(concluding_) << ", ";
          if (proved_lines_ == concluding_)
            os << "all proved";
          else
            os << std::to_string(proved_lines_) << " proved";
          os << ". *]";
        }

        if (proved_lines_ != proof_count_) {
          os << "\n" << spaces(proof_margin, proof_tab);
          os << "[* Number of proofs of the concluding proof lines: " << std::to_string(proof_count_) << " *]";
        }
      }

      if (!is_proved() == false && !proved_all_) {
        os << "\n" << spaces(proof_margin, proof_tab);
        os << "[* Statement is ";
        if (is_proved() == undefined)
          os << "conditionally ";
        os << "proved, but some proof lines are unproved. *]";
      }

      os << "\n" << spaces(proof_margin, proof_tab);
      os << "∎";
    }
  }


  // Implementation of class statement_substitution.

  void statement_substitution::write(std::ostream& os, write_style ws) const {
  #if 1
    write_style show_type_name = write_style(ws & (write_name | write_type));
    bool show_statement = ws & write_statement;
    if (show_type_name) {
      statement_->write(os, write_style(write_name | write_type));
      substitution_->write(os, ws);
    }
    if (show_type_name && show_statement)
      os << ". ";
    if (show_statement)
      statement_->write(os, ws);
    if (show_type_name && show_statement)
      os << ".";
  #else
    statement_.write(os, ws);
    substitution_.write(os, ws);
  #endif
  }

} // namespace mli

