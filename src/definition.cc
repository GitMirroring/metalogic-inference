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

#include "definition.hh"

#include "substitution.hh"


namespace mli {

  alternatives abbreviation::unify(unify_environment tt, const val<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    // Change this stuff: Obsolete.
    // Should probably unify as a tuple, as other data.
    // Include condition_.
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "abbreviation::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    alternatives as;
    alternatives bs = mli::unify(defined_, tt, x, tx, dbp, lv, sl, dr);

    as = as.append(bs.add_goal(definer_));
    bs = mli::unify(definer_, tt, x, tx, dbp, lv, sl, dr);
    as = as.append(bs.add_goal(defined_));

    return as;
  }


  alternatives abbreviation::unify(const val<formula>& x, unify_environment tx, const val<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {

   if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "abbreviation::unify(\n  " << x << ";\n  " << y << ") in ";
      write(std::clog, write_style(write_name));
      std::clog << std::endl;
    }

    val<formula> d0 = defined_->rename();
    val<formula> d1 = definer_->rename();

    // Make the abbreviation parameters unspecializable when x is a goal,
    // and specializable again for reuse of the abbreviation in further attempts:
    if (tx.target_ == goal) {
#if 1
      d0->unspecialize(const_cast<std::set<val<variable>>&>(parameters_), true);
      d1->unspecialize(const_cast<std::set<val<variable>>&>(parameters_), true);
#else
      const_cast<abbreviation&>(*this).unspecialize(const_cast<std::set<val<variable>>&>(parameters_), true);
#endif

#if 0 // debug.hh
    std::clog << "abbreviation::unify A: " << d0 << " ≔ " << d1 << std::endl;
    std::clog << "u(" << x << ", " << y << ")" << std::endl;
    std::clog << "u(" << x << ", " << d0 << "): ";
    std::clog << mli::unify(x, tx, d0, ty, dbp, lv, sl, dr, no_expand) << std::endl;

    for (auto i: parameters_)
      std::clog << i << " ";
    std::clog << std::endl;
#endif
    }


    // Abbreviations (definitions) unify in top level environment with respect to
    // bound variables. For example, the abbreviation B(t) ≔ 0 + t = t that should unify
    // with A(x) in ∀x A(x), should not have ∀x in its bound variable table.
    tx.table_.clear();
    ty.table_.clear();
    tx.excluded1_.clear();
    ty.excluded1_.clear();


    // Expand abbreviation only in argument x:
    //   u_0(x, d0)*u_0(d1, y).
    // Redundancy, proof duplicates, if 'expand' instead of 'no_expand' used in u(d1, y):
    alternatives as
      = mli::unify(x, tx, d0, ty, dbp, lv, sl, dr, no_expand).unify(d1, tx, y, ty, dbp, lv, sl, dr, no_expand);
#if 0
    // Make the abbreviation parameters specializable again when x is a goal:
    if (tx.target_ == goal && as.empty())
      const_cast<abbreviation&>(*this).unspecialize(const_cast<std::set<val<variable>>&>(parameters_), false);
#endif
    return as.add_goal(condition_);
  }


  void abbreviation::contains(std::set<val<variable>>& s, std::set<val<variable>>& bs, bool& more, occurrence oc) const {
    defined_->contains(s, bs, more, oc);
    definer_->contains(s, bs, more, oc);
    condition_->contains(s, bs, more, oc);
  }


  kleenean abbreviation::has(const val<variable>& v, occurrence oc) const {
    kleenean k1 = defined_->has(v, oc);
    if (k1 == true)  return true;
    kleenean k2 = definer_->has(v, oc);
    if (k2 == true)  return true;
    kleenean k3 = condition_->has(v, oc);
    return k1 || k2 || k3;
  }


  kleenean abbreviation::free_for(const val<formula>& f, const val<variable>& x,
    std::set<val<variable>>& s, std::list<val<variable>>& bs) const {
    kleenean k1 = defined_->free_for(f, x, s, bs);
    if (k1 == false)  return false;
    kleenean k2 = definer_->free_for(f, x, s, bs);
    if (k2 == false)  return false;
    kleenean k3 = condition_->free_for(f, x, s, bs);
    return k1 && k2 && k3;
  }


  void abbreviation::unspecialize(depth x, bool y) {
    defined_->unspecialize(x, y);
    definer_->unspecialize(x, y);
    condition_->unspecialize(x, y);
  }


  void abbreviation::unspecialize(std::set<val<variable>>& vs, bool b) {
    defined_->unspecialize(vs, b);
    definer_->unspecialize(vs, b);
    condition_->unspecialize(vs, b);
  }


  val<formula> abbreviation::rename(level lv, degree sl) const {
    val<abbreviation> fp(make, *this);
    fp->defined_ = defined_->rename(lv, sl);
    fp->definer_ = definer_->rename(lv, sl);
    fp->condition_ = condition_->rename(lv, sl);

    fp->parameters_.clear();
    fp->parameters(fp->parameters_);

    return fp;
  }


  val<formula> abbreviation::add_exception_set(variable_map& vm) const {
    val<abbreviation> fp(make, *this);
    fp->defined_ = defined_->add_exception_set(vm);
    fp->definer_ = definer_->add_exception_set(vm);
    fp->condition_ = condition_->add_exception_set(vm);

    fp->parameters_.clear();
    fp->parameters(fp->parameters_);

    return fp;
  }


  val<formula> abbreviation::substitute(const val<substitution>& s, substitute_environment vt) const {
    val<abbreviation> fp(make, *this);
    fp->defined_ = defined_->substitute(s, vt);
    fp->definer_ = definer_->substitute(s, vt);
    fp->condition_ = condition_->substitute(s, vt);

    fp->parameters_.clear();
    fp->parameters(fp->parameters_);

    return fp;
  }


  void abbreviation::set_bind(bind& b, name_variable_table& vt) {
    defined_->set_bind(b, vt);
    definer_->set_bind(b, vt);
    condition_->set_bind(b, vt);
  }


  order abbreviation::compare(const unit& x) const {
    auto& xr = dynamic_cast<const abbreviation&>(x);
#if (__cplusplus > 201703L) // C++20
    order c = defined_ <=> xr.defined_;
    if (c != equal)  return c;
    c = definer_ <=> xr.definer_;
    if (c != equal)  return c;
    return condition_ <=> xr.condition_;
#else
    order c = mli::compare(defined_, xr.defined_);
    if (c != equal)  return c;
    c = mli::compare(definer_, xr.definer_);
    if (c != equal)  return c;
    return mli::compare(condition_, xr.condition_);
#endif
  }


  void abbreviation::write(std::ostream& os, write_style) const {
    if (!condition_->empty())
      os << condition_ << " ⊢ ";

    if (precedence().argument(first, defined_->precedence()))
      os << "(" << defined_ << ")";
    else
      os << defined_;

    os << " ≔";

    if (!parameters_.empty()) {
      os << "₍";

      bool it0 = true;

      for (auto& i: parameters_) {
        if (it0)  it0 = false;
        else      os << ",";
        os << i;
      }
      os << "₎";
    }

    os << " ";

    if (precedence().argument(last, definer_->precedence()))
      os << "(" << definer_ << ")";
    else
      os << definer_;
  }


  alternatives definition::unify(const val<formula>& x, unify_environment tx, const val<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {

   if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "definition::unify(\n  " << x << ";\n  " << y << ") in ";
      write(std::clog, write_style(write_name));
      std::clog << std::endl;
    }

    degree dg = sl.get();

    if (sublevel_max != 0 && dg > sublevel_max)
      throw std::runtime_error("Too high degree in definition::unify.");

    // When A::unify(x, tx, y, ty, dbp, lv, sl, dr) is in A = formula,
    // then this cast is not necessary:
    val<statement> nd = val<statement>(rename(lv, dg));
    val<formula> f = nd->get_formula();
    abbreviation& di = dyn_cast<abbreviation&>(f);

    alternatives as;
    as = di.unify(x, tx, y, ty, dbp, lv, sl, dr).label(nd, lv, dg);

    // Unused definition degrees are reused:
    if (as.empty())
      sl.put_back(dg);

    return as;
  }


  void definition::write(std::ostream& os, write_style ws) const {
    bool show_type = ws & write_type;
    bool show_name = ws & write_name;
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;
    int proof_margin = (ws & write_proof_margin_level); // Value with indent.
    if (!(ws & write_proof_indent) && proof_margin > 0)  --proof_margin;
    int proof_tab = (ws & write_proof_margin_tab) >> 4;
    os << spaces(proof_margin, proof_tab);
    if (show_type)
      os << "definition";
    if (show_type && show_name)
      os << " ";
    if (show_name) 
      os << name_;
    if ((show_type || show_name) && show_statement)
      os << ". ";
    if (show_statement) {
      std::set<val<variable>> vs;
      declared(vs);
      write_variable_declaration(vs, os);
      os << "\n";
      os << spaces(proof_margin+1, proof_tab);
      statement_->write(os, ws);
      os << ".";
    }
  }


} // namespace mli
