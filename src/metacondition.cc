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

#include "metacondition.hh"

#include "substitution.hh"
#include "precedence.hh"


namespace mli {

  alternatives metanot::unify(unify_environment tt, const val<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "metanot::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    metanot* xp = dyn_cast<metanot*>(x);
    if (xp != 0)
      // Both *this and x are metanot. So simply discard the metanot in unification:
      return mli::unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
    // Now, x is a not a metanot object.
    database* dp = dyn_cast<database*>(x);
    if (dp != 0)  // Don't try to unify with a database, as it will do it.
      return O;
    alternatives as = mli::unify(formula_, tt, x, tx, dbp, lv, sl, dr);
    return (as.empty())? I : O;
  }


  kleenean metanot::has(const val<variable>& v, occurrence oc) const {
    return formula_->has(v, oc);
  }


  void metanot::contains(std::set<val<variable>>& s, std::set<val<variable>>& bs, bool& more, occurrence oc) const {
    formula_->contains(s, bs, more, oc);
  }


  kleenean metanot::free_for(const val<formula>& f, const val<variable>& x,
    std::set<val<variable>>& s, std::list<val<variable>>& bs) const {
    return formula_->free_for(f, x, s, bs);
  }


  void metanot::unspecialize(depth x, bool y) {
    formula_->unspecialize(x, y);
  }


  void metanot::unspecialize(std::set<val<variable>>& vs, bool b) {
    formula_->unspecialize(vs, b);
  }


  val<formula> metanot::rename(level lv, degree sl) const {
    val<metanot> mp(make, *this);
    mp->formula_ = formula_->rename(lv, sl);
    return mp;
  }


  val<formula> metanot::add_exception_set(variable_map& vm) const {
    val<metanot> mp(make, *this);
    mp->formula_ = formula_->add_exception_set(vm);
    return mp;
  }


  val<formula> metanot::substitute(const val<substitution>& s, substitute_environment vt) const {
    val<formula> sf = formula_->substitute(s, vt);
    succeed_fail* sfp = dyn_cast<succeed_fail*>(sf);
    if (sfp != 0)
      return val<succeed_fail>(make, !sfp->succeed_);
    return val<metanot>(make, sf);
  }


  void metanot::set_bind(bind& b, name_variable_table& vt) {
    formula_->set_bind(b, vt);
  }


  order metanot::compare(const unit& x) const {
    auto& xr = dynamic_cast<const metanot&>(x);
#if (__cplusplus > 201703L) // C++20
    return formula_ <=> xr.formula_;
#else
    return mli::compare(formula_, xr.formula_);
#endif
  }


  precedence_t metanot::precedence() const {
    return metanot_oprec;
  }


  void metanot::write(std::ostream& os, write_style ws) const {
    os << "~";

    bool do_bracket = precedence().argument(last, formula_->precedence());

    if (do_bracket)  os << "(";
    formula_->write(os, ws);
    if (do_bracket)  os << ")";
  }


  alternatives succeed_fail::unify(unify_environment, const val<formula>& x, unify_environment, database*, level, degree_pool&, direction) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "succeed_fail::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    succeed_fail* xp = dyn_cast<succeed_fail*>(x);
    if (xp == nullptr)  return O;
    return succeed_ == xp->succeed_? I : O;
  }


  val<formula> succeed_fail::substitute(const val<substitution>&, substitute_environment) const {
    return *this;
  }


  order succeed_fail::compare(const unit& x) const {
    auto& xr = dynamic_cast<const succeed_fail&>(x);
#if (__cplusplus > 201703L) // C++20
    return succeed_ <=> xr.succeed_;
#else
    return order(succeed_, xr.succeed_);
#endif
  }


  precedence_t succeed_fail::precedence() const {
    return precedence_t();
  }


  void succeed_fail::write(std::ostream& os, write_style) const {
    if (succeed_)  os << "succeed";
    else  os << "fail";
  }


  alternatives identical::unify(unify_environment, const val<formula>& x, unify_environment, database*, level, degree_pool&, direction) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "identical::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    identical* xp = dyn_cast<identical*>(x);
    if (xp == 0)  return O;
    if (positive_ != xp->positive_)  return O;
    if (positive_)
      return first_ == second_? I : O;
    return first_ != second_? I : O;
  }


  kleenean identical::has(const val<variable>& v, occurrence oc) const {
    kleenean k1 = first_->has(v, oc);
    if (k1 == true)  return true;

    kleenean k2 = second_->has(v, oc);

    return k1 || k2;
  }


  void identical::contains(std::set<val<variable>>& s, std::set<val<variable>>& bs, bool& more, occurrence oc) const {
    first_->contains(s, bs, more, oc);
    second_->contains(s, bs, more, oc);
  }


  kleenean identical::free_for(const val<formula>& f, const val<variable>& x,
    std::set<val<variable>>& s, std::list<val<variable>>& bs) const {
    kleenean k1 = first_->free_for(f, x, s, bs);
    if (k1 == false)  return false;
    kleenean k2 = second_->free_for(f, x, s, bs);
    return k1 && k2;
  }


  void identical::unspecialize(depth x, bool y) {
    first_->unspecialize(x, y);
    second_->unspecialize(x, y);
  }


  void identical::unspecialize(std::set<val<variable>>& vs, bool b) {
    first_->unspecialize(vs, b);
    second_->unspecialize(vs, b);
  }


  val<formula> identical::rename(level lv, degree sl) const {
    val<identical> ir(make, *this);
    ir->first_ = first_->rename(lv, sl);
    ir->second_ = second_->rename(lv, sl);
    return ir;
  }


  val<formula> identical::add_exception_set(variable_map& vm) const {
    val<identical> ir(make, *this);
    ir->first_ = first_->add_exception_set(vm);
    ir->second_ = second_->add_exception_set(vm);
    return ir;
  }


  val<formula> identical::substitute(const val<substitution>& s, substitute_environment vt) const {
    val<formula> x1 = first_->substitute(s, vt);
    val<formula> x2 = second_->substitute(s, vt);
    bool is_identical = (val<formula>(x1) == val<formula>(x2));
    return val<succeed_fail>(make, positive_? is_identical : !is_identical);
  }


  void identical::set_bind(bind& b, name_variable_table& vt) {
    first_->set_bind(b, vt);
    second_->set_bind(b, vt);
  }


  order identical::compare(const unit& x) const {
    auto& xr = dynamic_cast<const identical&>(x);
#if (__cplusplus > 201703L) // C++20
    order a = positive_ <=> xr.positive_;
#else
    order a = order(positive_, xr.positive_);
#endif
    if (a != equal)  return a;
#if (__cplusplus > 201703L) // C++20
    order c = first_ <=> xr.first_;
    if (c != equal)  return c;
    return second_ <=> xr.second_;
#else
    order c = mli::compare(first_, xr.first_);
    if (c != equal)  return c;
    return mli::compare(second_, xr.second_);
#endif
  }


  precedence_t identical::precedence() const {
    return identical_oprec;
  }


  void identical::write(std::ostream& os, write_style) const {
    os << first_;
    if (positive_)
      os << " ≣ ";
    else
      os << " ≣̷ ";
    os << second_;
  }


  alternatives objectidentical::unify(unify_environment, const val<formula>& x, unify_environment, database*, level, degree_pool&, direction) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "objectidentical::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }
    objectidentical* xp = dyn_cast<objectidentical*>(x);
    if (xp == 0)  return O;
    if (positive_ != xp->positive_)  return O;
    if (positive_)
      return first_ == second_? I : O;
    return first_ != second_? I : O;
  }

  kleenean objectidentical::has(const val<variable>& v, occurrence oc) const {
    kleenean k1 = first_->has(v, oc);
    if (k1 == true)  return true;

    kleenean k2 = second_->has(v, oc);

    return k1 || k2;
  }


  void objectidentical::contains(std::set<val<variable>>& s, std::set<val<variable>>& bs, bool& more, occurrence oc) const {
    first_->contains(s, bs, more, oc);
    second_->contains(s, bs, more, oc);
  }


  kleenean objectidentical::free_for(const val<formula>& f, const val<variable>& x,
    std::set<val<variable>>& s, std::list<val<variable>>& bs) const {
    kleenean k1 = first_->free_for(f, x, s, bs);
    if (k1 == false)  return false;
    kleenean k2 = second_->free_for(f, x, s, bs);
    return k1 && k2;
  }


  void objectidentical::unspecialize(depth x, bool y) {
    first_->unspecialize(x, y);
    second_->unspecialize(x, y);
  }


  void objectidentical::unspecialize(std::set<val<variable>>& vs, bool b) {
    first_->unspecialize(vs, b);
    second_->unspecialize(vs, b);
  }


  val<formula> objectidentical::rename(level lv, degree sl) const {
    val<objectidentical> ir(make, *this);
    ir->first_ = first_->rename(lv, sl);
    ir->second_ = second_->rename(lv, sl);
    return ir;
  }


  val<formula> objectidentical::add_exception_set(variable_map& vm) const {
    val<objectidentical> ir(make, *this);
    ir->first_ = first_->add_exception_set(vm);
    ir->second_ = second_->add_exception_set(vm);
    return ir;
  }


  val<formula> objectidentical::substitute(const val<substitution>& s, substitute_environment vt) const {
    val<formula> v1 = first_->substitute(s, vt);
    val<formula> v2 = second_->substitute(s, vt);

    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "objectidentical::substitute()\n  "
        << "(" << *this << ")" << s << "\n    "
        << "v1 = " << v1 << "\n    "
        << "v2 = " << v2
        << std::endl;
    }

    variable* v1p = dyn_cast<variable*>(v1);
    variable* v2p = dyn_cast<variable*>(v2);
    if (v1p == 0 || v2p == 0)
      throw std::runtime_error("In \"objectidentical\", substitute error.");

    bool is_identical = (*v1p == *v2p);

    return val<succeed_fail>(make, positive_? is_identical : !is_identical);
  }


  void objectidentical::set_bind(bind& b, name_variable_table& vt) {
    first_->set_bind(b, vt);  second_->set_bind(b, vt);
  }


  order objectidentical::compare(const unit& x) const {
    auto& xr = dynamic_cast<const objectidentical&>(x);
#if (__cplusplus > 201703L) // C++20
    order a = positive_ <=> xr.positive_;
#else
    order a = order(positive_, xr.positive_);
#endif
    if (a != equal)  return a;
#if (__cplusplus > 201703L) // C++20
    order c = first_ <=> xr.first_;
    if (c != equal)  return c;
    return second_ <=> xr.second_;
#else
    order c = mli::compare(first_, xr.first_);
    if (c != equal)  return c;
    return mli::compare(second_, xr.second_);
#endif
  }


  precedence_t objectidentical::precedence() const {
    return identical_oprec;
  }


  void objectidentical::write(std::ostream& os, write_style) const {
    os << first_;
    if (positive_)
      os << " ≡ ";
    else
      os << " ≢ ";
    os << second_;
  }


  alternatives free_in_object::unify(unify_environment tt, const val<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "free_in_object::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    free_in_object* xp = dyn_cast<free_in_object*>(x);
    if (xp == 0)  return O;
    if (positive_ != xp->positive_)  return O;
    alternatives as = mli::unify(val<formula>(variable_), tt, val<formula>(xp->variable_), tx, dbp, lv, sl, dr);
    return as.unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
  }


  kleenean free_in_object::has(const val<variable>& v, occurrence oc) const {
    kleenean k1 = variable_->has(v, oc);
    if (k1 == true)  return true;
    kleenean k2 = formula_->has(v, oc);
    return k1 || k2;
  }


  void free_in_object::contains(std::set<val<variable>>& s, std::set<val<variable>>& bs, bool& more, occurrence oc) const {
    variable_->contains(s, bs, more, oc);
    formula_->contains(s, bs, more, oc);
  }


  kleenean free_in_object::free_for(const val<formula>& f, const val<variable>& x,
    std::set<val<variable>>& s, std::list<val<variable>>& bs) const {
    kleenean k1 = variable_->free_for(f, x, s, bs);
    if (k1 == false)  return false;
    kleenean k2 = formula_->free_for(f, x, s, bs);
    return k1 && k2;
  }


  void free_in_object::unspecialize(depth x, bool y) {
    variable_->unspecialize(x, y);
    formula_->unspecialize(x, y);
  }


  void free_in_object::unspecialize(std::set<val<variable>>& vs, bool b) {
    variable_->unspecialize(vs, b);
    formula_->unspecialize(vs, b);
  }


  val<formula> free_in_object::rename(level lv, degree sl) const {
    val<free_in_object> fp(make, *this);
    fp->variable_ = variable_->rename(lv, sl);
    fp->formula_ = formula_->rename(lv, sl);
    return fp;
  }


  val<formula> free_in_object::add_exception_set(variable_map& vm) const {
    val<free_in_object> fp(make, *this);
    fp->variable_ = variable_->add_exception_set(vm);
    fp->formula_ = formula_->add_exception_set(vm);
    return fp;
  }


  val<formula> free_in_object::substitute(const val<substitution>& s, substitute_environment vt) const {
    val<formula> v0 = variable_->substitute(s, vt);
    variable* vp = dyn_cast<variable*>(v0);

    if (vp == 0)
      throw std::runtime_error("In free_in_object::substitute, substitution of variable not a variable.");

    val<variable> v(v0);
    val<formula> f = formula_->substitute(s, vt);

    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "free_in_object::substitute:\n  "
       << val<free_in_object>(make, v, f, positive_)
       << std::endl;
    }

    kleenean is_free_in = f->has(v, occurrence::free);

    if (is_free_in == undefined)
      return val<free_in_object>(make, v, f, positive_);

    if (is_free_in == positive_)
      return {};

    std::ostringstream oss;
    oss << "free_in_object::substitute: Metacondition false: "
      << val<free_in_object>(make, v, f, positive_);
    throw illegal_substitution(oss.str());
  }


  void free_in_object::set_bind(bind& b, name_variable_table& vt) {
    variable_->set_bind(b, vt);  formula_->set_bind(b, vt);
  }


  order free_in_object::compare(const unit& x) const {
    auto& xr = dynamic_cast<const free_in_object&>(x);

#if (__cplusplus > 201703L) // C++20
    order a = positive_ <=> xr.positive_;
#else
    order a = order(positive_, xr.positive_);
#endif
    if (a != equal)  return a;

#if (__cplusplus > 201703L) // C++20
    order c = variable_ <=> xr.variable_;
    if (c != equal)  return c;

    return formula_ <=> xr.formula_;
#else
    order c = mli::compare(variable_, xr.variable_);
    if (c != equal)  return c;

    return mli::compare(formula_, xr.formula_);
#endif
  }


  precedence_t free_in_object::precedence() const {
    return free_oprec;
  }


  void free_in_object::write(std::ostream& os, write_style) const {
    os << variable_;
    if (!positive_)  os << " not";
    os << " free in " << formula_;
  }


  alternatives free_for_object::unify(unify_environment tt, const val<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "free_for_object::unify(\n  " << *this << ";\n  " << x << ")\n" << std::flush;
    }

    free_for_object* xp = dyn_cast<free_for_object*>(x);
    if (xp == 0)  return O;
    if (positive_ != xp->positive_)  return O;
    alternatives as = mli::unify(term_, tt, xp->term_, tx, dbp, lv, sl, dr);
    as = as.unify(val<formula>(variable_), tt, val<formula>(xp->variable_), tx, dbp, lv, sl, dr);
    return as.unify(formula_, tt, xp->formula_, tx, dbp, lv, sl, dr);
  }


  kleenean free_for_object::has(const val<variable>& v, occurrence oc) const {
    kleenean k1 = term_->has(v, oc);
    if (k1 == true) return true;

    kleenean k2 = variable_->has(v, oc);
    if (k2 == true) return true;

    kleenean k3 = formula_->has(v, oc);

    return k1 || k2 || k3;
  }


  void free_for_object::contains(std::set<val<variable>>& s, std::set<val<variable>>& bs, bool& more, occurrence oc) const {
    term_->contains(s, bs, more, oc);
    variable_->contains(s, bs, more, oc);
    formula_->contains(s, bs, more, oc);
  }


  kleenean free_for_object::free_for(const val<formula>& f, const val<variable>& x,
    std::set<val<variable>>& s, std::list<val<variable>>& bs) const {
    kleenean k1 = term_->free_for(f, x, s, bs);
    if (k1 == false) return false;

    kleenean k2 = variable_->free_for(f, x, s, bs);
    if (k2 == false) return false;

    kleenean k3 = formula_->free_for(f, x, s, bs);

    return k1 && k2 && k3;
  }


  void free_for_object::unspecialize(depth x, bool y) {
    term_->unspecialize(x, y);
    variable_->unspecialize(x, y);
    formula_->unspecialize(x, y);
  }


  void free_for_object::unspecialize(std::set<val<variable>>& vs, bool b) {
    term_->unspecialize(vs, b);
    variable_->unspecialize(vs, b);
    formula_->unspecialize(vs, b);
  }


  val<formula> free_for_object::rename(level lv, degree sl) const {
    val<free_for_object> fp(make, *this);
    fp->term_ = term_->rename(lv, sl);
    fp->variable_ = variable_->rename(lv, sl);
    fp->formula_ = formula_->rename(lv, sl);
    return fp;
  }


  val<formula> free_for_object::add_exception_set(variable_map& vm) const {
    val<free_for_object> fp(make, *this);
    fp->term_ = term_->add_exception_set(vm);
    fp->variable_ = variable_->add_exception_set(vm);
    fp->formula_ = formula_->add_exception_set(vm);
    return fp;
  }


  val<formula> free_for_object::substitute(const val<substitution>& s, substitute_environment vt) const {
    val<formula> v0 = variable_->substitute(s, vt);
    variable* vp = dyn_cast<variable*>(v0);
    if (vp == 0)
      throw std::runtime_error("In free_for_object::substitute, substitution of variable not a variable.");

    val<variable> v(v0);
    val<formula> t = term_->substitute(s, vt);
    val<formula> f = formula_->substitute(s, vt);

    if (trace_value & trace_substitute) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "free_for_object::substitute:\n  "
       << val<free_for_object>(make, t, v, f, positive_)
       << std::endl;
    }

    kleenean is_free_for = f->free_for(t, v);

    if (is_free_for == undefined)
      return val<free_for_object>(make, t, v, f, positive_);

#if 1
    if (is_free_for == positive_)
      return {};

    std::ostringstream oss;
    oss << "free_for_object::substitute: Metacondition false: "
      << val<free_for_object>(make, t, v, f, positive_);
    throw illegal_substitution(oss.str());
#else
    return val<succeed_fail>(make, positive_? is_free_for : !is_free_for);
#endif
  }


  void free_for_object::set_bind(bind& b, name_variable_table& vt) {
    term_->set_bind(b, vt);
    variable_->set_bind(b, vt);
    formula_->set_bind(b, vt);
  }


  order free_for_object::compare(const unit& x) const {
    auto& xr = dynamic_cast<const free_for_object&>(x);
#if (__cplusplus > 201703L) // C++20
    order a = positive_ <=> xr.positive_;
#else
    order a = order(positive_, xr.positive_);
#endif
    if (a != equal)  return a;

#if (__cplusplus > 201703L) // C++20
    order b = term_ <=> xr.term_;
    if (b != equal)  return b;

    order c = variable_ <=> xr.variable_;
    if (c != equal)  return c;

    return formula_ <=> xr.formula_;
#else
    order b = mli::compare(term_, xr.term_);
    if (b != equal)  return b;

    order c = mli::compare(variable_, xr.variable_);
    if (c != equal)  return c;

    return mli::compare(formula_, xr.formula_);
#endif
  }


  precedence_t free_for_object::precedence() const {
    return free_oprec;
  }


  void free_for_object::write(std::ostream& os, write_style) const {
    os << term_;
    if (!positive_)  os << " not";
    os << " free for " << variable_ << " in " << formula_;
  }

} // namespace mli

