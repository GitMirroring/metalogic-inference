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

#include "database.hh"

#include "definition.hh"
#include "substitution.hh"


namespace mli {

  size_type sublevel_max = 1000;


  // Implementation of class sequence_database.

  sequence_database::sequence_database(const sequence_database& x, const sequence_database& y)
   : has_definition_(false) {
    const_sequence_iterator i = x.sequence_table_.begin(), i1 = x.sequence_table_.end();
    for (; i != i1; ++i)
      insert(*i);
    i = y.sequence_table_.begin(), i1 = y.sequence_table_.end();
    for (; i != i1; ++i)
      insert(*i);
  }


  alternatives sequence_database::unify(unify_environment tt, const val<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {

    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "sequence_database::unify: " << x << std::endl;
    }

#if NEW_PROVED
    // A formula can be provable, say an inference from its premises, and then
    // the statements should not be tried.
    if (tx.target_ == goal && x->provable())
      return I;
#endif

    alternatives as; // Return value.
    const_sequence_iterator i, i0 = sequence_table_.begin(), i1 = sequence_table_.end();

    if (trace_value & trace_statement) {
      std::clog << "Proposition alternatives:" << std::endl;
      for (i = i0; i != i1; ++i) {
        std::clog << "  ";
        (*i)->write(std::clog,
          write_style(write_name | write_type | write_statement));
        std::clog << "\n" << std::flush;
      }
    }

    for (i = i0; i != i1; ++i) {
      // If strict proofs are called for, do not look at not proved statements.
      if (strict_proof && (*i)->is_proved() != true)
        continue;

      if ((*i)->get_statement_type() == a_definition)
        continue; // Do not look at definitions; these are expanded during unification.

      val<statement> ls = val<statement>((*i)->rename(lv, 0));

      alternatives bs = mli::unify(ls, tt, x, tx, dbp, lv, sl, dr);

      if (trace_value & trace_unify) {
        val<formula> f = ls->get_formula();
        std::lock_guard<std::recursive_mutex> guard(write_mutex);
        std::clog << "sequence_database::unify(\n  " << x << ";\n  " << f << "):" << bs << std::endl;
      }

      if (bs.empty()) {
        continue;
      }

      as = as.append(bs);
    }

    return as;
  }


  alternatives sequence_database::unify(const val<formula>& x, unify_environment tx, const val<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {

    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "sequence_database::unify(\n  " << x << ";\n  " << y << ") in ";
      write(std::clog, write_style(write_name));
      std::clog << std::endl;
    }

    // Only unify when there is an abbreviation to expand:
    alternatives as;

    for (auto& i: sequence_table_) {
      if (i->get_statement_type() != a_definition)
        continue;  // Only expand definitions during unification.

      alternatives bs = i->unify(x, tx, y, ty, dbp, lv, sl, dr);
      as.append(bs);
    }

    return as;
  }


  val<formula> sequence_database::rename(level lv, degree sl) const {
    ref2<sequence_database> dp(make, *this);
    val<formula> rt(dp);
    const_sequence_iterator i = sequence_table_.begin(), i1 = sequence_table_.end();
    sequence_iterator j = dp->sequence_table_.begin(), j1 = dp->sequence_table_.end();
    for (; i != i1; ++i, ++j)
      (*j) = val<statement>((*i)->rename(lv, sl));
    return rt;
  }


  val<formula> sequence_database::add_exception_set(variable_map& vm) const {
    ref2<sequence_database> dp(make, *this);
    val<formula> rt(dp);
    const_sequence_iterator i = sequence_table_.begin(), i1 = sequence_table_.end();
    sequence_iterator j = dp->sequence_table_.begin(), j1 = dp->sequence_table_.end();
    for (; i != i1; ++i, ++j)
      (*j) = val<statement>((*i)->add_exception_set(vm));
    return rt;
  }



  val<formula> sequence_database::substitute(const val<substitution>& s, substitute_environment vt) const {
    ref2<sequence_database> dp(make, *this);
    const_sequence_iterator i = sequence_table_.begin(), i1 = sequence_table_.end();
    sequence_iterator j = dp->sequence_table_.begin(), j1 = dp->sequence_table_.end();

    for (; i != i1; ++i, ++j)
      (*j) = val<statement>((*i)->substitute(s, vt));

    return dp;
  }


  bool sequence_database::insert(const ref4<statement>& x) {
    if (name_table_.find(x->name()) != name_table_.end()) {
      std::cerr << "sequence_database::insert: not using statement name duplicate " << x->name() << "." << std::endl;
      return false;
    }

    name_table_[x->name()] = x;
    sequence_table_.push_back(x);
    if (!has_definition_)
      has_definition_ = (dyn_cast<definition*>(x) != 0);
    return true;
  }


  void sequence_database::insert(const ref2<sequence_database>& x) {
    for (auto& i: x->sequence_table_)
      insert(i);
  }


  std::optional<ref4<statement>> sequence_database::find(const std::string& name, level lv) {
    if (trace_value & trace_statement)
      std::clog << "sequence_database::find " << name << ", level " << lv.top << ": " << std::flush;

    name_iterator i = name_table_.find(name);
    if (i == name_table_.end()) {
      if (trace_value & trace_statement)
        std::clog << " not found.\n" << std::flush;

      return {};
    }

    if (trace_value & trace_statement)
      std::clog << i->second << ".\n" << std::flush;

    return i->second;
  }


  size_type sequence_database::metasize() const {
    size_type k = 0;

    for (auto& i: sequence_table_)
      if (i->get_statement_type() != a_definition)
        k += i->metasize();

    return k;
  }


  // Set to false exactly when a there is one statement with a non-empty name:
  // If this statement is an explicit "premise", then this inhibits the
  // implicit premise expansion.
  bool sequence_database::expand_premise(level lv) const {
#if 1 // New expand_premise
    //
    for (auto& i: sequence_table_)
      if (i->get_statement_type() != a_definition && !i->expand_premise(lv))
        return false;

    return true;
#else
    size_type k = 0;

    for (auto& i: sequence_table_)
      if (!i->name().empty() && i->get_statement_type() != a_definition)
        k += i->expand_premise(lv);

    return k != 1;
#endif
  }


  void sequence_database::write(std::ostream& os, write_style ws) const {
    bool show_type = ws & write_type;
    bool show_name = ws & write_name;
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;
    if ((show_proof || show_statement) && sequence_table_.empty()) {
      os << "— Empty database —" << std::endl;
      return;
    }
    const_sequence_iterator i, i0 = sequence_table_.begin(), i1 = sequence_table_.end();
    for (i = i0; i != i1; ++i) {
      if (i != i0) {
        if (show_proof || show_statement)  os << "\n";
        else  os << ", ";
      }
      (*i)->write(os, ws);
      if (show_proof || show_statement)  os << "\n";
    }
  }


  // Implementation of class sublevel_database.

  alternatives sublevel_database::unify(unify_environment tt, const val<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "sublevel_database::unify(\n  " << x << ") in ";
      write(std::clog, write_style(write_name));
      std::clog << std::endl;
    }

#if 1
    if (lv.sub < table_.size())
      return table_[lv.sub]->unify(tt, x, tx, dbp, lv, sl, dr);

    return table_.back()->unify(tt, x, tx, dbp, lv, sl, dr);
#else
    alternatives as;

    for (auto& i: table_) {
      alternatives bs = i->unify(tt, x, tx, dbp, lv, sl, dr);

      if (lv.top == 3) {
        std::clog << "sublevel_database::unify 3 A " << lv.sub << ": " << std::endl;
        std::clog << x << ") in ";
        write(std::clog, write_style(write_name));
        std::clog << "\n bs =\n" << bs <<  std::endl;
      }

      as.append(bs);
    }

    return as;
#endif
  }


  alternatives sublevel_database::unify(const val<formula>& x, unify_environment tx, const val<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "sublevel_database::unify(\n  " << x << ";\n  " << y << ") in ";
      write(std::clog, write_style(write_name));
      std::clog << std::endl;
    }

#if 1
    if (lv.sub < table_.size())
      return table_[lv.sub]->unify(x, tx, y, ty, dbp, lv, sl, dr);

    return table_.back()->unify(x, tx, y, ty, dbp, lv, sl, dr);
#else
    alternatives as;

    for (auto& i: table_) {
      alternatives bs = i->unify(x, tx, y, ty, dbp, lv, sl, dr);

      if (lv.top == 3) {
        std::clog << "sublevel_database::unify 3 B " << lv.sub << ": " << std::endl;
        std::clog << x << ";\n" << y << ") in ";
        write(std::clog, write_style(write_name));
        std::clog << "\n bs =\n" << bs <<  std::endl;
      }

      as.append(bs);
    }

    return as;
#endif
  }


  val<formula> sublevel_database::rename(level lv, degree sl) const {
    ref3<sublevel_database> dp(make, *this);

    auto i = table_.begin(), i1 = table_.end();
    auto j = dp->table_.begin();

    for (; i != i1; ++i, ++j)
      *j = val<database>((*i)->rename(lv, sl));

    return dp;
  }


  val<formula> sublevel_database::add_exception_set(variable_map& vm) const {
    ref3<sublevel_database> dp(make, *this);

    auto i = table_.begin(), i1 = table_.end();
    auto j = dp->table_.begin();

    for (; i != i1; ++i, ++j)
      *j = val<database>((*i)->add_exception_set(vm));

    return dp;
  }


  val<formula> sublevel_database::substitute(const val<substitution>& s, substitute_environment vt) const {
    ref3<sublevel_database> dp(make, *this);

    auto i = table_.begin(), i1 = table_.end();
    auto j = dp->table_.begin();

    for (; i != i1; ++i, ++j)
      *j = val<database>((*i)->substitute(s, vt));

    return dp;
  }


  bool sublevel_database::empty() const {
    for (auto& i: table_)
      if (!i->empty())
        return false;
    return true;
  }


  bool sublevel_database::has_definition(level lv) const {
    if (lv.sub < table_.size())
      return table_[lv.sub]->has_definition(lv);
    return table_.back()->has_definition(lv);
  }


  bool sublevel_database::insert(const ref4<statement>& s) {
    // Rewrite this so that statements are always inserted:
    if (table_.empty())
     return false;
    return table_.back()->insert(s);
  }


  std::optional<ref4<statement>> sublevel_database::find(const std::string& name, level lv) {
    if (lv.sub < table_.size())
      return table_[lv.sub]->find(name, lv);
    return table_.back()->find(name, lv);
  }


  size_type sublevel_database::metasize() const {
    size_type k = 0;

    for (auto& i: table_)
        k += i->metasize();

    return k;
  }


  bool sublevel_database::expand_premise(level lv) const {
    if (lv.sub < table_.size())
      return table_[lv.sub]->expand_premise(lv);

    return true;
  }


  void sublevel_database::write(std::ostream& os, write_style ws) const {
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;

    bool first = true;

    for (auto& i: table_) {
      if (first)
        first = false;
      else {
        os << ";";
        if (show_statement || show_proof)  os << "\n";
        else  os << " ";
      }

      i->write(os, ws);
    }
  }


  // Implementation of class level_database.

  alternatives level_database::unify(unify_environment tt, const val<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (lv.top <= get_level())
      return table_[lv.top - 1]->unify(tt, x, tx, dbp, lv, sl, dr);
    return table_.back()->unify(tt, x, tx, dbp, lv, sl, dr);
  }


  alternatives level_database::unify(const val<formula>& x, unify_environment tx, const val<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "level_database::unify(\n  " << x << ";\n  " << y << ") in ";
      write(std::clog, write_style(write_name));
      std::clog << std::endl;
    }

    if (lv.top <= get_level())
      return table_[lv.top - 1]->unify(x, tx, y, ty, dbp, lv, sl, dr);
    return table_.back()->unify(x, tx, y, ty, dbp, lv, sl, dr);
  }


  val<formula> level_database::rename(level lv, degree sl) const {
    ref5<level_database> dp(make, *this);

    auto i = table_.begin(), i1 = table_.end();
    auto j = dp->table_.begin();

    for (; i != i1; ++i, ++j)
      *j = val<database>((*i)->rename(lv, sl));

    return dp;
  }


  val<formula> level_database::add_exception_set(variable_map& vm) const {
    ref5<level_database> dp(make, *this);

    auto i = table_.begin(), i1 = table_.end();
    auto j = dp->table_.begin();

    for (; i != i1; ++i, ++j)
      *j = val<database>((*i)->add_exception_set(vm));

    return dp;
  }


  val<formula> level_database::substitute(const val<substitution>& s, substitute_environment vt) const {
    ref5<level_database> dp(make, *this);

    auto i = table_.begin(), i1 = table_.end();
    auto j = dp->table_.begin();

    for (; i != i1; ++i, ++j)
      *j = val<database>((*i)->substitute(s, vt));

    return dp;
  }


  bool level_database::empty() const {
    for (auto& i: table_)
      if (!i->empty())
        return false;
    return true;
  }


  database& level_database::operator[](size_type lv) {
    if (lv <= get_level())
      return *table_[lv - 1];;
    return *table_.back();
  }


  bool level_database::has_definition(level lv) const {
    if (lv.top <= get_level())
      return table_[lv.top - 1]->has_definition(lv);
    return table_.back()->has_definition(lv);
  }


  bool level_database::insert(const ref4<statement>& s) {
    // Rewrite this so that statements are always inserted:
    if (table_.empty())
     return false;
    return table_.back()->insert(s);
  }


  std::optional<ref4<statement>> level_database::find(const std::string& name, level lv) {
    if (lv.top <= get_level())
      return table_[lv.top - 1]->find(name, lv);
    return table_.back()->find(name, lv);
  }


  size_type level_database::metasize() const {
    size_type k = 0;

    for (auto& i: table_)
        k += i->metasize();

    return k;
  }


  bool level_database::expand_premise(level lv) const {
    if (lv.top <= get_level())
      return table_[lv.top - 1]->expand_premise(lv);

    return true;
  }



  void level_database::write(std::ostream& os, write_style ws) const {
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;

    bool first = true;

    for (auto& i: table_) {
      if (first)
        first = false;
      else {
        os << ":";
        if (show_statement || show_proof)  os << "\n";
        else  os << " ";
      }

      i->write(os, ws);
    }
  }


  // Implementation of class sequential_database.

  sequential_database::sequential_database(const sequential_database& x, const sequential_database& y)
   : has_definition_(false) {
    const_sequential_iterator i = x.sequential_table_.begin(), i1 = x.sequential_table_.end();
    for (; i != i1; ++i)
      insert(*i);
    i = y.sequential_table_.begin(), i1 = y.sequential_table_.end();
    for (; i != i1; ++i)
      insert(*i);
  }


  alternatives sequential_database::unify(unify_environment tt, const val<formula>& x, unify_environment tx, database* dbp, level lv, degree_pool& sl, direction dr) const {

    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog << "sequential_database::unify: " << x << std::endl;
    }

    alternatives as; // Return value.
    const_sequential_iterator i, i0 = sequential_table_.begin(), i1 = sequential_table_.end();

    if (trace_value & trace_statement) {
      std::clog << "Proposition alternatives:" << std::endl;
      for (i = i0; i != i1; ++i) {
        std::clog << "  ";
        (*i)->write(std::clog,
          write_style(write_name | write_type | write_statement));
        std::clog << "\n" << std::flush;
      }
    }

    for (i = i0; i != i1; ++i) {
      // If strict proofs are called for, do not look at not proved statements.
      if (strict_proof && (*i)->is_proved() != true)
        continue;

      if ((*i)->get_statement_type() == a_definition)
        continue; // Do not look at definitions; these are expanded during unification.

      val<statement> ls = val<statement>((*i)->rename(lv, 0));
      val<formula> f = ls->get_formula();

      alternatives s = mli::unify(f, tt, x, tx, dbp, lv, sl, dr);

      if (trace_value & trace_unify) {
        std::lock_guard<std::recursive_mutex> guard(write_mutex);
        std::clog << "unify(\n  " << x << ";\n  " << f << "):" << s << std::endl;
      }

      if (s.empty()) {
        continue;
      }

      s = s.label(ls, lv);
      as = as.append(s);
    }

    return as;
  }


  alternatives sequential_database::unify(const val<formula>& x, unify_environment tx, const val<formula>& y, unify_environment ty, database* dbp, level lv, degree_pool& sl, direction dr) const {

    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "sequential_database::unify(\n  " << x << ";\n  " << y << ") in ";
      write(std::clog, write_style(write_name));
      std::clog << std::endl;
    }

    // Only unify when there is an abbreviation to expand:
    alternatives as;

    for (auto& i: sequential_table_) {
      if (i->get_statement_type() != a_definition)
        continue;  // Only expand definitions during unification.

      alternatives bs = i->unify(x, tx, y, ty, dbp, lv, sl, dr);
      as.append(bs);
    }

    return as;
  }


  val<formula> sequential_database::rename(level lv, degree sl) const {
    val<sequential_database> dp(make, *this);
    val<formula> rt(dp);
    const_sequential_iterator i = sequential_table_.begin(), i1 = sequential_table_.end();
    sequential_iterator j = dp->sequential_table_.begin(), j1 = dp->sequential_table_.end();
    for (; i != i1; ++i, ++j)
      (*j) = val<statement>((*i)->rename(lv, sl));
    return rt;
  }


  val<formula> sequential_database::add_exception_set(variable_map& vm) const {
    val<sequential_database> dp(make, *this);
    val<formula> rt(dp);
    const_sequential_iterator i = sequential_table_.begin(), i1 = sequential_table_.end();
    sequential_iterator j = dp->sequential_table_.begin(), j1 = dp->sequential_table_.end();
    for (; i != i1; ++i, ++j)
      (*j) = val<statement>((*i)->add_exception_set(vm));
    return rt;
  }


  val<formula> sequential_database::substitute(const val<substitution>& s, substitute_environment vt) const {
    val<sequential_database> dp(make, *this);
    const_sequential_iterator i = sequential_table_.begin(), i1 = sequential_table_.end();
    sequential_iterator j = dp->sequential_table_.begin(), j1 = dp->sequential_table_.end();
    for (; i != i1; ++i, ++j)
      (*j) = val<statement>((*i)->substitute(s, vt));
    return dp;
  }


  bool sequential_database::insert(const ref4<statement>& x) {
    if (x->name().empty()) {
      std::cerr << "sequential_database::insert: no name of " << x << std::endl;
      return false;
    }

    if (name_table_.find(x->name()) != name_table_.end()) {
      std::cerr << "sequential_database::insert: not using statement name duplicate " << x->name() << "." << std::endl;
      return false;
    }

    name_table_[x->name()] = x;
    sequential_table_.push_back(x);
    if (!has_definition_)
      has_definition_ = (dyn_cast<definition*>(x) != 0);
    return true;
  }


  std::optional<ref4<statement>> sequential_database::find(const std::string& name, level lv) {
    if (trace_value & trace_statement)
      std::clog << "sequential_database::find " << name << ", level " << lv.sub << ": " << std::flush;

    name_iterator i = name_table_.find(name);
    if (i == name_table_.end()) {
      if (trace_value & trace_statement)
        std::clog << " not found.\n" << std::flush;

      return {};
    }

    if (trace_value & trace_statement)
      std::clog << i->second << ".\n" << std::flush;

    return i->second;
  }


  size_type sequential_database::metasize() const {
    size_type k = 0;

    for (auto& i: sequential_table_)
        k += i->metasize();

    return k;
  }


  void sequential_database::write(std::ostream& os, write_style ws) const {
    bool show_type = ws & write_type;
    bool show_name = ws & write_name;
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;
    if ((show_proof || show_statement) && sequential_table_.empty()) {
      os << "— Empty database —" << std::endl;
      return;
    }
    const_sequential_iterator i, i0 = sequential_table_.begin(), i1 = sequential_table_.end();
    for (i = i0; i != i1; ++i) {
      if (i != i0) {
        if (show_proof || show_statement)  os << "\n";
        else  os << "| ";
      }
      (*i)->write(os, ws);
      if (show_proof || show_statement)  os << "\n";
    }
  }


  // Implementation of class theory.

  std::optional<ref4<statement>> theory::find(const std::string& name, level lv) {
    std::optional<ref4<statement>> p = sequential_database::find(name, lv);
    if (!p) {
      for (auto& i: includes_) {
        p = i->find(name, lv);
        if (!p)  continue;
        if (trace_value & trace_statement)
          std::clog << i->name() << "." << *p << ".\n" << std::flush;
        return p;
      }
    }
    return p;
  }


  void theory::write(std::ostream& os, write_style ws) const {
    bool show_type = ws & write_type;
    bool show_name = ws & write_name;
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;
    os << "theory " << name_ << ".\n";
    if ((show_proof || show_statement) && sequential_table_.empty() && includes_.empty()) {
      os << "— Empty theory —\n";
      os << "end theory " << name_ << ".\n";
      return;
    }
    if (!includes_.empty()) {
      os << "  include theory";
      for (auto& i: includes_)
        os << " " << i->name();
      os << ".\n";
    }
    os << "\n";

    bool it0 = true;
    for (auto& i: sequential_table_) {
      if (it0) it0 = false;
      else {
        if (show_proof || show_statement)  os << "\n";
        else  os << ", ";
      }
      i->write(os, ws);
      if (show_proof || show_statement)  os << "\n";
    }

    os << "\nend theory " << name_ << ".\n";
  }




  bool theory_database::insert(const ref1<theory>& t) {
    if (t->name().empty()) {
      std::cerr << "theory_database::insert: no name of " << t << std::endl;
      return false;
    }
    if (name_table_.find(t->name()) != name_table_.end()) {
      std::cerr << "theory_database::insert: not using statement name duplicate " << t->name() << "." << std::endl;
      return false;
    }
    name_table_[t->name()] = t;
    sequential_table_.push_back(t);
    return true;
  }


  std::optional<ref1<theory>> theory_database::find(const std::string& name) {
    if (trace_value & trace_statement)
      std::clog << "theory_database::find " << name << ": " << std::flush;
    name_iterator i = name_table_.find(name);
    if (i == name_table_.end()) {
      if (trace_value & trace_statement)  std::clog << " not found.\n" << std::flush;
        return {};
    }
    if (trace_value & trace_statement)  std::clog << i->second << ".\n" << std::flush;
    return i->second;
  }


  // Implementation of class theory_database.

  void theory_database::write(std::ostream& os, write_style ws) const {
    bool show_type = ws & write_type;
    bool show_name = ws & write_name;
    bool show_statement = ws & write_statement;
    bool show_proof = ws & write_proof;
    os << "— Begin: theory database " << name_ << ".\n\n";
    if (sequential_table_.empty()) {
      os << "— No theories —\n";
      return;
    }
    theory_database::const_sequential_iterator i, i0 = sequential_table_.begin(), i1 = sequential_table_.end();
    for (i = i0; i != i1; ++i) {
      if (i != i0)  os << "\n\n";
      (*i)->write(os, ws);
    }
    os << "\n— End: theory database " << name_ << ".\n";
  }

} // namespace mli
