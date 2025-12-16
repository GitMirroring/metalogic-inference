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

  class integer : public nonempty_formula {
  public:
    int64_t value;

    integer() = default;

    new_copy(integer);
    new_move(integer);

    integer(long x) : value(x) {}

    integer(const char* xp, int base = 10) : value(std::stol(xp, nullptr, base)) {}
    integer(const std::string& x, int base = 10) : value(std::stol(x, nullptr, base)) {}

    explicit operator signed long int() const { return (signed long)value; }
    explicit operator unsigned long int() const { return (unsigned long)value; }

    formula::type get_formula_type() const override { return formula::object; }

    virtual alternatives unify(unify_environment, const val<formula>&, unify_environment, database*, level, degree_pool&, direction) const;

    virtual kleenean has(const val<variable>&, occurrence) const { return false; }
    virtual void contains(std::set<val<variable>>&, std::set<val<variable>>&, bool&, occurrence) const {}

    virtual kleenean free_for(const val<formula>&, const val<variable>&, 
      std::set<val<variable>>&, std::list<val<variable>>&) const
    { return true; }

    virtual val<formula> rename(level, degree) const { return *this; }
    virtual val<formula> substitute(const val<substitution>&, substitute_environment) const { return *this; }

    virtual void set_bind(bind&, name_variable_table&) {}

    virtual order compare(const unit&) const;

    virtual void write(std::ostream&, write_style) const;
  };

} // namespace mli

