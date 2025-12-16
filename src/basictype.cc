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

#include "basictype.hh"

#include "substitution.hh"


namespace mli {

  alternatives integer::unify(unify_environment, const val<formula>& x, unify_environment, database*, level, degree_pool&, direction) const {
    if (trace_value & trace_unify) {
      std::lock_guard<std::recursive_mutex> guard(write_mutex);
      std::clog
       << "integer::unify\n  " << *this << ";\n  " << x << ")"
       << std::endl;
    }

    integer* xp = dyn_cast<integer*>(x);
    return (xp != 0 && value == xp->value)? I : O;
  }


  order integer::compare(const unit& x) const {
    auto& xr = dynamic_cast<const integer&>(x);

    return order(value, xr.value);
  }


  void integer::write(std::ostream& os, write_style) const {
    os << value;
  }

} // namespace mli


