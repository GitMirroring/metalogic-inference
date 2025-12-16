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

#include <iostream>

#include "location.hh"


namespace mli {

  using location_type = location;
  using location_t = location_type;


  inline void diagnostic(const location_type& loc, const std::string& errstr, std::istream& isp, std::istream::pos_type pos) {
    std::string s = "error: ";

    if (errstr.substr(0, 7) == "warning")
      s.clear();

    std::cerr << loc << ": " << s << errstr << std::endl;

    // Find the current line by seeking from the beginning of the file:

    // The stream might have reached EOF and not readable unless cleared:
    std::istream::iostate st0 = isp.rdstate();

    isp.clear();

    // Save the current file position and restore it after the line has been output:
    std::istream::pos_type pos0 = isp.tellg();

    if (pos0 == -1) return;

    try {
      isp.seekg(pos);
    }
    catch (const std::ios_base::failure&) {
      return;
    }

    std::istream::int_type c;

    while ((c = isp.get()) != '\n' && c != std::istream::traits_type::eof())
      std::cerr << (char)c;

    std::cerr << std::endl;


    // Write a line with the error position marked:

    size_t i = 0;

    for (i = 1; i < loc.begin.column; ++i)
      std::cerr << " ";

    std::cerr << "^";

    if (loc.begin.column + 1 < loc.end.column) {
      for (i += 2; i < loc.end.column; ++i)
        std::cerr << "-";

      std::cerr << "^";
    }

    std::cerr << std::endl;


    // Restore file position and state:
    try {
      isp.seekg(pos0);
      isp.setstate(st0);
    }
    catch (const std::ios_base::failure&) {
      return;
    }
  }


} // namespace mli

