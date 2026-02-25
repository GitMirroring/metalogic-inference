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

#include <iostream>


  // Debugging macros.

  // Usage:
  //   show_element(x)   // Write variable x name and its value.
  //   show_function(x)  // Write function name and variable types. Uses GCC C extension.
  #define show_element(x)  std::cout << #x " = " << (x) << std::endl;
  #define show_function    std::cout << __PRETTY_FUNCTION__ << std::endl;
  #define show_element_log(x)  std::clog << #x " = " << (x) << std::endl;
  #define show_functionlog    std::clog << __PRETTY_FUNCTION__ << std::endl;


  // Usage:
  //   show_bool(x)     // Write variable x name and its boolean value as "true" or "false".
  //   show_sizeof(x)   // Write variable x name and its sizeof value.
  #define show_bool(x) std::cout << "  " #x " = " << ((x)? "true" : "false") << std::endl;
  #define show_sizeof(x) std::cout << "sizeof(" #x ") = " << sizeof(x) << std::endl;


