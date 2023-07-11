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

#pragma once

#include <stdexcept>


namespace mli {


  class access_error : public std::runtime_error {
  public:
    explicit access_error(const char* what_arg) : std::runtime_error(what_arg) {}
    explicit access_error(const std::string& what_arg) : std::runtime_error(what_arg) {}
  };


  class precedence_error : public std::runtime_error {
  public:
    explicit precedence_error(const char* what_arg) : std::runtime_error(what_arg) {}
    explicit precedence_error(const std::string& what_arg) : std::runtime_error(what_arg) {}
  };


  class parse_error : public std::logic_error {
  public:
    explicit parse_error(const char* what_arg) : std::logic_error(what_arg) {}
    explicit parse_error(const std::string& what_arg) : std::logic_error(what_arg) {}
  };


  class interpret_error : public std::runtime_error {
  public:
    explicit interpret_error(const char* what_arg) : std::runtime_error(what_arg) {}
    explicit interpret_error(const std::string& what_arg) : std::runtime_error(what_arg) {}
  };


  class illegal_substitution : public std::runtime_error {
  public:
    explicit illegal_substitution(const char* what_arg) : std::runtime_error(what_arg) {}
    explicit illegal_substitution(const std::string& what_arg) : std::runtime_error(what_arg) {}
  };


  class thread_exit : public std::exception {
  public:
    thread_exit() = default;
  };

} // namespace mli

