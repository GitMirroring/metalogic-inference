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

	// Class for reassigning file stream buffers.

#pragma once

#include <ostream>


  class reassign {
    std::streambuf* buf_save;
    std::ostream* os_save;
  public:
    reassign() : buf_save(0), os_save(0) {}
    // Save os1 buffer, and make new buffer of os1 to be os2.rdbuf():
    reassign(std::ostream& os1, std::ostream& os2)
     : buf_save(os1.rdbuf()), os_save(&os1) {
      os1.rdbuf(os2.rdbuf());
    }
    // Restore old buffer of saved os_save to buf_save:
    ~reassign() { if (os_save && buf_save) os_save->rdbuf(buf_save); }
  };

