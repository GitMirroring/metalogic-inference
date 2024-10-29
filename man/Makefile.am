# Copyright (C) 2017, 2021-2024 Hans Åberg.
#
# This file is part of MLI, MetaLogic Inference.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# Using 'help2man' to create man pages (does not work with Å):

# In 'configure.ac' put
# AM_MISSING_PROG(HELP2MAN, help2man, $missing_dir)
#
# In ../Makefile.am, add 'man' to SUBDIRS or EXTRA_DIST.

dist_man1_MANS = mli.man

mli.man: ../src/mli
	-$(HELP2MAN) --output=$@ --locale=en_US.UTF-8 --name='GNU MLI, MetaLogic Inference' ../src/mli
	-mv mli.man $(srcdir)

