# Copyright (C) 2017, 2021-2026 Hans Åberg.
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

AC_PREREQ([2.69])

AC_INIT([GNU MLI],[0.1],[bug-mli@gnu.org],[mli],[https://www.gnu.org/software/metalogic-inference/])
AM_INIT_AUTOMAKE([-Wall foreign])

AC_CONFIG_HEADERS([src/config.h:src/config.in.h])
AC_CONFIG_FILES([Makefile src/Makefile doc/Makefile man/Makefile tests/Makefile])

AC_SUBST(mlidatarootdir, [${datadir}])
AC_SUBST(mlidatadir, [${datadir}/mli])
AC_SUBST(examplesdir, [${docdir}])

AC_LANG(C++)
AC_PROG_CXX

AM_MISSING_PROG(HELP2MAN, help2man, $missing_dir)

AC_OUTPUT

