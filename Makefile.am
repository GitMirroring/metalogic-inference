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

# Makefile for MLI (Meta-Logic Inference).

AUTOMAKE_OPTIONS = dist-xz

SUBDIRS =  tests src doc man
EXTRA_DIST = mli examples

dist_doc_DATA = README AUTHORS COPYING LICENSE THANKS # NEWS TODO

include mli/local.mk
include examples/local.mk

mlidatadir = @mlidatadir@
examplesdir = @examplesdir@

dist-hook:
# Remove MacOS .DS_Store and file metadata (extended attributes)
	find $(distdir) -name '.DS_Store' -type f -delete
	if hash xattr 2>/dev/null; then xattr -r -c $(distdir); fi
