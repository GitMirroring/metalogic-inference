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

info_TEXINFOS = mli.texi

dist_doc_DATA = mli.pdf classes.pdf classes.gv
dist_noinst_DATA = mli.tex version.texi luatex-math-modified.tex gpl-3.0.texi  texinfo.tex


TEXI2PDF = ':'

mli.texi: mli.tex
	awk '!/@stixfont/' $(srcdir)/mli.tex > $(srcdir)/mli.texi

# Indexing: luatex mli.tex cretest the unsorted mli.?p index files, and texindex mli.??
# creates the sorted texindex mli.??s files, which are used in the mli.pdf index. Several runs 
# may be required to get the index right, cf. the Texinfo manual, sec. 19.3.
mli.pdf: mli.tex
	cd $(srcdir) && luatex mli.tex && texindex mli.??

classes.pdf: classes.gv
	-cd $(srcdir) && dot -Tpdf classes.gv -o classes.pdf




