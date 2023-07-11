[— Copyright (C) 2017, 2021-2023 Hans Åberg.

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
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  —]


input std/KM.mli


theory NBG. — Mendelson
  include theory KM.

  formal system.
    — binary infix ∈, =, ⊆, ⊊.
    predicate M, Pr.
  
  definition EQ. — Equality.
    object X, Y.
      X = Y ≔ ∀Z: Z ∈ X ⇔ Z ∈ Y.

  definition Inc. — Inclusion.
    object X, Y.
      X ⊆ Y ≔ ∀Z: Z ∈ X ⇒ Z ∈ Y.

  definition PInc. — Proper inclusion.
    object X, Y.
      X ⊊ Y ≔ X ⊆ Y ∧ ¬X = Y.
  
  definition IsSet. — Is a set.
    object X.
      M(X) ≔ ∃Y: X ∈ Y.

  definition PClass. — Is a proper class.
    object X.
      Pr(X) ≔ ¬M(X).

  axiom T. — Axiom of extensionality.
    object X, Y, Z.
      X = Y ⇒ (X ∈ Z ⇔ Y ∈ Z).

[— 
  axiom P. — Pairing axiom.
    ∀x, y of M  ∃z of M  ∀u of M:
      u ∈ z ⇔ u = x ∨ u = x.
  
  axiom N. — Null (empty) set.
    ∃x of M  ∀y of M: ¬y ∈ x.
  — In Mendelson, the following statement is listed as a
  — definition, but it does ¬ make sense as such; instead it is a
  — defining axiom.
  defining axiom Empty. constant empty. — Mendelson, p. 161.
    ∀x of M: ¬x ∈ ∅.
  justification. Show that axiom N imples:
    ∃! x of M  ∀y of M: ¬y ∈ x.
  One then knows that adding the defining axiom Empty creates a theory
  equivalent to the old one. See Mendelson, proposition 2.29, p. 82 ff.
definition E1. formula A. 
  ∃! x A(x) ≔ ∃A & ∀x, y: A(x) & A(y) ⇒ x = y.
—]
  end formal system.

end theory NBG.
