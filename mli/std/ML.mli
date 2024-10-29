[— Copyright (C) 2017, 2021-2024 Hans Åberg.

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


theory ML. — MetaLogic theory

[— Metaquantities and metasymbols:
    A ≡ A   metaequality, or identical
    R ⊏ S   metasubset
    A ⋿ theory(T)  in, member of
    ⊩ ⊢     metaproof
    ⋎ or    metaor
    ⋏ and   metaand
    not     metanot
    if then, implies ⇨ metaimplication
    ⇦
    metatheorem
    postulate
    metaformula
    metapredicate  accepts only formulas as argument.
    formula sequence
—]

  formal system.
  — binary infix metapredicate * ≡ *
  
[—
  — Extension of premises and theory.
  — “extension”.
  axiom ext. formula A theory T, U formula sequence S, R.
    R ⊏ S, U ⊏ T, (R ⊢₍U₎ A) ⊢ (S ⊢₍T₎ A).

  — Relation between body₍X₎ and head₍X₎.
  axiom BH. rule X theory T formula sequence S.
    (S ⊢₍T₎ body₍X₎) ⊢ (S ⊢₍T₎ head₍X₎).
  
  — Formulaset recursion (not currently needed).
  axiom FS. formula A formula sequence S, As rule X theory T.
    (S ⊢₍T₎ As use FS), (S ⊢₍T₎ A) ⊢ (S ⊢₍T₎ As :> A).

  — Proof induction.
  axiom PI. theorem T, metapredicate P, postulate A.
    A ⋿ theory(T), (P(body₍A₎) ⊢ P(head₍A₎)), P(body₍T₎) ⊢ P(head₍T₎).
—]  

[—
  — Axioms for metaequality (MEQ) * ≡ * (a binary infix metapredicate):
  axiom ref. formula A.
    A ≡ A. — Reflexivity.
  rule sub1. formula A, B metaformula P.
    A ≡ B, P(A, A) ⊢ P(A, B). — Substitutivity.
—]
[—
  rule sub2. formula A, B, X, Y metaformula P.
    A ≡ B, P[X.A, Y.A] ⊢ P[X.A, Y.B]. — Substitutivity.
—]
[—
  — Prove left hand side:
  rule PL. formula A, B. B, A ≡ B ⊢ A. 
  — Prove right hand side:
  rule PR. formula A, B. A, A ≡ B ⊢ B.
—]
— axiom P1. metapredicate P. P(X, Y) ≡ (Y ≡ X).

  end formal system.


[—
theorem sym. — “symmetry”.
  formula A, B.
    A ≡ B ⊢ B ≡ A. — Symmetry.
proof
  1. A ≡ B by premise.
  2. formula X, Y. define P(X, Y) ≔ Y ≡ X.
  3. P(A, A) by ref.
  4. P(A, B) by sub; 1, 3.
  conclusion by 4.
∎
 
theorem tran. — “transitivity”.
  formula A, B, C.
    A ≡ B, B ≡ C ⊢ A ≡ C. — Transitivity.
proof
  1. A ≡ B by premise.
  2. B ≡ C by premise.
  3. object X, Y. define P(X, Y) ≔ Y ≡ C.
  4. P(B, B) by 2.
  5. B ≡ A by sym; 1.
  6. P(B, A) by sub; 5, sub.
  conclusion by 6.
∎

theorem prov. — “provability”
  formula A, B theory T formula sequence S.
    A ≡ B, (S ⊢₍T₎ A) ⊢ (S ⊢₍T₎ B). — Provability.
proof
—]

end theory ML.

