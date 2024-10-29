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

input std/KM.mli

theory TK1. — Test K (predicate theory).
  include theory KM.


  — Mendelson, p. 60.
  lemma X2. formula A, C.
    A, ∀x A ⇒ C ⊢ ∀x C
  proof
  —  conclusion by Gen, premise, MP.
    1. A by premise.
    2. ∀x A by Gen: 1.
    3. ∀x A ⇒ C by premise.
    4. C by MP: 2; 3. — 2, 3, MP.
    conclusion by Gen: 4. — 4, Gen.
  ∎


  — Mendelson, p. 62.
  lemma X3. formula A. —  object °x, °y.
    ∀x, y A ⊢ ∀y, x A
  by Gen: Gen: K1: K1: premise X3. — Gen, premise, K1.
[—
  proof
    1. ∀x, y A by premise.
    2. ∀x, y A ⊢ ∀y A by K1.
  — K1. ∀x A ⊢ A[x.t]
    3. ∀y A by 2, 1.
    4. ∀y A ⊢ A by K1.
    conclusion by 3, 4, Gen.
  [—
    1. ∀x, y A by premise.
    2. ∀x, y A ⊢ (∀y A) by K1.
  —  2. ∀x, y A ⊢ (∀y A)[x.x] by K1.
    3. ∀y A by 2, 1.
    4. ∀y A ⊢ A by K1.
  —  4. ∀y A ⊢ A[y.y] by K1.
    5. A by 3, 4.
    6. ∀x A by 5, Gen.
    7. ∀y, x A by 6, Gen.
    conclusion by 7.
  —]
  ∎
—]

  lemma X3a. formula A. —  object °x, °y.
    ∀x, y A ⇒ ∀y, x A
  by DT: Gen: Gen: K1. — Gen, K1, DT.


  lemma X3b. formula A. —  object °x, °y.
    ∀x, y A ⇒ ∀y, x A
  by DT: Gen: Gen: K1: K1: premise. — conclusion by Gen, K1, DT.
  —  conclusion by DT: “X3”. — Fails proof.



— rule K1. ∀x A ⊢ A[x⤇t].


[—
  lemma X4. formula A  object x.
    ∀x A ⊢ ∀y: A[x⤇y]
  proof
    conclusion by premise.
  ∎
—]

{— trace result —}

  — Example of variable dependencies, Mendelson, p. 60: Let 𝑩₁, 𝑩₂, 𝑩₃, 𝑩₄, 𝑩₅
  — respectively be the statement formulas of the correspondingly numbered prooflines.
  — Then in the given proof:
  — 𝑩₁ and 𝑩₂ depend on premise 𝑨.
  — 𝑩₃ depends on premise ∀𝑥 𝑨 ⇒ 𝑪.
  — 𝑩₄ and 𝑩₅ depend on premises 𝑨 and ∀𝑥 𝑨 ⇒ 𝑪.
  lemma X4. formula 𝑨, 𝑪.
    𝑨, ∀𝑥 𝑨 ⇒ 𝑪 ⊢ ∀𝑥 𝑪
  proof                  — Depends on premise(s):
    1. 𝑨 by premise.          — 𝑨
    2. ∀𝑥 𝑨 by 1, Gen.        — 𝑨
    3. ∀𝑥 𝑨 ⇒ 𝑪 by premise.  — ∀𝑥 𝑨 ⇒ 𝑪
    4. 𝑪 by 2, 3, MP.         — 𝑨, ∀𝑥 𝑨 ⇒ 𝑪
    conclusion by 4, Gen.      — 𝑨, ∀𝑥 𝑨 ⇒ 𝑪
  ∎


end theory TK1.

