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

input std/LM.mli

theory TL1.  — Test theory LM (propositional calculus).
  include theory LM.


  {— trace result —} [— {— trace proof —}  {— trace variable type —}  {— trace bind —}
  {— trace unify —}  {— trace substitute —}
  —]

  lemma “1.7”. formula A. ⊢ A ⇒ A — Mendelson, p. 31.
  proof — Mendelson, p. 32.
    conclusion by MP: A1; MP: A1; A2.
  —  conclusion by MP: A1, MP: A1, A2.
  —  conclusion by A1, A2, MP.
  [—
    1. ((A ⇒ ((A ⇒ A) ⇒ A)) ⇒ ((A ⇒ (A ⇒ A)) ⇒ (A ⇒ A))) by A2.
    2. A ⇒ ((A ⇒ A) ⇒ A) by A1.
    3. (A ⇒ (A ⇒ A)) ⇒ (A ⇒ A) by MP, 1, 2.
    4. A ⇒ (A ⇒ A) by A1.
    conclusion by MP, 3, 4.
  —]
  ∎


  — Corollary 1.9 & lemma 1.10: Mendelson, p. 33ff.
  corollary “1.9i”. formula A, B, C. A ⇒ B, B ⇒ C ⊢ A ⇒ C
  proof
  [—
    conclusion by DT, premise, MP. — Cannot handle this.
    — Probably due to the limited form of DT.
  —]
    1. A ⇒ B by premise.
    2. B ⇒ C by premise.

    3. A ⊢ C
    proof
      4. A by premise.
      5. B by MP: 4, 1.
      conclusion by MP: 2, 5.
    ∎

    conclusion by DT: 3.
  ∎


  corollary “1.9ii”. formula A, B, C. A ⇒ (B ⇒ C), B ⊢ A ⇒ C
  proof
    1. A ⇒ (B ⇒ C) by premise.
    2. B by premise.

    3. A ⊢ C
    proof
      4. A by premise.
      5. B ⇒ C by MP: 4, 1.
      conclusion by MP: 2, 5.
    ∎

    conclusion by DT: 3.
  ∎


  lemma “1.10a”. formula A, B. ¬¬B ⇒ B
  proof
    1. (¬B ⇒ ¬¬B) ⇒ ((¬B ⇒ ¬B) ⇒ B) by A3.
    2. ¬B ⇒ ¬B by “1.7”.
    3. (¬B ⇒ ¬¬B) ⇒ B by “1.9ii”: 1, 2.
    4. ¬¬B ⇒ (¬B ⇒ ¬¬B) by A1.
    conclusion by “1.9i”: 3, 4.
  ∎


  lemma “1.10b”. formula A, B. B ⇒ ¬¬B
  proof
    1. (¬¬¬B ⇒ ¬B) ⇒ ((¬¬¬B ⇒ B) ⇒ ¬¬B) by A3.
    2. ¬¬¬B ⇒ ¬B by “1.10a”.
    3. (¬¬¬B ⇒ B) ⇒ ¬¬B by MP: 1, 2.
    4. B ⇒ (¬¬¬B ⇒ B) by A1.
    conclusion by “1.9i”: 3, 4.
  ∎


  lemma “1.10c”. formula A, B. ¬A ⇒ (A ⇒ B)
  proof
    a. ¬A, A ⊢ B
    proof
      1. ¬A by premise.
      2. A by premise.
      3. A ⇒ (¬B ⇒A) by A1.
      4. ¬A ⇒ (¬B ⇒ ¬A) by A1.
      5. ¬B ⇒ A by MP: 2, 3.
      6. ¬B ⇒ ¬A by MP: 1, 4.
      7. (¬B ⇒ ¬A) ⇒ ((¬B ⇒ A) ⇒ B) by A3.
      8. (¬B ⇒ A) ⇒ B by MP: 6, 7.
      conclusion by MP: 5, 8.
    ∎

    b. ¬A ⊢ A ⇒ B
    proof
      1. ¬A by premise.

      c. A ⊢ B
      proof
        c1. A by premise.
        conclusion by a: 1, c1.
      ∎

      conclusion by DT: c.
    ∎

    conclusion by DT: b.
  ∎


  lemma “1.10d”. formula A, B. (¬B ⇒ ¬A) ⇒ (A ⇒ B)
  proof
    a. ¬B ⇒ ¬A, A ⊢ B
    proof
      1. ¬B ⇒ ¬A by premise.
      2. A by premise.
      3. (¬B ⇒ ¬A) ⇒ ((¬B ⇒ A) ⇒ B) by A3.
      4. A ⇒ (¬B ⇒ A) by A1.
      5. (¬B ⇒ A) ⇒ B by MP: 1, 3.
      6. A ⇒ B by “1.9i”: 4, 5.
      conclusion by MP: 2, 6.
    ∎

    b. ¬B ⇒ ¬A ⊢ A ⇒ B
    proof
      1. ¬B ⇒ ¬A by premise.

      c. A ⊢ B
      proof
        c1. A by premise.
        conclusion by a: 1, c1.
      ∎

      conclusion by DT: c.
    ∎

    conclusion by DT: b.
  ∎


  lemma “1.10e”. formula A, B. (A ⇒ B) ⇒ (¬B ⇒ ¬A)
  proof
    a. A ⇒ B ⊢ ¬B ⇒ ¬A
    proof
      1. A ⇒ B by premise.
      2. ¬¬A ⇒ A by “1.10a”.
      3. ¬¬A ⇒ B by “1.9i”: 1, 2.
      4. B ⇒ ¬¬B by “1.10b”.
      5. ¬¬A ⇒ ¬¬B by “1.9i”: 3, 4.
      6. (¬¬A ⇒ ¬¬B) ⇒ (¬B ⇒ ¬A) by “1.10d”.
      conclusion by MP: 5, 6.
    ∎

    conclusion by DT: a.
  ∎


  lemma “1.10f”. formula A, B. A ⇒ (¬B ⇒ ¬(A ⇒ B))
  proof
    a. A ⇒ ((A ⇒ B) ⇒ B)
    proof
      b. A ⊢ (A ⇒ B) ⇒ B
      proof
        b1. A by premise.

        c. A ⇒ B ⊢ B
        proof
          c1. A ⇒ B by premise.
          conclusion by MP: b1, c1.
        ∎

        conclusion by DT: c.
      ∎

      conclusion by DT: b.
    ∎

    1. ((A ⇒ B) ⇒ B) ⇒ (¬B ⇒ ¬(A ⇒ B)) by “1.10e”.
    conclusion by “1.9i”: a, 1.
  ∎


  lemma “1.10g”. formula A, B. (A ⇒ B) ⇒ ((¬A ⇒ B) ⇒ B)
  proof
    a. A ⇒ B, ¬A ⇒ B ⊢ B — Proof by contradiction!
    proof
      a1. A ⇒ B by premise.
      a2. ¬A ⇒ B by premise.
      a3. (A ⇒ B) ⇒ (¬B ⇒ ¬A) by “1.10e”.
      a4. ¬B ⇒ ¬A by MP: a1, a3.
      a5. (¬A ⇒ B) ⇒ (¬B ⇒ ¬¬A) by “1.10e”.
      a6. ¬B ⇒ ¬¬A by MP: a2, a5.
      a7. (¬B ⇒ ¬¬A) ⇒ ((¬B ⇒ ¬A) ⇒ B) by A3.
      a8. (¬B ⇒ ¬A) ⇒ B by MP: a6, a7.
      conclusion by MP: a4, a8.
    ∎

    b. (A ⇒ B) ⊢ (¬A ⇒ B) ⇒ B
    proof
      b1. A ⇒ B by premise.

      c. ¬A ⇒ B ⊢ B
      proof
        c1. ¬A ⇒ B by premise.
        conclusion by a: b1, c1.
      ∎

      conclusion by DT: c.
    ∎

    conclusion by DT: b.
  ∎


  lemma “1.10h”. formula A, B. (A ⇒ B) ⇒ ((¬A ⇒ B) ⇒ B)
  proof
[—    a. A ⇒ B, ¬A ⇒ B ⊢ B. — Proof by contradiction!
    proof
      conclusion by MP: MP; MP: MP; A3; premise a; “1.10e”: premise a; “1.10e”.
    ∎
—]
    conclusion by DT: DT: MP: MP; MP: MP; A3; premise ⊢; “1.10e”: premise ⊢; “1.10e”.
—    conclusion by DT: DT: MP: MP, A3, “1.10e”.
—    conclusion by DT: DT: a: premise ⊢; premise ⊢.
—    conclusion by DT, MP, A3, “1.10e”.
  ∎

{— untrace all —}

end theory TL1.

