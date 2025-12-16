[— Copyright (C) 2017, 2021-2025 Hans Åberg.

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

theory TML. — Test ML (MetaLogic).

{— trace result —}

  lemma N1. formula A, B.
    ~A ⊢ ~A
  proof conclusion by premise.
  ∎


  lemma N2. formula A, B.
    A ⊢ ~A
  proof conclusion by premise.
  ∎


  lemma N3. formula A, B.
    ~A ⊢ A
  proof conclusion by premise.
  ∎


  lemma N4. formula A, B.
    A ⊢ ~fail
  proof conclusion by premise.
  ∎


  lemma C1. formula A, B.
    A | B ⊢ B | A
  proof conclusion by premise.
  ∎


  lemma C2. formula A, B.
    A | B ⊢ A
  proof conclusion by premise.
  ∎


  lemma C2b. formula A, B.
    A | B ⊢ A, B
  proof conclusion by premise.
  ∎


  lemma C2c. formula A, B.
    A, B ⊢ A | B
  proof conclusion by premise.
  ∎


  lemma C3. formula A, B.
    A ⊢ A | B
  proof conclusion by premise.
  ∎


  lemma C4. formula A, B, C.
    (A ⊢ C), (B ⊢ C) ⊢ (A | B ⊢ C)
  proof conclusion by premise.
  ∎


  lemma B0. formula A, B.
    A, B ⊢ A
  proof
    1. B, A by premise.
    conclusion by 1.
  ∎


  lemma B1. formula A, B.
    A, B ⊢ A, B
  proof conclusion by premise. ∎


  lemma B2. formula A, B.
    A, B ⊢ B, A
  proof
    1. A by premise.
    2. B by premise.
    conclusion by 1, 2.
  —  conclusion by 1, 2, B1.
  ∎


  lemma B3. formula A, B.
    A, B ⊢ B, A
  proof conclusion by premise, B1. ∎


  lemma B4. formula A, B, C, D.
  —  (A ⊢ B, C), D ⊢ (A ⊢ B), (A ⊢ C).
    (A ⊢ B, C) ⊢ (A ⊢ B), (A ⊢ C)
  proof
    conclusion by premise.
  ∎

end theory TML.

