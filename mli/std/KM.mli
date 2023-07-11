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


theory KM. — Quantification: Predicate calculus by Mendelson.
  include theory LM.

  formal system. 
    formula 𝑨, 𝑩 object 𝒕 object °𝒙.

  [— Axioms 1-3 of Mendelson, p.57, are here included from theory L
     where they are named A1, A2, A3. Modus ponens (MP) is likewise
     included from theory L. Mendelson axioms 4 (resp. 5)
     are here called K1 (resp. K2). —]


  — Treated as axioms in Mendelson:

[—
  axiom K1. 𝒕 free for 𝒙 in 𝑨 ⊩ (∀𝒙 𝑨) ⇒ 𝑨[𝒙⤇𝒕].
—  rule K1a. 𝒕 free for 𝒙 in 𝑨 ⊩ ∀𝒙 𝑨 ⊢ 𝑨[𝒙⤇𝒕].   — Not in Mendelson theory.
  rule K1a. ∀𝒙 𝑨 ⊢ 𝑨[𝒙⤇𝒕].   — Not in Mendelson theory.
  rule K1b. formula 𝑨 object 𝒕 object °𝒙. ∀𝒙 𝑨 ⊢ 𝑨[𝒙⤇𝒕].
—]

  — Specialization or particularization:
  rule K1. formula 𝑨 object °𝒙 object 𝑡. ∀𝒙 𝑨 ⊢ 𝑨[𝒙⤇𝑡].

  axiom K2. 𝒙 not free in 𝑨 ⊩ (∀𝒙: 𝑨 ⇒ 𝑩) ⇒ (𝑨 ⇒ ∀𝒙 𝑩).
  
  rule Gen. formula 𝑨 object °𝒙.
    𝑨 ⊢⁽𝒙⁾ ∀𝒙 𝑨.

  — Not in Mendelson theory.
  rule Ex. 𝒕 free for 𝒙 in 𝑨 ⊩ 𝑨[𝒙⤇𝒕] ⊢ ∃𝒙 𝑨. — Existence.
  postulate K3. formula sequence 𝜞 formula 𝑨, 𝑩. 𝜞, 𝑨 ⊢ 𝑩 ⊩ 𝜞, ∃𝒙 𝑨 ⊢ 𝑩.

  end formal system.

end theory KM.

