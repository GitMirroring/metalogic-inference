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


input std/LM.mli


theory KK. — Quantification: Predicate calculus by Kleene, p. 82.
  include theory LM.

  formal system. 
    formula 𝑨, 𝑩  object 𝒕  object °𝒙.

  [— Axioms 1-3 of Mendelson, p.57, are here included from theory L
     where they are named A1, A2, A3. Modus ponens (MP) is likewise
     included from theory L. Mendelson axioms 4 (resp. 5)
     are here called K1 (resp. K2). —]


  — Treated as axioms in Mendelson:
  rule A9. 𝒙 not free in 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑨 ⇒ ∀𝒙 𝑩.   — Generalization.
  rule A10. 𝒕 free for 𝒙 in 𝑨 ⊢ ∀𝒙 𝑨 ⇒ 𝑨[𝒙⤇𝒕].    — Specialization

  rule A11. 𝒕 free for 𝒙 in 𝑨 ⊢ 𝑨[𝒙⤇𝒕] ⇒ ∃𝒙 𝑨.  — Existence.
  rule A12. 𝒙 not free in 𝑩, 𝑨 ⇒ 𝑩 ⊢ ∃𝒙 𝑨 ⇒ 𝑩. — Existence.

  end formal system.

end theory KK.

