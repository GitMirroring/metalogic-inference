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
   along with this program.  If not, see <http://www.gnu.org/licenses/>. —]


input std/KM.mli


theory SM.  — Natural numbers, Mendelson:
  include theory KM.
  
  formal system.
    — predicate · = ·, · + ·, · ⋅ ·. — Implicitly defined.
    function constant s.
  

    object 𝑥, 𝑦, 𝑧.

    axiom S1. 𝑥 = 𝑦 ⇒ (𝑥 = 𝑧 ⇒ 𝑦 = 𝑧).
    axiom S2. 𝑥 = 𝑦 ⇒ s(𝑥) = s(𝑦).
    axiom S3. 0 ≠ s(𝑥).  — Not-equal ≠ in definition NE below.
    axiom S3a. ¬0 = s(𝑥).
    axiom S4. s(𝑥) = s(𝑦) ⇒ 𝑥 = 𝑦.
    axiom S5. 𝑥 + 0 = 𝑥.
    axiom S6. 𝑥 + s(𝑦) = s(𝑥 + 𝑦).
    axiom S7. 𝑥⋅0 = 0.
    axiom S8. 𝑥⋅s(𝑦) = 𝑥⋅𝑦 + 𝑥.


    — The axioms S1, S2, S4 expressed as rules, avoiding the use of MP.
    rule S1a. 𝑥 = 𝑦, 𝑥 = 𝑧 ⊢ 𝑦 = 𝑧.
    rule S2a. 𝑥 = 𝑦 ⊢ s(𝑥) = s(𝑦).
    rule S4a. s(𝑥) = s(𝑦) ⊢ 𝑥 = 𝑦.


    — Principle of mathematical induction:

    — The predicate variable 𝑷 should be unary:
    axiom S9a. predicate variable 𝑷.
      𝑷(0) ∧ (∀𝑥: 𝑷(𝑥) ⇒ 𝑷(s(𝑥))) ⇒ ∀𝑥 𝑷(𝑥).

    axiom S9b. formula 𝑨 object °𝒙.
      𝑨[𝒙⤇0] ∧ (∀𝒙: 𝑨 ⇒ 𝑨[𝒙⤇s(𝒙)]) ⇒ ∀𝒙 𝑨.

    postulate S9c. formula 𝑨 object °𝒙.
      𝑨[𝒙⤇0], ∀𝒙: 𝑨 ⇒ 𝑨[𝒙⤇s(𝒙)] ⊢ ∀𝒙 𝑨.


    — Definition of not equal.
    definition NE. object 𝑥, 𝑦.
      𝑥 ≠ 𝑦 ≔ ¬𝑥 = 𝑦.


    — Definition of inequalities.
    definition SL. object 𝑥, 𝑦.
      𝑥 < 𝑦 ≔ ∃𝒘: ¬𝒘 = 0 ∧ 𝑥 + 𝒘 = 𝑦.

    definition SLA. object 𝑥, 𝑦.
      𝑥 < 𝑦 ≔ ∃𝑤: ¬𝑤 = 0 ∧ 𝑥 + 𝑤 = 𝑦.


    definition SLE. object 𝑥, 𝑦.
      𝑥 ≤ 𝑦 ≔ 𝑥 < 𝑦 ∨ 𝑥 = 𝑦.

    definition SG. object 𝑥, 𝑦.
      𝑥 > 𝑦 ≔ 𝑦 < 𝑥.

    definition SGE. object 𝑥, 𝑦.
      𝑥 ≥ 𝑦 ≔ 𝑦 ≤ 𝑥.

    definition SNL. object 𝑥, 𝑦.
      𝑥 ≮ 𝑦 ≔ ¬𝑥 < 𝑦.

    definition SNLE. object 𝑥, 𝑦.
      𝑥 ≤ 𝑦 ≔ ¬𝑥 ≤ 𝑦.

    definition SNG. object 𝑥, 𝑦.
      𝑥 ≯ 𝑦 ≔ ¬𝑥 > 𝑦.

    definition SNGE. object 𝑥, 𝑦.
      𝑥 ≱ 𝑦 ≔ ¬𝑥 ≥ 𝑦.


    — Definition of some numbers.
    definition n1. 1 ≔ s(0).
    definition n2. 2 ≔ s(1).
    definition n3. 3 ≔ s(2).
    definition n4. 4 ≔ s(3).

  end formal system.

end theory SM.

