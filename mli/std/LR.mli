[— Copyright (C) 2017, 2021-2026 Hans Åberg.

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


theory LR. — Logic: Propositional calculus by Frege.

  formal system.
    atom 𝕗, 𝕥. — False, true. Not in core of theory.
    formula 𝑨, 𝑩, 𝑪.

  axiom A1. 𝑨 ⇒ (𝑩 ⇒ 𝑨).
  axiom A2. (𝑨 ⇒ 𝑩) ⇒ ((𝑩 ⇒ 𝑪) ⇒ (𝑨 ⇒ 𝑪)).
  axiom A3. (𝑨 ⇒ (𝑩 ⇒ 𝑪)) ⇒ (𝑩 ⇒ (𝑨 ⇒ 𝑪)).
  axiom A4. ¬¬𝑨 ⇒ 𝑨.
  axiom A5. (𝑨 ⇒ ¬𝑨) ⇒ ¬𝑨.
  axiom A6. (𝑨 ⇒ ¬𝑩) ⇒ (𝑩 ⇒ ¬𝑨).

  — Modus ponens
  rule MP. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

  — Deduction theorem
  postulate DT. formula sequence 𝜞 formula 𝑨, 𝑩.
    𝜞, 𝑨 ⊢ 𝑩 ⊩ 𝜞 ⊢ 𝑨 ⇒ 𝑩.

  definition D1. 𝑨 ∧ 𝑩 ≔ ¬(𝑨 ⇒ ¬𝑩).  
  definition D2. 𝑨 ∨ 𝑩 ≔ ¬𝑨 ⇒ 𝑩.
  definition D3. 𝑨 ⇔ 𝑩 ≔ (𝑨 ⇒ 𝑩) ∧ (𝑩 ⇒ 𝑨).
  axiom D4. 𝕥.
  definition D5. 𝕗 ≔ ¬𝕥.

  end formal system.

end theory LR.


theory LRo. — Logic: Propositional calculus by Rosser, cf. Mendelson, p. 40.

  formal system.
    atom 𝕗, 𝕥. — False, true. Not in core of theory.
    formula 𝑨, 𝑩, 𝑪.

  — In the following axioms, ⇒ should be expanded using this definition:
  definition D1. 𝑨 ⇒ 𝑩 ≔ ¬(𝑨 ∧ ¬𝑩).

  axiom A1. 𝑨 ⇒ 𝑨 ∧ 𝑨.
  axiom A2. 𝑨 ∧ 𝑩 ⇒ 𝑨.
  axiom A3. (𝑨 ⇒ 𝑩) ⇒ (¬(𝑩 ∧ 𝑪) ⇒ ¬(𝑪 ∧ 𝑨)).

  — Modus ponens
  rule MP. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

  — Deduction theorem
  — Entered as an axiom in the absence of the appropriate metatools.
  postulate DT. formula 𝑨, 𝑩. (𝑨 ⊢ 𝑩) ⊢ 𝑨 ⇒ 𝑩.


  definition D2. 𝑨 ∨ 𝑩 ≔ ¬(¬𝑨 ∧ ¬𝑩).
  definition D3. 𝑨 ⇔ 𝑩 ≔ (𝑨 ⇒ 𝑩) ∧ (𝑩 ⇒ 𝑨).
  axiom D4. 𝕥.
  definition D5. 𝕗 ≔ ¬𝕥.

  end formal system.

end theory LRo.

