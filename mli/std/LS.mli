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


theory LS1. — Logic: Propositional calculus by Sobociński.

  formal system.
    atom 𝕗, 𝕥. — False, true. Not in core of theory.
    formula 𝑨, 𝑩, 𝑪.

  axiom A1. (𝑨 ⇒ 𝑩) ⇒ (¬𝑩 ⇒ (𝑨 ⇒ 𝑪)).
  axiom A2. 𝑨 ⇒ (𝑩 ⇒ (𝑪 ⇒ 𝑨)).
  axiom A3. (¬𝑨 ⇒ 𝑩) ⇒ ((𝑨 ⇒ 𝑩) ⇒ 𝑩).

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

end theory LS1.


theory LS2. — Logic: Propositional calculus by Sobociński.

  formal system.
    atom 𝕗, 𝕥. — False, true. Not in core of theory.
    formula 𝑨, 𝑩, 𝑪.

  axiom A1. ¬𝑨 ⇒ (𝑨 ⇒ 𝑩).
  axiom A2. 𝑨 ⇒ (𝑩 ⇒ (𝑪 ⇒ 𝑨)).
  axiom A3. (¬𝑨 ⇒ 𝑪) ⇒ ((𝑩 ⇒ 𝑪) ⇒ ((𝑨 ⇒ 𝑩) ⇒ 𝑪)).

  — Modus ponens
  rule MP. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

  — Deduction theorem
  — Entered as an axiom in the absence of the appropriate metatools.
  postulate DT. formula 𝑨, 𝑩. (𝑨 ⊢ 𝑩) ⊢ 𝑨 ⇒ 𝑩.
  postulate DT1. formula 𝑨, 𝑩, 𝑭. (𝑭, 𝑨 ⊢ 𝑩) ⊢ (𝑭 ⊢ 𝑨 ⇒ 𝑩).
  postulate DT2. formula sequence 𝜞 formula 𝑨, 𝑩. (𝜞, 𝑨 ⊢ 𝑩) ⊢ (𝜞 ⊢ 𝑨 ⇒ 𝑩).

  definition D1. 𝑨 ∧ 𝑩 ≔ ¬(𝑨 ⇒ ¬𝑩).  
  definition D2. 𝑨 ∨ 𝑩 ≔ ¬𝑨 ⇒ 𝑩.
  definition D3. 𝑨 ⇔ 𝑩 ≔ (𝑨 ⇒ 𝑩) ∧ (𝑩 ⇒ 𝑨).
  axiom D4. 𝕥.
  definition D5. 𝕗 ≔ ¬𝕥.

  end formal system.

end theory LS2.

