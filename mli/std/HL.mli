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


theory HL. — Hoare Logic, for proving computer program consistency.

[— The Hoare triples traditionally written {P} C {Q} for partial correctness (ignoring
program termination), and [P] C [Q] for total correctness (with proof of program termination)
are here written, to emphasize the nature of a triple and get non-conflicting syntax, as:
  <P| C |Q>
—]

  formal system.
    atom 𝕗, 𝕥. — False, true.
    object °𝒙, °𝒗. object 𝒆. code 𝑆, 𝑇.
    formula 𝑨, 𝑩, 𝑪, 𝑫, 𝑰, 𝑷, 𝑸, 𝑹, 𝑺.


    — Empty statement, also called skip.
    axiom E. {𝑷} {𝑷}.
    axiom E1. {𝑷}∅{𝑷}.

    — Assignment.
    axiom A. {𝑷[𝒙 ⤇ 𝒆]}𝒙 ≔ 𝒆{𝑷}. — Hoare assignment.
    axiom A1. {𝑷}𝒙 ≔ 𝒆{∃𝒗: 𝒙 = 𝒆[𝒙 ⤇ 𝒗] ∧ 𝑷[𝒗 ⤇ 𝒙]}.  — Floyd assignment.

    — Composition rules.
    rule C. {𝑷}𝑆{𝑸}, {𝑸}𝑇{𝑹} ⊢ {𝑷}𝑆; 𝑇{𝑹}.
    rule C1. {𝑷}𝑆{𝑸}, 𝑸 ⇒ 𝑹, {𝑹}𝑇{𝑺} ⊢ {𝑷}𝑆; 𝑇{𝑺}.

    — Conditional.
    rule D. {𝑪 ∧ 𝑷}𝑆{𝑸}, {¬𝑪 ∧ 𝑷}𝑇{𝑸} ⊢ {𝑷}if 𝑪 then 𝑆 else 𝑇{𝑸}.
    rule D1. {𝑪 ∧ 𝑷}𝑆{𝑸}, {¬𝑪 ∧ 𝑷}𝑇{𝑹} ⊢ {𝑷}if 𝑪 then 𝑆 else 𝑇{(𝑪 ⇒ 𝑸)∧(¬𝑪 ⇒ 𝑹)}.

    — Consequence.
    rule F. 𝑨 ⇒ 𝑩, {𝑩}𝑆{𝑪}, 𝑪 ⇒ 𝑫 ⊢ {𝑨}𝑆{𝑫}.
    rule F1. 𝑨 ⇒ 𝑩, {𝑩}𝑆{𝑪} ⊢ {𝑨}𝑆{𝑪}.
    rule F2. {𝑨}𝑆{𝑩}, 𝑩 ⇒ 𝑪 ⊢ {𝑨}𝑆{𝑪}.

    — While rule, with loop invariant 𝑰 and loop condition 𝑩.
    rule W. {𝑰 ∧ 𝑪}𝑆{𝑰} ⊢ {𝑰}while 𝑪 do 𝑆{¬𝑪 ∧ 𝑰}.

[—
  — Loop, where 𝑆 has internal break statements of the form 'ξ↓𝑖: if 𝑸↓𝑖 break', where the labels ξ↓𝑖 identify the point in the code.
  rule L. {𝑷}𝑆{𝑷} ⊢ {𝑷}loop 𝑆{𝕗; ξ↓𝑖: 𝑸↓𝑖}. — Loop.

  — Exceptions:
  axiom X1. {𝑷}throw 𝜉{𝕗; 𝜉 ⤳ 𝑷}.
  rule X2. {𝑷}𝑆{𝑸; 𝜉 ⤳ 𝑹, 𝜁 ≠ 𝜉, 𝜁 ⤳ 𝑺}, {𝑹}𝑡{𝑸; 𝜁 ⤳ 𝑺} ⊢ {𝑷}try 𝑆 catch 𝜉 ⤳ 𝑡{𝑸; 𝜁 ⤳ 𝑺}.
—]

  end formal system.

end theory HL.

