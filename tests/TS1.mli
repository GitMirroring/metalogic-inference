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

input std/SM.mli

theory TS1.  — Test theory S (number theory).
  include theory SM.

  formal system.
  rule TA1. formula 𝑨. 𝑨 ⊢ 𝑨 ∧ 𝑨.
  rule TA2. formula 𝑨, 𝑩, 𝑪. 𝑩, 𝑨 ∧ 𝑩 ⇒ 𝑪 ⊢ 𝑨 ⇒ 𝑪.

  rule CI. formula 𝑨, 𝑩. 𝑨, 𝑩 ⊢ 𝑨 ∧ 𝑩. — Conjunction introduction.


  — Course-of-values induction
  rule CVIA. formula 𝑨 object °𝒙, °𝒚 predicate 𝑷: 𝒚 ↦ 𝑨 function constant s.
    𝑷(0), (∀𝒚: 𝒚 ≤ 𝒙 ⇒ 𝑷(𝒚)) ⇒ 𝑷(s(𝒙)) ⊢⁽¹𝒙⁾ 𝑷(𝒙).

  rule CVIr. formula 𝑩 object °𝒙, °𝒚, °𝒛, 𝒕 predicate 𝑷: 𝒛 ↦ 𝑩 function constant s formula sequence 𝜞.
    (𝜞 ⊢ 𝑷(0); (𝜞, 𝒚 ≤ 𝒙 ⊢₍𝒙₎ 𝑷(𝒚) ⊩⁽𝒚⁾₍𝒙₎ 𝜞  ⊢ 𝑷(s(𝒙)))) ⊩¹ 𝜞 ⊢ 𝑷(𝒕).


  rule CVI2. formula 𝑨 object °𝒙, °𝒚 predicate variable 𝑷 function constant s.
    𝑷(0), (∀𝒚: 𝒚 ≤ 𝒙 ⇒ 𝑷(𝒚)) ⇒ 𝑷(s(𝒙)) ⊢⁽¹𝒙⁾ 𝑷(𝒙).


  rule IR. formula 𝑨 predicate 𝑷: 𝒚 ↦ 𝑨
    object °𝒙, 𝒕 function constant s formula sequence 𝜞.
      𝜞 ⊢ 𝑷(0); 𝜞, 𝑷(𝒙) ⊢₍𝒙₎ 𝑷(s(𝒙)) ⊩ 𝜞 ⊢ 𝑷(𝒕).

  rule IRz. formula 𝑨 object °𝒙, 𝒕 function constant s formula sequence 𝜞.
    𝜞 ⊢ (𝒙 ↦ 𝑨)(0); 𝜞, 𝑨 ⊢₍𝒙₎ (𝒙 ↦ 𝑨)(s(𝒙)) ⊩ 𝜞 ⊢ (𝒙 ↦ 𝑨)(𝒕).
  — Gives the same result:
  — 𝜞 ⊢ (𝒙 ↦ 𝑨)(0); 𝜞, (𝒙 ↦ 𝑨)(𝒙) ⊢₍𝒙₎ (𝒙 ↦ 𝑨)(s(𝒙)) ⊩ 𝜞 ⊢ (𝒙 ↦ 𝑨)(𝒕).


  — Inequality ≤ reflexive.
  axiom ineqr. object 𝑥. 𝑥 ≤ 𝑥.

  rule S1b. object 𝑥, 𝑦, 𝑧.
    𝑥 = 𝑦, 𝑦 = 𝑧 ⊢ 𝑥 = 𝑧.

  rule S2b. object 𝑥, 𝑦 function constant s. 𝑥 = 𝑦 ⊢ s(𝑥) = s(𝑦).

  axiom S5. object 𝑥. 𝑥 + 0 = 𝑥.
  axiom S6. object 𝑥, 𝑦 function constant s. 𝑥 + s(𝑦) = s(𝑥 + 𝑦).


  end formal system.

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}


  lemma T1. object x function constant s. x = x
  proof
    by MP, TA1, S1, S5. — MP: S5; MP: S5; S1. — MP, TA1, S1, S5.
  ∎

  {— unexpand_implicit_premise —}
  
  lemma T2. object x, y function constant s. x = y ⇒ y = x
  by DT: MP: T1; MP: S1. — DT, T1, MP, S1.

  — Course-of-values induction

  {— expand_implicit_premise —}

  — Induction proof, using course-of-values induction.
  — Fully automated, does not require an explicit predicate to
  — be defined, nor how the statements used should be applied:
  lemma X0CV. object 𝑥. 0 + 𝑥 = 𝑥
  proof
    by CVIr: S5; S1b: S6; S2b: premise ⊢: ineqr.
    —by CVIr, S5, S1b, S6, S2b, ineqr.
  ∎

  {— unexpand_implicit_premise —}

  — Using predicate:
  lemma CVIq. formula 𝑩 object °𝒙, °𝒚, 𝒕 predicate 𝑷: 𝒚 ↦ 𝑩 function constant s formula sequence 𝜞.
    𝜞 ⊢ 𝑷(0); 𝜞, ∀𝒚: 𝒚 ≤ 𝒙 ⇒ 𝑷(𝒚) ⊢₍𝒙₎ 𝑷(s(𝒙)) ⊩ 𝜞 ⊢ 𝑷(𝒙)
  proof
    by CVIA: DT.
  ∎


  — Using predicate variable (uninterpreted):
  lemma CVIs. formula 𝑨 object °𝒙, °𝒚, 𝒕 predicate variable 𝑷 function constant s formula sequence 𝜞.
    𝜞 ⊢ 𝑷(0); 𝜞, ∀𝒚: 𝒚 ≤ 𝒙 ⇒ 𝑷(𝒚) ⊢₍𝒙₎ 𝑷(s(𝒙)) ⊩ 𝜞 ⊢ 𝑷(𝒙)
  proof
    by CVI2: DT.
  ∎


  — Should be:
  — A(0), ∀x: A(x) ⇒ A(s(x)) ⊢ ∀x A(x).
  lemma IRa. — Induction Rule.
    predicate variable A function constant s.
    A(0) ∧ ∀x: A(x) ⇒ A(s(x)) ⊢ ∀x A(x)
  by MP: S9a.

  [—
  proof by MP: premise, S9a. ∎
  proof
    P1. A(0) ∧ (∀x: A(x) ⇒ A(s(x))) by premise.
    by MP, S9a, P1.
  ∎
  —]

[—
{— trace result —}  {— trace proof —}  {— trace variable type —}  {— trace bind —}
 {— trace unify —}  {— trace substitute —}
—]

  — Changes ∧ of IRa to a formula set comma:
  lemma IR1.
    predicate variable A function constant s.
    A(0), ∀x: A(x) ⇒ A(s(x)) ⊢ ∀x A(x)
  proof
[—
    1. A(0) by premise.
    2. ∀x: A(x) ⇒ A(s(x)) by premise.
    3. A(0) ∧ (∀x: A(x) ⇒ A(s(x))) by CI: 1; 2. — 1, 2, CI.
—]
    by IRa: CI. — IRa, 3.
  ∎

[—
{— trace result —}  {— trace proof —}  {— trace unify —}  {— trace substitute —}
{— trace variable type —}  {— trace bind —}
—]


—  {— trace result —}
—  {— trace proof —}
— {— trace variable type —}  {— trace bind —}
[— {— trace unify —}
 {— trace substitute —}  {— trace split —}
—]

—{— conditional proof —}
{— strict proof —}

  — Induction proof, fully automated, does not require an explicit predicate to
  — be defined, nor how the statements used should be applied:
  — IRz, S5, S1b, S6, S2b. —IRz: S5; S1b: S6; S2b.
  lemma X. object x. 0 + x = x
  proof
    by IR: S5; S1b: S6; S2b.
    —by IR, S5, S1b, S6, S2b.
  ∎


  — Induction proof, fully automated, does not require an explicit predicate to
  — be defined, nor how the statements used should be applied:
  — IRz, S5, S1b, S6, S2b. —IRz: S5; S1b: S6; S2b.
  lemma X0. object x. 0 + x = x
  proof
    by IRz: S5; S1b: S6; S2b.
    —by IRz, S5, S1b, S6, S2b.
  ∎


  — Induction proof, fully automated, does not require an explicit predicate to
  — be defined, nor how the statements used should be applied:
  — S9c, S5, Gen, DT, S1b, S6, MP, S2. — S9c: S5; Gen: DT: S1b: S6; MP: S2.
  — This version uses Gen and DT, requiring a more extensive proof search.
  —
  — The transitive rule axiom S1b 𝑥 = 𝑦, 𝑦 = 𝑧 ⊢ 𝑥 = 𝑧 is used, as the
  — asymmetrical axiom S1 𝑥 = 𝑦 ⇒ (𝑥 = 𝑧 ⇒ 𝑦 = 𝑧) requires a longer proof.
  lemma X1. ∀x: 0 + x = x
  proof
    by S9c: S5; Gen: DT: S1b: S6; MP: S2.
  —  by S9c, S5, Gen, DT, S1b, S6, MP, S2. — S9c: S5; Gen: DT: S1b: S6; MP: S2.

    definition D5. predicate constant B object t.
      B(t) ≔ 0 + t = t.

    1. predicate constant B. B(0) by D5, S5.

    a. object x predicate constant B function constant s. B(x) ⊢ B(s(x))
    proof
      a1. 0 + x = x by D5, premise.
      a2. 0 + s(x) = s(0 + x) by S6.
      a3. s(0 + x) = s(x) by MP: S2, a1.
      — S1a is 𝑥 = 𝑦, 𝑥 = 𝑧 ⊢ 𝑦 = 𝑧; must have S1b 𝑥 = 𝑦, 𝑦 = 𝑧 ⊢ 𝑥 = 𝑧.
      a4. 0 + s(x) = s(x) by a2, a3, S1b. — MP: S1a, S2, a1, S6.
      by D5, a4.
    ∎

    by IR1, D5: 1; Gen: DT: a.
    —by D5, IR1, 1, Gen, DT, a. — IR1₍D5₎: 1; Gen: DT: a.

    — Original, deterministic proof:
    2. object x predicate constant B function constant s. B(x) ⇒ B(s(x)) by DT, a.
    3. predicate constant B function constant s. ∀x: B(x) ⇒ B(s(x)) by Gen, 2.
    4. predicate constant B.∀x B(x) by IR1, 1, 3.
    by D5, 4.
  ∎


—{— untrace all —}

{— trace all —}
{— untrace all —}

end theory TS1.

