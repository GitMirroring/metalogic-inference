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

{— level max 100 —}
{— sublevel max 10000 —}
{— unify count max 600000 —}


—input std/SM.mli
—input std/IR.mli


theory TM.  — Test meta.
—  include theory SM.
—  include theory IR.
  formal system.

  
  axiom S6. object 𝑥, 𝑦 function constant s. 𝑥 + s(𝑦) = s(𝑥 + 𝑦).
  rule S2a. object 𝑥, 𝑦 function constant s. 𝑥 = 𝑦 ⊢ s(𝑥) = s(𝑦).

  rule T1C. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒚, 𝒚 = 𝒛 ⊢ 𝒙 = 𝒛.

  rule T1D. object 𝒙, 𝒚, 𝒛.
    𝒙 = 𝒛, 𝒚 = 𝒛 ⊢ 𝒙 = 𝒚.

  end formal system.

{— thread count 0 —}
{— proof count 3 —}

{— trace result —}
—{— trace proof —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace unify —}{— trace statement —}


  — Valid proofs:
  — T1C: S6; T1D: S2a; S6: premise ⊢.
  — T1D: S6; T1D: S6; S2a: premise ⊢.
  — T1D: T1C; S6: S6; S2a: premise ⊢.

  — Check:
  — T1D: T1C; S6: T1D; T1C: S6; S6; S6; S2a: premise ⊢.

  — First premise (𝒙 = 𝒚) is redundant.
  lemma a. object 𝒙, 𝒚, 𝒛 function constant s.
    𝒙 = 𝒚, 𝒙 + 𝒛 = 𝒚 + 𝒛 ⊢ 𝒙 + s(𝒛) = 𝒚 + s(𝒛)
  by T1D, S6, T1C, S2a.
—  by T1C, T1D: T1C, T1D, S6: S6, S2a. — Can set {— proof count 0 —}.
—  by T1C: S6; T1D: S2a; S6: premise ⊢, T1D.

  — T1D: T1C; S6: S6; S2a: 2. — T1D, S6, T1C, S2a, 2.
  —by T1C: T1D; T1D. — T1D, T1C.


end theory.



