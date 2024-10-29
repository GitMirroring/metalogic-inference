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
{— sublevel max 100 —}
{— unify count max 600000 —}

—input test-LI.mli
—input std/IR.mli


theory Smp. — Sample.
—  include theory IR.

  formal system.

  rule MP. formula 𝑨, 𝑩. 𝑨, 𝑨 ⇒ 𝑩 ⊢ 𝑩.

  rule CE1. formula 𝑨, 𝑩. 𝑨 ∧ 𝑩 ⊢ 𝑨.
  rule CE2. formula 𝑨, 𝑩. 𝑨 ∧ 𝑩 ⊢ 𝑩.

  rule DI1. formula 𝑨, 𝑩. 𝑨 ⊢ 𝑨 ∨ 𝑩.
  rule DI2. formula 𝑨, 𝑩. 𝑩 ⊢ 𝑨 ∨ 𝑩.

  rule DS1. formula 𝑨, 𝑩. 𝑨 ∨ 𝑩, ¬𝑨 ⊢ 𝑩.

  end formal system.


{— trace result —}

{— thread count 0 —}


  lemma “S1a”. formula 𝑨, 𝑩, 𝑪, 𝑫, 𝑬, 𝑭.
    (𝑨 ∨ 𝑩) ∧ ¬𝑪, ¬𝑪 ⇒ (𝑫 ∧ ¬𝑨), 𝑩 ⇒ (𝑨 ∨ 𝑬) ⊢ 𝑬 ∨ 𝑭
  proof
    by DI1: DS1: MP; CE2: DS1; MP: CE1; CE2; CE2: MP: CE2. —0.28s
  ∎

end theory Smp.

