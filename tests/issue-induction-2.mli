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


theory TS1.  — Test theory S (number theory).
—  include theory SM.
—  include theory IR.
  formal system.

  — Object variable substitution, Kleene p. 101:
  rule OVS. formula 𝑪 object °𝒛 object 𝒖.
  —𝑪 ⊢ 𝑪[𝒛 ⤇ 𝒖].
  𝑪 ⊢⁽𝒛⁾ 𝑪[𝒛 ⤇ 𝒖]. — 𝒛 is varied in deduction

  rule OVSO. formula 𝑪 object °𝒛 object 𝒖.
  𝑪 ⊢ 𝑪[𝒛 ⤇ 𝒖].

  end formal system.

{— thread count 0 —}

{— trace result —}
{— trace unspecializable —}
{— trace variable label —}
—{— trace unify —} {— trace solve —}

  — False: variation of 𝑥 not indicated.
  lemma Q2a0. object °𝑥 object 𝒕 predicate constant 𝑃.
    𝑃(𝑥) ⊢ 𝑃(𝒕)
  by OVS: premise.

  {— expand_implicit_premise —}

  — True
  lemma Q2a. object °𝑥 object 𝒕 predicate constant 𝑃.
    𝑃(𝑥) ⊢⁽𝑥⁾ 𝑃(𝒕)
  by OVS: premise ⊢.


  — True
  lemma Q2b. object °𝑥, °𝑦 object 𝒕 predicate constant 𝑃.
    𝑃(𝑥, 𝑦) ⊢⁽𝑥 𝑦⁾ 𝑃(𝒕, 𝒕)
  by OVS: premise ⊢.


  — Without explicit premise:

  — True
  lemma Q2c. object °𝑥 object 𝒕 predicate constant 𝑃.
    𝑃(𝑥) ⊢⁽𝑥⁾ 𝑃(𝒕)
  by OVS:.


  — True
  lemma Q2d. object °𝑥, °𝑦 object 𝒕 predicate constant 𝑃.
    𝑃(𝑥, 𝑦) ⊢⁽𝑥 𝑦⁾ 𝑃(𝒕, 𝒕)
  by OVS:.


end theory TS1.



