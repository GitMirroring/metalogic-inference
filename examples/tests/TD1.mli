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

input std/SM.mli

theory TD1. — Test definitions.
  include theory SM.

  formal system.

    axiom S5a. object 𝒙. 𝒙 = 𝒙 + 0.

  end formal system.


  definition D6. function f  object t.
    f(t) ≔ t + 0.

  definition D7. function g  object u.
    g(u) ≔ 0 + u.


  lemma Xf. function f, g.
    f(0) = g(0)
  proof
    1. f(0) = 0 by D6, S5.
    2. g(0) = 0 by D7, S5.
    3. 0 = 0 by S1, S5, MP.
    1a. 0 = f(0) by D6, S5a.
    2a. 0 = g(0) by D7, S5a.
    conclusion by 1a, 2a, 3, S1, MP.
  ∎


{— trace result —}

  — Fails, as not true for every choice of t, i.e., the interpretation
  — is that 0 + 0 = 0 follows from all versions of the premise t + 0 = t,
  — which is not true if t is not equal to 0, corresponding to the
  — closed formula ∀x: (x + 0 = x ⇒ 0 + 0 = 0), which is not true.
  — True is however (∀x: (x + 0 = x) ⇒ 0 + 0 = 0, see the next lemma.
  lemma Xs. object t.
    t + 0 = t ⊢ 0 + 0 = 0
  by premise.


  — This version succeeds, as ∀x: x + 0 = x is applicable to
  — all substitutions of x.
  lemma Xt.
    ∀x: x + 0 = x ⊢ 0 + 0 = 0
   conclusion by premise, K1.


end theory TD1.

