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


input std/IR.mli


theory G. — Group.
  include theory IR.

  formal system. 
—    function constant ⋅. — binary infix.
  
    object x, y, z.

  axiom G1. (x⋅y)⋅z = x⋅(y⋅z).
  axiom G2. ∃ x: (∀ y x⋅y = y) ∧ ∀ y ∃ z z⋅y = x.
  
  end formal system.

  constant e.
—  function constant ^-1. — unary postfix.
  
  definition g1. predicate P object x.
    P(x) ≔ (∀ y x⋅y = y) ∧ ∀ y ∃ z z⋅y = x.

  lemma g2. predicate P object u, v. ∀ u, v: P(u) ∧ P(v) ⇒ u = v
  proof
    a. P(u), P(v) ⊢ u = v
    proof
      a1. ∀ y u⋅y = y by g1, premise.
      a2. ∀ y v⋅y = y by g1, premise.
      a3. ∀ y ∃ z z⋅y = u by g1, premise.
      a4. u⋅v = v by a1.
      a5. v⋅v = v by a2.
      a6. ∃ z z⋅v = u by a3.

      b. object z. z⋅v = u ⊢ u = v
      proof
        b1. (z⋅v)⋅v = u⋅v by premise. — Equality axiom a = b ⇒ f(a) = f(b).
        b2. z⋅(v⋅v) = v by b1, G1, a4.
        b3. z⋅v = v by b2, a5. — Equality axiom.
        conclusion by b3, premise. — And equality axioms.
      ∎

      a7. ∃ z z⋅v = u ⊢ u = v by a1. — ... — existence introduction.
      conclusion by a7, a6.
    ∎

    conclusion by a, DT.
  ∎
[—
  defining axiom unit. (∀ y e⋅y = y) ∧ ∀ y ∃ z z⋅y = e.
  proof
    1. ∃! P(x) by G2, g1, g2.
    2. conclusion by 1. — ... — Defining axiom theorem.
  ∎ 

  lemma g3. x⋅y = x⋅z ⇒ y = z.
  proof
    1. ∃ x' ∀ y x'⋅y = e by unit.

    a. x'⋅y = e, x⋅y = x⋅z ⊢ y = z.
    proof
      a1. x'⋅(x⋅y) = x'⋅(x⋅z) by premise, ... — equality axiom
      a2. (x'⋅x)⋅y = (x'⋅x)⋅z by G1, ... — equality axiom.
      a3. e⋅y = e⋅z by premise. ... — equality axiom.
      conclusion by a3, unit.
    ∎

    conclusion by 1, a, DTx, existence introduction.
  ∎

  lemma g4. z⋅e = z.
  proof
    1. e⋅e = e by unit.
    2. ∃ z' z'⋅z = e by unit.

    a. z'⋅z = e ⊢ z⋅e = z.
      a1. (z'⋅z)⋅e = z'⋅z by 1, premise, ... — equality axiom.
      a2. z'⋅(z⋅e) = z'⋅z by G1.
      conclusion by g3.
    ∎

    conclusion by 2, a, existence introduction.
  ∎

  lemma g5. s⋅x = e ∧ x⋅t = e ⇒ s = t.
  proof
    1. s = s⋅e by g4.
    2. s⋅e = s⋅(x⋅t) = (s⋅x)⋅t = e⋅t = t by unit, G1.
    conclusion by 1, 2.
  ∎

  corollary g6. s⋅x = e ⇒ x⋅s = e.
  proof
    1. ∃ s' s'⋅s = e by unit.
    2. s' = x by g5.
    concluson by 1, 2.
  ∎

  definition g7. Q(z) ≔ z⋅y = e.

  lemma g8. ∀ s, t: Q(s) ∧ Q(t) ⇒ s = t.
  proof
    1. s = e⋅s = (t⋅y)⋅s = t⋅(y⋅s) = t⋅e = t
      by unit, g7, premise, G1, g4.
  ∎

  defining axiom inverse. x^-1⋅x = e.
  proof
    1. ∃! x Q(x) by g7, g8.
    conclusion by ... — Defining axiom theorem.
  ∎
—]
end theory G.

[—
theory AG. — Abelian group.

  include theory G
    write
      e as 0,
      object x. x^-1 as -x,
     ⋅as +.

  formal system. 
    object x, y.

    axiom A1. x + y = y + x.
  
  end formal system.

end theory AG.

theory NR. — Non-unitary ring.

  include theory AG.

  formal system.
    object x, y, z.
    axiom A. (x⋅y) + z = x⋅(y⋅z).    — Associative law.
    axiom DL. x⋅(y + z) = x⋅y + x⋅z. — Distributive to the left.
    axiom DR. (x + y)⋅z = x⋅z + y⋅z. — Distributive to the right.
  end formal system.

lemma nr1. x⋅0 = 0.
proof
  1. x⋅(0 + 0) = x⋅0 + x⋅0.
  2. x⋅(0 + 0) = x⋅0 by unit, AG.equality.
  3. x⋅0 + x⋅0 = x⋅0 by 1, 2.
  conclusion by AG.cancellation.
∎

lemma nr1. 0⋅x = 0.
proof
  1. (0 + 0)⋅x = 0⋅x + 0⋅x.
  2. (0 + 0)⋅x = 0⋅x by unit, AG.equality.
  3. 0⋅x + 0⋅x = 0⋅x by 1, 2.
  conclusion by AG.cancellation.
∎


end theory NR.

theory UR. — Unitary ring.

  include theory NR.
  
  formal system.
    axiom unit. ∃ x ∀ y: x⋅y = y ∧ y⋅x = x.
  end formal system.

  constant 1.

definition ur1. P(x) ≔ x⋅y = y ∧ y⋅x = y.

lemma ur2. ∀ u, v: P(u) ∧ P(v) ⇒ u = v.
proof
  a. P(u) ∧ P(v) ⊢ u = v.
  proof
    1. u⋅v = u by ur1, premise.
    2. u⋅v = v by ur1, premise.
    conclusion by 1, 2, equality.
  ∎

  conclusion by a, DT.
∎

defining axiom unit. 1⋅y = y ∧ y⋅1 = y.
proof
  1. ∃! P(x) by ur1, ur2, unit.
  conclusion by defining axiom theorem.
∎

end theory UR.

theory SF. — Skew-field.

  include theory NR.

  formal system.
    axiom SF1. ∃ x ≠ 0.
    axiom SF2. ∀ a ≠ 0, b ∃ x a⋅x = b.
    axiom SF3. ∀ a ≠ 0, b ∃ y y⋅a = b.
  end formal system.

definition sf1. P(u) ≔ u⋅x = x.

lemma sf2. ∃ u: P(u).
proof
  1. ∃ a ≠ 0 by SF1.

  a. a ≠ 0 ⊢ P(u).
  proof
    a1. ∃ u u⋅a = a by SF3.

    b. u⋅a = a ⊢ P(u).
    proof
      b1. ∃ y a⋅y = x by SF2.

      c. a⋅y = x ⊢ P(u).
      proof
        c1. u⋅x = u⋅(a⋅y) = (u⋅a)⋅y = a⋅y = x
          by NR.A, b.premise, premise, equality.
        conclusion by c1, sf1.
      ∎

      conclusion by existence introduction, c.
    ∎

    conclusion by existence introduction, b.
  ∎

  conclusion by existence introduction, a.
∎


— Theorem: SF is an extension of UR.

end theory SF.

theory F. — Field.

  include theory SF.

  formal system.
    object x, y.

    axiom F1. x⋅y = y⋅x.
  
  end formal system.

end theory SF.
—]
