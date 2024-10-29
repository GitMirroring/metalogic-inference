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


theory λ. — Church's λ-K-conversion. Cf. Church, p. 12.

  formal system.
  
—    binder λ.
  
  axiom Lambda1. object x, y  object M.
    x not free in M —, y does not occur in M
      ⊩ M[x⤅y] = M.

  axiom Lambda2. object x  object M, N.
    x not in bound(M), free(N) intersection bound(M) ≡ ~empty — Change to: ... = empty
      ⊢ ((λ x M) N) = M[x⤅N].

  — Cf. Schmidt, pp.57-58.
  axiom beta.
    object °x  object M, N.
    N free for x in M ⊢ ((λ x M) N) = M[x⤇N]. — (x ⤇ M)(N) = M[x⤇N]
 — bound M intersection free N = empty ⊢ ((λ x M) N) = M[x⤅N].

  axiom alpha.
    object °x, y  object E.
    y not free in E, y free for x in E
      ⊢ (λ x E) = (λ y E[x⤇y]). — x ⤇ E = y ⤇ E[x⤇y]
 
  axiom eta.
    object °x  object E.
    x not free in E ⊢ (λ x (E x)) = E. — x ⤇ E(x) = E
    
  end formal system.

end theory λ.


