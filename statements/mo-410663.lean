import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Set.Card

/-!
# Perfect matchings in graphs excluding a copy of K₃,₃

Source: https://mathoverflow.net/questions/410663
Credit: @jpollard-cs

The question asks for a uniform upper bound on the number of perfect matchings.
The discussion identifies the scale (constant times n^(2/3))^n, where 2*n is the
vertex count. The question itself specifies no constant. Cubing the inequality
allows this formulation to use only natural numbers. Containment permits edges
inside either part of the forbidden copy.
-/

namespace OMA.S_mo_410663

theorem main : ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin (2 * n))),
    ¬ SimpleGraph.IsContained (completeBipartiteGraph (Fin 3) (Fin 3)) G →
    (Set.ncard {M : G.Subgraph | M.IsPerfectMatching}) ^ 3 ≤ (C * n ^ 2) ^ n := by
  sorry

end OMA.S_mo_410663
