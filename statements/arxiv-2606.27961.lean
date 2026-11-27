import Mathlib

/-!
# The square-plane transversal difference conjecture

Barcau, Paşol and Ţurcaş, *Transversal Difference Numbers in Finite Abelian
Quotients*, Conjecture 6.2. Source: https://arxiv.org/abs/2606.27961
Credit: @rleshner
-/

namespace OMA.S_arxiv_2606_27961

open scoped Pointwise

abbrev Plane (m : ℕ) := ZMod m × ZMod m

/-- Coordinatewise reduction from the square-modulus plane to the residue plane. -/
def reduce (p : ℕ) (x : Plane (p ^ 2)) : Plane p :=
  ((x.1.val : ZMod p), (x.2.val : ZMod p))

/-- The minimum ranges over sets containing exactly one lift of each residue pair. -/
theorem main : ∀ p : ℕ, p.Prime → Odd p →
    IsLeast {n : ℕ | ∃ T : Set (Plane (p ^ 2)),
      Set.BijOn (reduce p) T Set.univ ∧ (T - T).ncard = n} ((2 * p - 1) ^ 2) := by
  sorry

end OMA.S_arxiv_2606_27961
