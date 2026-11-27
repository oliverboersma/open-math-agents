import Mathlib

/-!
# A046057: Smallest order m > 0 for which there are n nonisomorphic finite groups of order m, or 0
if no such order exists.

Source: https://oeis.org/A046057
Credit: @mbilenko03

Conjecture (R. Keith Dennis): there are no 0's in this sequence, that is, for every `n ≥ 1`
(the offset of the sequence is 1) there is an order `m > 0` such that there are exactly `n`
groups of order `m` up to isomorphism.

Conventions:
- The number of groups of order `m` up to isomorphism is counted as in A000001: the number of
  isomorphism classes of group structures on `Fin m`. Every group of order `m` is isomorphic to
  one carried by `Fin m`. Isomorphism is an equivalence relation, so `Quot` by it is the set of
  isomorphism classes, and `Group (Fin m)` is a finite type, so `Nat.card` is the actual number.
-/

namespace OMA.S_oeis_a046057

/-- Two group structures on `Fin m` are isomorphic. -/
def IsoRel (m : ℕ) (G H : Group (Fin m)) : Prop :=
  Nonempty (@MulEquiv (Fin m) (Fin m) (letI := G; inferInstance) (letI := H; inferInstance))

/-- The number of groups of order `m` up to isomorphism (OEIS A000001). -/
noncomputable def gnu (m : ℕ) : ℕ := Nat.card (Quot (IsoRel m))

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ gnu m = n := by
  sorry

end OMA.S_oeis_a046057
