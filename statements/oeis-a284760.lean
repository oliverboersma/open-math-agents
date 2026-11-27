import Mathlib

/-!
# A284760: a(n) = Sum_{i=1..n-1}(i^(n-2)) mod n^4.

Source: https://oeis.org/A284760
Credit: @LAPRAI

Formalizes the OEIS comment: Mestrovic conjectures that a(n) > 0 for all n > 1 (Conjecture 2.11).

Conventions: the sum runs over `i = 1, ..., n-1`, i.e. `Finset.Ico 1 n`; `a(n) > 0` means the remainder modulo `n^4` is nonzero.
-/

namespace OMA.S_oeis_a284760

/-- For every `n > 1`, `n^4` does not divide `Sum_{i=1..n-1} i^(n-2)`. -/
theorem main : ∀ n : ℕ, 1 < n → (∑ i ∈ Finset.Ico 1 n, i ^ (n - 2)) % n ^ 4 ≠ 0 := by
  sorry

end OMA.S_oeis_a284760
