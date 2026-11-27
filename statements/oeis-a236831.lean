import Mathlib

/-!
# A236831: Ordered ways to write n = p + q with q > 0 such that p, p + 2 and p + prime(q) + 1 are all prime

Source: https://oeis.org/A236831
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A236831): a(n) > 0 for all n > 13.

Conventions:
* prime(q) is the q-th prime with prime(1) = 2 (`Nat.nth Nat.Prime (q - 1)`).
* a(n) > 0 means that n = p + q for some q > 0 such that p, p + 2 and p + prime(q) + 1 are all
  prime.
-/

namespace OMA.S_oeis_a236831

/-- The `q`-th prime, `prime 1 = 2`. -/
noncomputable def prime (q : ℕ) : ℕ := Nat.nth Nat.Prime (q - 1)

/-- Sun's conjecture on A236831: every `n > 13` is `p + q` with `q > 0` such that `p`, `p + 2`
and `p + prime(q) + 1` are all prime. -/
theorem main : ∀ n : ℕ, 13 < n → ∃ p q : ℕ, 0 < q ∧ p + q = n ∧
    p.Prime ∧ (p + 2).Prime ∧ (p + prime q + 1).Prime := by
  sorry

end OMA.S_oeis_a236831
