import Mathlib

/-!
# A254690: Number of decompositions of 2n into a sum of two primes p1 < p2 such that p2-p1 is between a pair of sexy primes.

Source: https://oeis.org/A254690
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: when n>=7, a(n)>0.

Conventions: a pair of sexy primes is `(r, r + 6)` with both prime; `p2 - p1` lies between them
means `r < p2 - p1 < r + 6` (OEIS: p_a < p2 - p1 < p_a + 6). `a(n) > 0` means such a
decomposition `2n = p1 + p2` exists.
-/

namespace OMA.S_oeis_a254690

/-- For every `n ≥ 7`, `2n = p1 + p2` with primes `p1 < p2` and `r < p2 - p1 < r + 6` for some
pair of sexy primes `r, r + 6`. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ∃ p₁ p₂ r : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₁ < p₂ ∧ p₁ + p₂ = 2 * n ∧
      r.Prime ∧ (r + 6).Prime ∧ r < p₂ - p₁ ∧ p₂ - p₁ < r + 6 := by
  sorry

end OMA.S_oeis_a254690
