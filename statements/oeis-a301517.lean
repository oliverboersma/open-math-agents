import Mathlib

/-!
# Square ratios of nonsquarefree and squarefree divisor sums

Source: https://oeis.org/A301517
Credit: @anmolspace

Michel Lagneau conjectured in 2018 that whenever the ratio of the sum of the
nonsquarefree divisors to the sum of the squarefree divisors is a positive
integer square, it is the square of a prime (OEIS A001248).
-/

namespace OMA.S_oeis_a301517

/-- The sum of all squarefree divisors of `n` (OEIS A048250). -/
def squarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with Squarefree d, d

/-- The sum of all nonsquarefree divisors of `n` (OEIS A162296). -/
def nonsquarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with ¬ Squarefree d, d

/-- Since 1 is a squarefree divisor of every positive `n`, cross-multiplying
expresses the exact ratio. Requiring `k > 0` restricts it to OEIS A301517. -/
theorem main : ∀ n k : ℕ, 0 < n → 0 < k →
    nonsquarefreeSum n = squarefreeSum n * k ^ 2 → k.Prime := by
  sorry

end OMA.S_oeis_a301517
