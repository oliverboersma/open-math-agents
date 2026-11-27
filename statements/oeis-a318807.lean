import Mathlib

/-!
# Integer ratios when both divisor sums are perfect squares

Source: https://oeis.org/A318807
Credit: @anmolspace

Michel Lagneau's OEIS entry collects numbers whose squarefree and nonsquarefree
divisor sums are both perfect squares. In the subsequence `c` in the entry's
comment, both sums are positive and their ratio is integral. Lagneau conjectured
in 2018 that every such ratio is a prime square (OEIS A001248).
-/

namespace OMA.S_oeis_a318807

/-- Sum of the squarefree divisors (OEIS A048250). -/
def squarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with Squarefree d, d

/-- Sum of the nonsquarefree divisors (OEIS A162296). -/
def nonsquarefreeSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors with ¬ Squarefree d, d

/-- For positive `n`, the squarefree sum includes 1. Thus `r > 0` and the
explicit product equality express positive integral membership in `c`. -/
theorem main : ∀ n r : ℕ, 0 < n → IsSquare (squarefreeSum n) →
    IsSquare (nonsquarefreeSum n) → 0 < r → nonsquarefreeSum n = squarefreeSum n * r →
    ∃ p : ℕ, p.Prime ∧ r = p ^ 2 := by
  sorry

end OMA.S_oeis_a318807
