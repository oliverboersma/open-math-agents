import Mathlib

/-!
# A047872: floor(abs(B(2*n+2)/B(2*n))).

Source: https://oeis.org/A047872
Credit: @rot13maxi

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a047872

/-- A047872: `a(n) = floor(abs(B(2*n+2) / B(2*n)))`, where `B(n)` is the `n`-th
Bernoulli number. -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊|(bernoulli (2 * n + 2) : ℚ) / (bernoulli (2 * n) : ℚ)|⌋

/-- Bill McEachen's conjecture on A047872:
`a(n) = floor((n+1)*(2*n+1) / (2*Pi^2))`. -/
theorem main : ∀ n : ℕ,
    a n = ⌊(((n + 1) * (2 * n + 1) : ℝ) / (2 * Real.pi ^ 2))⌋ := by
  sorry

end OMA.S_oeis_a047872
