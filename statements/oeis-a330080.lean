import Mathlib

/-!
# Bounds on the floors of a rational recurrence

Source: https://oeis.org/A330080 (Andres Cicuttin).
Credit: @physbuzz
-/

namespace OMA.S_oeis_a330080

/-- Term with zero-based index n, corresponding to b(n + 1) in A330080. -/
def term : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => (term (n + 2) + term (n + 1)) / term n

/-- Every term of the floor sequence is between zero and five, inclusive. -/
theorem main : ∀ n : ℕ, 0 ≤ ⌊term n⌋ ∧ ⌊term n⌋ ≤ 5 := by
  sorry

end OMA.S_oeis_a330080
