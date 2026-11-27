import Mathlib

/-!
# Intersection of binary digit-addition orbits (OEIS A096303)

Source: https://oeis.org/A096303 (Jason Earls). The reference orbit
https://oeis.org/A010062 starts at 1 and uses the same iteration.
Credit: @MMexicann
-/

namespace OMA.S_oeis_a096303

/-- In base two, the digit sum counts the ones. -/
def step (n : ℕ) : ℕ := n + (Nat.digits 2 n).sum

theorem main : ∀ n : ℕ, 0 < n →
    ∃ i j : ℕ, (step^[i]) n = (step^[j]) 1 := by
  sorry

end OMA.S_oeis_a096303
