import Mathlib

/-!
# Intersection of largest-decimal-digit addition orbits (OEIS A096306)

Source: https://oeis.org/A096306 (Jason Earls). The reference sequence
https://oeis.org/A045844 starts at 1.
Credit: @MMexicann
-/

namespace OMA.S_oeis_a096306

/-- Add the largest decimal digit of the current number. -/
def step (n : ℕ) : ℕ := n + (Nat.digits 10 n).foldl max 0

theorem main : ∀ n : ℕ, 0 < n →
    ∃ i j : ℕ, (step^[i]) n = (step^[j]) 1 := by
  sorry

end OMA.S_oeis_a096306
