import Mathlib

/-!
# The parity conjecture for OEIS A000139

Source: https://oeis.org/A000139
Credit: @Heart-galaxy

OEIS A000139 defines `a(n) = 2 * (3*n)! / ((2*n+1)! * (n+1)!)` with offset 0,1, so
`n` ranges over all natural numbers. Its conjecture says that `a(n)` is odd exactly when `n`
belongs to A022341. OEIS A022341 is the set of odd fibbinary numbers: positive odd natural
numbers whose binary expansion has no adjacent 1-bits. We state membership by this explicit
bit condition.
-/

namespace OMA.S_oeis_a000139

/-- The factorial quotient defining the terms of A000139, with natural-number division. -/
def a (n : ℕ) : ℕ :=
  2 * (3 * n).factorial / ((2 * n + 1).factorial * (n + 1).factorial)

/-- Membership in A022341: odd fibbinary numbers (no adjacent set bits). -/
def IsA022341 (n : ℕ) : Prop :=
  n % 2 = 1 ∧ ∀ i : ℕ, ¬ (n.testBit i ∧ n.testBit (i + 1))

/-- A000139 is odd precisely at indices belonging to A022341. -/
theorem main : ∀ n : ℕ, Odd (a n) ↔ IsA022341 n := by
  sorry

end OMA.S_oeis_a000139
