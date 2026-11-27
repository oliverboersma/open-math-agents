import Mathlib

/-!
# A085265: Numbers that can be written as sum of a positive squarefree number and a positive square

Source: https://oeis.org/A085265
Credit: @niclorusso

Conjecture (in the comments of A085265): a(n) = n + 2 for n > 11. That is, only 1 and 13 are
missing.

Conventions:
* The terms are the positive integers n = s + k^2 with s >= 1 squarefree (Mathlib's `Squarefree`)
  and k >= 1.
* "only 1 and 13 are missing" is stated as: a positive integer n is a term if and only if
  n /= 1 and n /= 13. (This is the content of a(n) = n + 2 for n > 11, given the listed initial
  terms 2, 3, ..., 12, 14.)
-/

namespace OMA.S_oeis_a085265

/-- `n` is the sum of a positive squarefree number and a positive square. -/
def IsTerm (n : ℕ) : Prop :=
  ∃ s k : ℕ, 1 ≤ s ∧ Squarefree s ∧ 1 ≤ k ∧ s + k ^ 2 = n

/-- The conjecture on A085265: the only positive integers that are not the sum of a positive
squarefree number and a positive square are `1` and `13`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (IsTerm n ↔ (n ≠ 1 ∧ n ≠ 13)) := by
  sorry

end OMA.S_oeis_a085265
