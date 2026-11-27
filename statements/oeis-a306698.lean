import Mathlib.Data.Finset.Insert
import Mathlib.Data.Set.Image

/-!
# OEIS A306698: range conjecture

Sources: https://oeis.org/A306698 and https://oeis.org/A032766
Credit: @hangumm

The state stores the current value and all values seen so far. At step n+1,
subtract 2*(n+1) precisely when the result is positive and has not occurred;
otherwise add n+1. The initial value is zero.

The conjecture says that the range is exactly the nonnegative integers
congruent to zero or one modulo three. This is a statement, not a proof.
-/

namespace OMA.S_oeis_a306698

def state : ℕ → ℕ × Finset ℕ
  | 0 => (0, {0})
  | n + 1 =>
    let s := state n
    let next := if 2 * (n + 1) < s.1 ∧ s.1 - 2 * (n + 1) ∉ s.2
      then s.1 - 2 * (n + 1) else s.1 + (n + 1)
    (next, insert next s.2)

def sequence (n : ℕ) : ℕ := (state n).1

theorem main : Set.range sequence = {m : ℕ | m % 3 = 0 ∨ m % 3 = 1} := by
  sorry

end OMA.S_oeis_a306698

