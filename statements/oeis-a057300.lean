import Mathlib

/-!
# A057300 and Ralf Stephan's even and odd recurrences

The sequence swaps each neighboring pair of binary digits, counting positions
from the units digit. Equivalently, it swaps 1 and 2 in base 4 and leaves 0
and 3 fixed. Ralf Stephan conjectured the two recurrences on October 11, 2003.
Both equalities below move the negative term to the left, so that all
arithmetic takes place in the natural numbers.

Source: https://oeis.org/A057300
Credit: @ecirak42
-/

namespace OMA.S_oeis_a057300

/-- Reverse the two binary bits comprising one base-4 digit. -/
def swapDigit (d : ℕ) : ℕ := 2 * (d % 2) + d / 2

/-- Apply the digit swap to the base-4 expansion, starting at the units digit. -/
def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else 4 * a (n / 4) + swapDigit (n % 4)
termination_by n
decreasing_by omega

theorem main : ∀ n : ℕ,
    a (2 * n) + 2 * a n = 5 * n ∧
    a (2 * n + 1) + 2 * a n = 5 * n + 2 := by
  sorry

end OMA.S_oeis_a057300
