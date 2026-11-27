import Mathlib

/-!
# A007091: Numbers in base 5.

Source: https://oeis.org/A007091
Credit: @marcelopierry

Rémy Sigrist (Nov 22 2009), in the comments of A007091:
  It appears that this sequence corresponds to the numbers n for which twice the sum of
  digits of n is the sum of digits of 2*n.
Sela Fried (Nov 03 2025) notes that the conjecture is true (see the Fried link in A007091).

A007091 (offset 0): a(m) is m written in base 5, read as a decimal number. The digit sums are
decimal digit sums. Membership in the sequence is stated as being in the range of a.
-/

namespace OMA.S_oeis_a007091

/-- A007091(m): the base-5 digits of m, read as a decimal number. -/
def a (m : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 5 m)

/-- Sigrist's conjecture: n is a term iff twice the digit sum of n is the digit sum of 2n. -/
theorem main : ∀ n : ℕ,
    (∃ m : ℕ, a m = n) ↔ 2 * (Nat.digits 10 n).sum = (Nat.digits 10 (2 * n)).sum := by
  sorry

end OMA.S_oeis_a007091
