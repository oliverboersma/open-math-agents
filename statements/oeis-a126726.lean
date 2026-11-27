import Mathlib.Data.Nat.Sqrt

/-!
# OEIS A126726

R. J. Mathar's conjecture of May 21, 2025 relates the number of squares
with exactly n binary digits to the count between consecutive powers of two.
A126726 starts at index zero and uses one digit to write zero. A190568
starts at index -1. Its defining formula below gives its values at the
positive indices used in the conjecture.

Sources: https://oeis.org/A126726 and https://oeis.org/A190568
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a126726

/-- Number of binary digits in x, with one digit for zero. -/
def binaryDigits (x : Nat) : Nat := x.log2 + 1

/-- A126726 counts nonnegative roots whose square has n digits. Such a
square is less than 2^n, and its root is at most the square. -/
def squareCount (n : Nat) : Nat :=
  ((List.range (2 ^ n)).filter (fun k => binaryDigits (k * k) == n)).length

/-- A190568 at a nonnegative index, using its defining difference
of integer square roots. -/
def betweenPowers (n : Nat) : Nat :=
  Nat.sqrt (2 ^ (n + 1)) - Nat.sqrt (2 ^ n)

theorem main :
    ∀ n : Nat, 0 < n →
      (squareCount n : Int) = (betweenPowers n : Int) - (-1 : Int) ^ n := by
  sorry

end OMA.S_oeis_a126726
