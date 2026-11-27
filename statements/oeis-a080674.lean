import Mathlib

/-!
# A080674: a(n) = (4/3)*(4^n - 1).

Source: https://oeis.org/A080674 (OEIS Foundation, CC BY-SA 4.0)
Credit: @OrangeHeadz

The OEIS entry has offset 0 and begins 0, 4, 20, 84, 340, ... It carries the comment of
Alexandre Wajnberg (Apr 25 2005): the sequence is conjectured to be the number of integers from
0 to (10^n)-1 that lack 0, 1, 2, 3, 4 and 5 as a digit.

Conventions.
* The integer 0 is written with the single digit 0, so it has the digit 0 and is not counted;
  this agrees with a(0) = 0. Since `Nat.digits 10 0` is the empty list, the condition `m ≠ 0` is
  stated separately.
* For `m ≠ 0`, `Nat.digits 10 m` is the list of decimal digits of `m`, without leading zeros.
* `4 * (4 ^ n - 1) / 3` is an exact division, because 3 divides `4 ^ n - 1`.
-/

namespace OMA.S_oeis_a080674

/-- For every `n`, the number of integers from `0` to `10 ^ n - 1` none of whose decimal digits
is 0, 1, 2, 3, 4 or 5 equals `(4/3) * (4 ^ n - 1)`. -/
theorem main : ∀ n : ℕ,
    ((Finset.range (10 ^ n)).filter fun m : ℕ =>
      m ≠ 0 ∧ ∀ d ∈ Nat.digits 10 m, d ∉ ({0, 1, 2, 3, 4, 5} : Finset ℕ)).card =
      4 * (4 ^ n - 1) / 3 := by
  sorry

end OMA.S_oeis_a080674
