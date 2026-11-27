import Mathlib

/-!
# A028870: Numbers k such that k^2 - 2 is prime.

Source: https://oeis.org/A028870
Credit: @ShoQo

Conjecture (OEIS comment): It is conjectured that this sequence is infinite.

Formalization notes:
* `k` ranges over natural numbers. The data starts at 2 (2^2 - 2 = 2), and `k = 0, 1` give no
  prime in either `ℕ` or `ℤ`, so truncated subtraction in `ℕ` does not change the set.
-/

namespace OMA.S_oeis_a028870

theorem main : {k : ℕ | (k ^ 2 - 2).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a028870
