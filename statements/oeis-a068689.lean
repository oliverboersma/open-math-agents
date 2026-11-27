import Mathlib

/-!
# A068689: Primes which are a sandwich of numbers made of only one decimal digit between two 9's.

Source: https://oeis.org/A068689
Credit: @divmxnd0x

The numbers in question are `9 d d ... d 9` with `k ≥ 1` copies of one decimal digit `d` between
two 9's.

Conjecture (stated in A068689): inner digits 1, 2 and 8 are the only repeating digits for which the
resulting numbers can be prime; i.e. `9444...4449`, `9555...5559`, `9777...7779` are composite
(inner digits 0, 3, 6, 9 always give composite numbers).

Formalization notes:
* `sandwich d k = 9 * 10^(k+1) + 10 * (d * ((10^k - 1) / 9)) + 9` is `9`, then `k` copies of `d`,
  then `9`; here `(10^k - 1) / 9` is the repunit with `k` ones (exact division).
* The statement: if `sandwich d k` is prime for a digit `d` and `k ≥ 1`, then `d ∈ {1, 2, 8}`.
* For `k ≤ 6` the primes among these numbers are 919, 929, 9222229, 9888889 (data of A068689),
  and none has inner digit 4, 5 or 7.
-/

namespace OMA.S_oeis_a068689

/-- `9`, followed by `k` copies of the digit `d`, followed by `9`. -/
def sandwich (d k : ℕ) : ℕ :=
  9 * 10 ^ (k + 1) + 10 * (d * ((10 ^ k - 1) / 9)) + 9

/-- The conjecture of A068689: such a number can only be prime when the inner digit is 1, 2 or 8. -/
theorem main : ∀ d k : ℕ, d < 10 → 1 ≤ k → (sandwich d k).Prime → d = 1 ∨ d = 2 ∨ d = 8 := by
  sorry

end OMA.S_oeis_a068689
