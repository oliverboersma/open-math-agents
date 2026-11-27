import Mathlib

/-!
# A059917: a(n) = (3^(2^n) + 1)/2 = A059919(n)/2, n >= 0.

Source: https://oeis.org/A059917
Credit: @divmxnd0x

`a(0), a(1), a(2), a(4), a(5)` and `a(6)` are prime.

Conjecture (Thomas Ordowski, Dec 26 2012): `a(n)` is composite for all `n > 6`.

Formalization notes:
* `3^(2^n) + 1` is even, so `(3 ^ 2 ^ n + 1) / 2` in `ℕ` is exact; `a 0, ..., a 3` are 2, 5, 41,
  3281, matching the data of A059917.
* For `n > 6`, `a(n) > 1`, so "composite" is the same as "not prime".
-/

namespace OMA.S_oeis_a059917

/-- A059917: `(3^(2^n) + 1) / 2`. -/
def a (n : ℕ) : ℕ :=
  (3 ^ 2 ^ n + 1) / 2

/-- Ordowski's conjecture: `a(n)` is composite for every `n > 6`. -/
theorem main : ∀ n : ℕ, 6 < n → ¬ (a n).Prime := by
  sorry

end OMA.S_oeis_a059917
