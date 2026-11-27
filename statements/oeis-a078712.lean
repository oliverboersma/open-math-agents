import Mathlib

/-!
# A078712: Series expansion of (-3 - 2*x)/(1 + x - x^3) in powers of x.

Source: https://oeis.org/A078712
Credit: @divmxnd0x

Conjecture (Michael Somos, Dec 25 2022): similar to the Perrin sequence A001608, if `p` is a prime
then `a(p) ≡ 1 (mod p)`.

Formalization notes:
* Multiplying the series by `1 + x - x^3` shows `a(0) = -3`, `a(1) = 1`, `a(2) = -1` and
  `a(n + 3) = -a(n + 2) + a(n)`; this recursion defines `a` below.
* With it `a 0, ..., a 11` are -3, 1, -1, -2, 3, -4, 2, 1, -5, 7, -6, 1, matching the data of
  A078712.
-/

namespace OMA.S_oeis_a078712

/-- A078712: coefficients of `(-3 - 2x) / (1 + x - x^3)`. -/
def a : ℕ → ℤ
  | 0 => -3
  | 1 => 1
  | 2 => -1
  | n + 3 => -a (n + 2) + a n

/-- Somos' conjecture: `a(p) ≡ 1 (mod p)` for every prime `p`. -/
theorem main : ∀ p : ℕ, p.Prime → a p ≡ 1 [ZMOD p] := by
  sorry

end OMA.S_oeis_a078712
