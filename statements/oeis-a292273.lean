import Mathlib

/-!
# A292273: For odd n: a(n) = 0, and for even n: a(n) = -mu(n)

Source: https://oeis.org/A292273
Credit: @xor2k

Formalizes the OEIS A292273 conjecture (Mats Granvik, Jul 06 2024), stated as
Conjecture: a(n) = Re(A008683(n)*(i^n)).

Conventions:
* offset 1, so the statement is for all `n ≥ 1`;
* `A008683` is the Moebius function, `ArithmeticFunction.moebius` (integer valued);
* `i` is the imaginary unit `Complex.I`, `Re` is `Complex.re`;
* `a n` is integer valued and is compared with the real part after casting to `ℝ`.
-/

namespace OMA.S_oeis_a292273

/-- `a(n) = 0` for odd `n` and `a(n) = -mu(n)` for even `n`. -/
def a (n : ℕ) : ℤ :=
  if Odd n then 0 else -ArithmeticFunction.moebius n

/-- For every `n ≥ 1`, `a(n) = Re(mu(n) * i^n)`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = (((ArithmeticFunction.moebius n : ℤ) : ℂ) * Complex.I ^ n).re := by
  sorry

end OMA.S_oeis_a292273
