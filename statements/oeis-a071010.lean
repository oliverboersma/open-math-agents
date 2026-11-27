import Mathlib

/-!
# A071010: Sigma(k)/4 when k is not a sum of 2 squares

Source: https://oeis.org/A071010
Credit: @xor2k

Formalizes the OEIS A071010 conjecture: if n is not the sum of 2 squares, then
sigma(n) == 0 (mod 4).

Conventions: `n` ranges over the natural numbers; a sum of 2 squares means `n = x^2 + y^2`
with natural numbers `x, y` (zero allowed, as in A001481, so `0`, squares and doubled squares
count as sums of two squares; signs are irrelevant since only `x^2` and `y^2` enter). `n = 0`
is a sum of two squares, so only `n ≥ 1` is constrained. `sigma(n)` is the sum of divisors,
`ArithmeticFunction.sigma 1 n`. The congruence `sigma(n) == 0 (mod 4)` is written `4 ∣ sigma(n)`.
-/

namespace OMA.S_oeis_a071010

/-- If `n` is not a sum of two squares, then `4` divides the sum of divisors `σ(n)`. -/
theorem main :
    ∀ n : ℕ, (¬ ∃ x y : ℕ, n = x ^ 2 + y ^ 2) → 4 ∣ ArithmeticFunction.sigma 1 n := by
  sorry

end OMA.S_oeis_a071010
