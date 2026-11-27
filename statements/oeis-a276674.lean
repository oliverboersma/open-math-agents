import Mathlib

/-!
# A276674: Numbers n such that x - lambda(x) = n has no solution, where lambda(x) = A002322(x)

Source: https://oeis.org/A276674
Credit: @niclorusso

Conjecture (in the comments of A276674): if x - lambda(x) = 2*m > 0, then x <= 4*m.

Conventions:
* lambda is the Carmichael function A002322 (the exponent of the unit group of ZMod x), Mathlib's
  `ArithmeticFunction.carmichael`.
* x and m range over the positive integers. lambda(x) <= x, so x - lambda(x) is an exact
  natural-number subtraction.
-/

namespace OMA.S_oeis_a276674

open ArithmeticFunction

/-- The conjecture on A276674: whenever `x - lambda(x) = 2m > 0`, we have `x <= 4m`. -/
theorem main : ∀ x m : ℕ, 1 ≤ x → 0 < m → x - carmichael x = 2 * m → x ≤ 4 * m := by
  sorry

end OMA.S_oeis_a276674
