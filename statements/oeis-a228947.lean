import Mathlib

/-!
# OEIS A228947: a(n) = sigma(n) - phi(n) - n

Source: https://oeis.org/A228947 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence is `a(n) = sigma(n) - phi(n) - n` with offset 1, where `sigma` is the sum of
divisors and `phi` is Euler's totient function (the values can be negative, e.g. `a(1) = -1`).
The entry records the formula line:

  a(n) = 0  <=>  n = 2 (conjectured).

We formalize this conjecture: for every `n ≥ 1`, the integer `sigma(n) - phi(n) - n` vanishes
if and only if `n = 2`.
-/

namespace OMA.S_oeis_a228947

/-- `a(n) = sigma(n) - phi(n) - n`, computed in the integers. -/
def a (n : ℕ) : ℤ := (ArithmeticFunction.sigma 1 n : ℤ) - (Nat.totient n : ℤ) - (n : ℤ)

/-- For `n ≥ 1`, `a(n) = 0` exactly when `n = 2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n = 2) := by
  sorry

end OMA.S_oeis_a228947
