import Mathlib

/-!
# A275675: Number of ordered ways to write n as 4^k*(1+x^2+y^2)+5*z^2, where k,x,y,z are nonnegative integers with x <= y.

Source: https://oeis.org/A275675
Credit: @sntntHb

Conjecture (Zhi-Wei Sun, stated on the OEIS page): `a(n) > 0` for all `n > 0`, i.e. every positive
integer `n` can be written as `4^k * (1 + x^2 + y^2) + 5 * z^2` with `k, x, y, z` nonnegative
integers and `x ≤ y`.
-/

namespace OMA.S_oeis_a275675

theorem main : ∀ n : ℕ, 0 < n →
    ∃ k x y z : ℕ, x ≤ y ∧ n = 4 ^ k * (1 + x ^ 2 + y ^ 2) + 5 * z ^ 2 := by
  sorry

end OMA.S_oeis_a275675
