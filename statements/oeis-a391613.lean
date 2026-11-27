import Mathlib

/-!
# A391613: Number of ways to write n as x^2 + y + z with x >= 1 and y >= z >= 1 such that lcm(x^2,y,z) is a square.

Source: https://oeis.org/A391613
Credit: @divmxnd0x

Conjecture (stated in A391613): `a(n) > 0` for all `n > 5`, i.e. every `n > 5` can be written as
`x^2 + y + z` with `x ≥ 1`, `y ≥ z ≥ 1` such that `lcm(x^2, y, z)` is a square.

Formalization notes:
* `lcm(x^2, y, z)` is `Nat.lcm (x ^ 2) (Nat.lcm y z)`.
* With this definition `a(1), ..., a(25)` = 0, 0, 1, 0, 0, 2, 2, 1, 2, 1, 2, 1, 2, 3, 3, 2, 2, 2, 6,
  1, 4, 6, 3, 4, 5, matching the data of A391613.
-/

namespace OMA.S_oeis_a391613

/-- The conjecture of A391613. -/
theorem main : ∀ n : ℕ, 5 < n → ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧ n = x ^ 2 + y + z ∧
    IsSquare (Nat.lcm (x ^ 2) (Nat.lcm y z)) := by
  sorry

end OMA.S_oeis_a391613
