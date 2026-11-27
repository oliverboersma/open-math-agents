import Mathlib

/-!
# A270928: Ways to write n = x*(x-1)/2 + y*(y-1)/2 + z*(z-1)/2 with 0 < x <= y <= z, one of x, y, z prime

Source: https://oeis.org/A270928
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A270928; Conjecture 1.2(i) of his JNT paper):
(i) a(n) > 0 for n > 0 with the only exception n = 15^2 = 225.

(The comment continues "Also, a(n) = 1 only for n = 1, 2, 4, ..., 4068"; only the first statement,
a(n) > 0 for n > 0 except n = 225, is formalized here.)

Conventions:
* a(n) > 0 means that n = x(x-1)/2 + y(y-1)/2 + z(z-1)/2 for some integers 0 < x <= y <= z with at
  least one of x, y, z prime. x(x-1)/2 is an exact division.
* The conjecture is stated as: for n >= 1, such a representation exists if and only if n /= 225.
-/

namespace OMA.S_oeis_a270928

/-- `n` has a representation counted by A270928. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ x ≤ y ∧ y ≤ z ∧ (x.Prime ∨ y.Prime ∨ z.Prime) ∧
    x * (x - 1) / 2 + y * (y - 1) / 2 + z * (z - 1) / 2 = n

/-- Sun's conjecture (i) on A270928: every `n >= 1` except `225` has such a representation. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (IsRepresentable n ↔ n ≠ 225) := by
  sorry

end OMA.S_oeis_a270928
