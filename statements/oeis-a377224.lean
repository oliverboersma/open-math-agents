import Mathlib

/-!
# A377224: Ways to write n as x*(5*x+1) + y*(5*y+1)/2 + z*(5*z+1)/2

Source: https://oeis.org/A377224
Credit: @niclorusso

A377224(n) is the number of ways to write n as x*(5*x+1) + y*(5*y+1)/2 + z*(5*z+1)/2, where x, y, z
are integers with y*(5*y+1) <= z*(5*z+1).

Conjecture 1 (in the comments of A377224): a(n) = 0 only for n = 1.

(Conjecture 1 goes on with "Also, a(n) = 1 only for n = 0, 2, 3, 5, 7, 14, 16, 19, 37, 43, 58, 61,
79", and the entry has a Conjecture 2; only the first statement, a(n) = 0 only for n = 1, is
formalized here.)

Conventions:
* The sequence has offset 0; n ranges over the natural numbers.
* x, y, z range over the integers. y*(5*y+1) and z*(5*z+1) are always even, so the divisions by 2
  are exact (integer division `/` on ℤ).
* a(n) = 0 means that n has no such representation. The ordering condition
  y*(5*y+1) <= z*(5*z+1) only avoids counting a representation twice, so it does not affect whether
  a representation exists and is dropped here.
* "a(n) = 0 only for n = 1" is stated as: n has a representation if and only if n /= 1.
-/

namespace OMA.S_oeis_a377224

/-- `n = x(5x+1) + y(5y+1)/2 + z(5z+1)/2` for some integers `x, y, z`. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ x y z : ℤ, x * (5 * x + 1) + y * (5 * y + 1) / 2 + z * (5 * z + 1) / 2 = n

/-- Conjecture 1 on A377224 (first part): every natural number except `1` is of the form
`x(5x+1) + y(5y+1)/2 + z(5z+1)/2` with integers `x, y, z`. -/
theorem main : ∀ n : ℕ, IsRepresentable n ↔ n ≠ 1 := by
  sorry

end OMA.S_oeis_a377224
