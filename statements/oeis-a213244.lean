import Mathlib

/-!
# A213244: Number of nonzero elements in GF(2^n) that are 5th powers

Source: https://oeis.org/A213244
Credit: @ivillar

Joerg Arndt (Jun 07 2012): a(n) (offset 1) is the number of nonzero elements x of the finite field
GF(2^n) (Mathlib's `GaloisField 2 n`) that are 5th powers, i.e. x = y^5 for some y in GF(2^n).

Conjectures from Colin Barker, Aug 23 2014:
  a(n) = 17*a(n-4) - 16*a(n-8),
  G.f.: x*(8*x^6+12*x^5+14*x^4+3*x^3+7*x^2+3*x+1) / ((x-1)*(x+1)*(2*x-1)*(2*x+1)*(x^2+1)*(4*x^2+1)).
The recurrence is stated for n > 8, so that every index is at least the offset 1. The g.f. is
the formal power series Sum_{n ≥ 1} a(n) x^n over ℚ (constant coefficient 0, as the sequence
starts at n = 1).
-/

namespace OMA.S_oeis_a213244

open PowerSeries

/-- a(n): the number of nonzero 5th powers in GF(2^n). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : GaloisField 2 n // x ≠ 0 ∧ ∃ y : GaloisField 2 n, y ^ 5 = x}

/-- Barker's conjectures: the linear recurrence and the generating function. -/
theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 17 * a (n - 4) - 16 * a (n - 8)) ∧
    mk (fun n => if n = 0 then (0 : ℚ) else a n) =
      (X * (8 * X ^ 6 + 12 * X ^ 5 + 14 * X ^ 4 + 3 * X ^ 3 + 7 * X ^ 2 + 3 * X + 1)) *
        ((X - 1) * (X + 1) * (2 * X - 1) * (2 * X + 1) * (X ^ 2 + 1) * (4 * X ^ 2 + 1))⁻¹ := by
  sorry

end OMA.S_oeis_a213244
