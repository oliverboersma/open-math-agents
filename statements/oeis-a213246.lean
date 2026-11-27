import Mathlib

/-!
# A213246: Number of nonzero elements in GF(2^n) that are 9th powers

Source: https://oeis.org/A213246
Credit: @ivillar

Joerg Arndt (Jun 07 2012): a(n) (offset 1) is the number of nonzero elements x of the finite field
GF(2^n) (Mathlib's `GaloisField 2 n`) that are 9th powers, i.e. x = y^9 for some y in GF(2^n).

Conjectures from Colin Barker, Aug 23 2014 (reported verified by Robert Israel, Jun 27 2018):
  a(n) = 65*a(n-6) - 64*a(n-12),
  G.f.: x*(2*x^2 -x +1)*(16*x^8 +16*x^7 +28*x^6 +16*x^5 +25*x^4 +8*x^3 +7*x^2 +2*x +1) /
    ((x -1)*(x +1)*(2*x -1)*(2*x +1)*(x^2 -x +1)*(x^2 +x +1)*(4*x^2 -2*x +1)*(4*x^2 +2*x +1)).
The recurrence is stated for n > 12, so that every index is at least the offset 1. The g.f. is
the formal power series Sum_{n ≥ 1} a(n) x^n over ℚ (constant coefficient 0, as the sequence
starts at n = 1).
-/

namespace OMA.S_oeis_a213246

open PowerSeries

/-- a(n): the number of nonzero 9th powers in GF(2^n). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : GaloisField 2 n // x ≠ 0 ∧ ∃ y : GaloisField 2 n, y ^ 9 = x}

/-- Barker's conjectures: the linear recurrence and the generating function. -/
theorem main :
    (∀ n : ℕ, 12 < n → (a n : ℤ) = 65 * a (n - 6) - 64 * a (n - 12)) ∧
    mk (fun n => if n = 0 then (0 : ℚ) else a n) =
      (X * (2 * X ^ 2 - X + 1) * (16 * X ^ 8 + 16 * X ^ 7 + 28 * X ^ 6 + 16 * X ^ 5 + 25 * X ^ 4 + 8 * X ^ 3 + 7 * X ^ 2 + 2 * X + 1)) *
        ((X - 1) * (X + 1) * (2 * X - 1) * (2 * X + 1) * (X ^ 2 - X + 1) * (X ^ 2 + X + 1) * (4 * X ^ 2 - 2 * X + 1) * (4 * X ^ 2 + 2 * X + 1))⁻¹ := by
  sorry

end OMA.S_oeis_a213246
