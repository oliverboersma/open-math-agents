import Mathlib

/-!
# A213248: Number of nonzero elements in GF(2^n) that are 13th powers

Source: https://oeis.org/A213248
Credit: @ivillar

Joerg Arndt (Jun 07 2012): a(n) (offset 1) is the number of nonzero elements x of the finite field
GF(2^n) (Mathlib's `GaloisField 2 n`) that are 13th powers, i.e. x = y^13 for some y in GF(2^n).

Conjectures from Colin Barker, Aug 24 2014:
  a(n) = 4097*a(n-12) - 4096*a(n-24),
  G.f.: x*(2048*x^22 +3072*x^21 +3584*x^20 +3840*x^19 +3968*x^18 +4032*x^17 +4064*x^16 +4080*x^15
    +4088*x^14 +4092*x^13 +4094*x^12 +315*x^11 +2047*x^10 +1023*x^9 +511*x^8 +255*x^7 +127*x^6
    +63*x^5 +31*x^4 +15*x^3 +7*x^2 +3*x +1) / (4096*x^24 -4097*x^12 +1).
The recurrence is stated for n > 24, so that every index is at least the offset 1. The g.f. is
the formal power series Sum_{n ≥ 1} a(n) x^n over ℚ (constant coefficient 0, as the sequence
starts at n = 1).
-/

namespace OMA.S_oeis_a213248

open PowerSeries

/-- a(n): the number of nonzero 13th powers in GF(2^n). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : GaloisField 2 n // x ≠ 0 ∧ ∃ y : GaloisField 2 n, y ^ 13 = x}

/-- Barker's conjectures: the linear recurrence and the generating function. -/
theorem main :
    (∀ n : ℕ, 24 < n → (a n : ℤ) = 4097 * a (n - 12) - 4096 * a (n - 24)) ∧
    mk (fun n => if n = 0 then (0 : ℚ) else a n) =
      (X * (2048 * X ^ 22 + 3072 * X ^ 21 + 3584 * X ^ 20 + 3840 * X ^ 19 + 3968 * X ^ 18 + 4032 * X ^ 17 + 4064 * X ^ 16 + 4080 * X ^ 15 + 4088 * X ^ 14 + 4092 * X ^ 13 + 4094 * X ^ 12 + 315 * X ^ 11 + 2047 * X ^ 10 + 1023 * X ^ 9 + 511 * X ^ 8 + 255 * X ^ 7 + 127 * X ^ 6 + 63 * X ^ 5 + 31 * X ^ 4 + 15 * X ^ 3 + 7 * X ^ 2 + 3 * X + 1)) *
        (4096 * X ^ 24 - 4097 * X ^ 12 + 1)⁻¹ := by
  sorry

end OMA.S_oeis_a213248
