import Mathlib

/-!
# Mathar's recurrence conjecture for OEIS A025754

Source: https://oeis.org/A025754
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A025/A025754.seq
Credit: @sntntHb

OEIS A025754 (offset 0) lists the 9th-order Patalan numbers, with
G.f.: (10-(1-81*x)^(1/9))/9. Expanding (1-81x)^(1/9) by the binomial series gives
a(0) = 1 and a(n) = -(1/9)*binomial(1/9, n)*(-81)^n for n >= 1, where binomial(1/9, n) is
the generalized binomial coefficient (Ring.choose in Mathlib). The first terms are
1, 1, 36, 1836, 107406, 6766578.

Conjecture (R. J. Mathar, Jul 28 2014, quoted from the entry):
n*a(n) + 9*(-9*n+10)*a(n-1) = 0.
The entry gives no range. At n = 1 the left side is 1 + 9 = 10, so the recurrence is stated
here for every n >= 2.
-/

namespace OMA.S_oeis_a025754

/-- OEIS A025754: the coefficients of (10-(1-81*x)^(1/9))/9. -/
noncomputable def a (n : ℕ) : ℚ :=
  if n = 0 then 1 else -(1 / 9) * Ring.choose (1 / 9 : ℚ) n * (-81) ^ n

/-- Mathar's conjectured recurrence, for every n >= 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℚ) * a n + 9 * (-9 * (n : ℚ) + 10) * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a025754
