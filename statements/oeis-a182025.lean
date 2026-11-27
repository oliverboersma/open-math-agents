import Mathlib

/-!
# A182025: a(n) = 31*binomial(2*n,n-4) + Sum_{i=1..n-4} binomial(2*n,n-4-i)*(4+i).

Source: https://oeis.org/A182025
Credit: @agchua

R. J. Mathar (Aug 08 2012), in the formula section of A182025:
  Conjecture: 558*(n-4)*(n+4)*a(n) +7*(-631*n^2+777*n+4600)*a(n-1) +4370*(n-1)*(2*n-3)*a(n-2)=0.
The sequence has offset 0. For n < 4 the binomial coefficient binomial(2n, n-4) has a negative
lower index and is 0, and the sum is empty, so a(0) = a(1) = a(2) = a(3) = 0 as in the data; the
definition below makes this case explicit, because natural-number subtraction would give n-4 = 0.
For n ≥ 4 all subtractions are exact (in the sum, i ≤ n-4). The recurrence uses a(n-2), so the
conjecture is stated for n ≥ 2. Terms are taken in ℤ.
-/

namespace OMA.S_oeis_a182025

/-- A182025(n) = 31 C(2n, n-4) + Sum_{i=1..n-4} C(2n, n-4-i) (4+i), which is 0 for n < 4. -/
def a (n : ℕ) : ℤ :=
  if n < 4 then 0
  else 31 * ((2 * n).choose (n - 4) : ℤ)
    + ∑ i ∈ Finset.Icc 1 (n - 4), ((2 * n).choose (n - 4 - i) : ℤ) * (4 + (i : ℤ))

/-- Mathar's conjecture: for n ≥ 2,
558(n-4)(n+4) a(n) + 7(-631n^2+777n+4600) a(n-1) + 4370(n-1)(2n-3) a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    558 * ((n : ℤ) - 4) * ((n : ℤ) + 4) * a n
      + 7 * (-631 * (n : ℤ) ^ 2 + 777 * (n : ℤ) + 4600) * a (n - 1)
      + 4370 * ((n : ℤ) - 1) * (2 * (n : ℤ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a182025
