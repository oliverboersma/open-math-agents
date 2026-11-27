import Mathlib

/-!
# A050168: a(0) = 1; for n > 0, a(n) = binomial(n, floor(n/2)) + binomial(n-1, floor(n/2)).

Source: https://oeis.org/A050168
Credit: @agchua

R. J. Mathar (Nov 26 2012), in the formula section of A050168:
  Conjecture: (n+1)*a(n) + (n-3)*a(n-1) + 2*(-2*n+1)*a(n-2) + 4*(-n+3)*a(n-3) = 0.
The sequence has offset 0. The recurrence uses a(n-3), so the conjecture is stated for n ≥ 3.
floor(n/2) is the natural-number division n / 2; for n > 0, n - 1 is the natural-number
subtraction. Terms are taken in ℤ.
-/

namespace OMA.S_oeis_a050168

/-- A050168: a(0) = 1; for n > 0, a(n) = C(n, floor(n/2)) + C(n-1, floor(n/2)). -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 1 else ((n.choose (n / 2) : ℕ) : ℤ) + (((n - 1).choose (n / 2) : ℕ) : ℤ)

/-- Mathar's conjecture: the order-3 recurrence holds for all n ≥ 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 1) * a n + ((n : ℤ) - 3) * a (n - 1) + 2 * (-2 * (n : ℤ) + 1) * a (n - 2)
      + 4 * (-(n : ℤ) + 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a050168
