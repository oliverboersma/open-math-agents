import Mathlib

/-!
# A167481: Convolution of the central binomial coefficients A000984(n) and (-2)^n.

Source: https://oeis.org/A167481
Credit: @agchua

R. J. Mathar (Nov 16 2011), in the formula section of A167481:
  Conjecture: n*a(n) + 2*(1-n)*a(n-1) + 4*(1-2n)*a(n-2) = 0.
The convolution is a(n) = Sum_{k=0..n} (-2)^(n-k)*C(2k,k), as in the formula section of the
entry. The sequence has offset 0 (a(0) = 1). The recurrence uses a(n-2), so the conjecture is
stated for n ≥ 2 (then n, n-1, n-2 are all indices of the sequence). Terms are taken in ℤ.
-/

namespace OMA.S_oeis_a167481

/-- A167481(n) = Sum_{k=0..n} (-2)^(n-k) * C(2k, k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (-2 : ℤ) ^ (n - k) * ((2 * k).choose k : ℤ)

/-- Mathar's conjecture: for n ≥ 2, n a(n) + 2(1-n) a(n-1) + 4(1-2n) a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℤ) * a n + 2 * (1 - (n : ℤ)) * a (n - 1) + 4 * (1 - 2 * (n : ℤ)) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a167481
