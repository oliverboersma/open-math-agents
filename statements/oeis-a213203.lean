import Mathlib

/-!
# A213203: The sum of the first n! integers, with every n-th integer taken as negative.

Source: https://oeis.org/A213203
Credit: @agchua

R. J. Mathar (Mar 21 2013), in the formula section of A213203:
  Conjecture: a(n) + (-n^2-n-11)*a(n-1) + (n^3+7*n^2-13*n+39)*a(n-2)
  - 2*(n-2)*(4*n^2-2*n-15)*a(n-3) + 20*(n-2)*(n-3)*(n-4)*a(n-4) = 0.
Here a(n) is the sum of k over 1 ≤ k ≤ n!, where k is replaced by -k when n divides k (the
examples of the entry: a(3) = 1+2-3+4+5-6 = 3). The sequence has offset 1 (a(1) = -1). The
recurrence uses a(n-4), so the conjecture is stated for n ≥ 5 (then n, ..., n-4 are all indices
of the sequence). Terms are taken in ℤ.
-/

namespace OMA.S_oeis_a213203

/-- A213203(n): the sum of 1, 2, ..., n!, where every k divisible by n is counted as -k. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n.factorial, if n ∣ k then -(k : ℤ) else (k : ℤ)

/-- Mathar's conjecture: the order-4 recurrence holds for all n ≥ 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n + (-((n : ℤ) ^ 2) - (n : ℤ) - 11) * a (n - 1)
      + ((n : ℤ) ^ 3 + 7 * (n : ℤ) ^ 2 - 13 * (n : ℤ) + 39) * a (n - 2)
      - 2 * ((n : ℤ) - 2) * (4 * (n : ℤ) ^ 2 - 2 * (n : ℤ) - 15) * a (n - 3)
      + 20 * ((n : ℤ) - 2) * ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a213203
