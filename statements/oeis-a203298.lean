import Mathlib

/-!
# A203298: Second elementary symmetric function of the first n terms of (1,2,2,3,3,4,4,5,5...)

Source: https://oeis.org/A203298
Credit: @ivillar

Clark Kimberling's sequence (offset 2): with t(k) = floor((k+2)/2) for k ≥ 1, i.e. the sequence
1, 2, 2, 3, 3, 4, 4, 5, 5, ..., a(n) is the second elementary symmetric function of
t(1), ..., t(n), namely the sum of t(i)*t(j) over all 1 ≤ i < j ≤ n (the Mathematica program
in the entry uses SymmetricPolynomial[2, ...] with f(k) = Floor[(k+2)/2]).

Conjectures from Colin Barker, Jan 04 2018:
  a(n) = (6*n^4 + 40*n^3 + 48*n^2 - 112*n) / 192 for n even,
  a(n) = (6*n^4 + 40*n^3 + 36*n^2 - 136*n + 54) / 192 for n odd,
  a(n) = 2*a(n-1) + 2*a(n-2) - 6*a(n-3) + 6*a(n-5) - 2*a(n-6) - 2*a(n-7) + a(n-8) for n > 9.
The closed forms are stated over ℚ for every n ≥ 2 (the offset) of the given parity, and the
recurrence over ℤ.
-/

namespace OMA.S_oeis_a203298

/-- t(k) = floor((k+2)/2): the k-th term (k ≥ 1) of 1, 2, 2, 3, 3, 4, 4, ... -/
def t (k : ℕ) : ℕ := (k + 2) / 2

/-- a(n) = Σ_{1 ≤ i < j ≤ n} t(i) t(j), the second elementary symmetric function of t(1..n). -/
def a (n : ℕ) : ℕ := ∑ j ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Ico 1 j, t i * t j

/-- Barker's conjectures: both closed forms and the order-8 recurrence. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n → Even n →
      (a n : ℚ) = (6 * n ^ 4 + 40 * n ^ 3 + 48 * n ^ 2 - 112 * n) / 192) ∧
    (∀ n : ℕ, 2 ≤ n → Odd n →
      (a n : ℚ) = (6 * n ^ 4 + 40 * n ^ 3 + 36 * n ^ 2 - 136 * n + 54) / 192) ∧
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) + 6 * a (n - 5) -
      2 * a (n - 6) - 2 * a (n - 7) + a (n - 8)) := by
  sorry

end OMA.S_oeis_a203298
