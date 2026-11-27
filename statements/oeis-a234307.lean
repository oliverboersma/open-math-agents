import Mathlib

/-!
# OEIS A234307: sums of gcds of the parts of two-part partitions of 2n

Source: https://oeis.org/A234307 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence is `a(n) = Sum_{i=1..n} gcd(2*n-i, i)` with offset 1 (the sum of the gcds of the
smallest and largest parts in the partitions of `2n` into exactly two parts).

The entry records, among its formulas:

  Conjecture: a(n) = (1/4)*Sum_{k = 1..4*n} (-1)^k *gcd(k, 8*n). - Peter Bala, Jan 01 2024

We formalize this conjecture: for every `n ≥ 1`, the value `a(n)` equals one quarter of the
alternating sum `Sum_{k=1..4n} (-1)^k gcd(k, 8n)`, computed in the rationals.
-/

namespace OMA.S_oeis_a234307

/-- `a(n) = Sum_{i=1..n} gcd(2*n-i, i)`. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, Nat.gcd (2 * n - i) i

/-- Peter Bala's conjecture: `a(n) = (1/4) * Sum_{k=1..4n} (-1)^k gcd(k, 8n)` for all `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) = (1 / 4 : ℚ) *
      ∑ k ∈ Finset.Icc 1 (4 * n), (-1 : ℚ) ^ k * (Nat.gcd k (8 * n) : ℚ) := by
  sorry

end OMA.S_oeis_a234307
