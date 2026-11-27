import Mathlib

/-!
# A373617: Positive integers that cannot be written as a sum of a practical number and a 14-gonal number

Source: https://oeis.org/A373617
Credit: @niclorusso

Conjecture (Somu and Tran (2024), in the comments of A373617): there are finitely many such
integers, and 106878 is the largest such integer. This conjecture was checked up to 10^8.

Conventions:
* A practical number is a positive integer n such that every m with m <= n is a sum of distinct
  divisors of n (Srinivasan's definition; 1, 2, 4, 6, 8, 12, ...).
* The 14-gonal numbers are k(12k-10)/2 for k >= 0 (including 0, as the data of the sequence requires:
  for instance 1 = 1 + 0 is not a term). The division by 2 is exact.
* "106878 is the largest such integer" is stated with `IsGreatest`: 106878 cannot be written in this
  form, and every larger integer can (which also gives the finiteness).
-/

namespace OMA.S_oeis_a373617

/-- `n` is a practical number: every `m <= n` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

/-- The `k`-th 14-gonal number. -/
def polygonal (k : ℕ) : ℕ := k * (12 * k - 10) / 2

/-- `n` is a practical number plus a 14-gonal number. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ p k : ℕ, IsPractical p ∧ p + polygonal k = n

/-- Somu and Tran's conjecture on A373617: 106878 is the largest positive integer that is not a
practical number plus a 14-gonal number. -/
theorem main : IsGreatest {n : ℕ | 0 < n ∧ ¬ IsRepresentable n} 106878 := by
  sorry

end OMA.S_oeis_a373617
