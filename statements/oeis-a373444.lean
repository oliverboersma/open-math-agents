import Mathlib

/-!
# A373444: Positive integers that cannot be written as a sum of a practical number and a heptagonal number

Source: https://oeis.org/A373444
Credit: @niclorusso

Conjecture (Somu and Tran (2024), in the comments of A373444): there are finitely many such
integers, and 79445 is the largest such integer. This conjecture was checked up to 10^8.

Conventions:
* A practical number is a positive integer n such that every m with m <= n is a sum of distinct
  divisors of n (Srinivasan's definition; 1, 2, 4, 6, 8, 12, ...).
* The heptagonal numbers are k(5k-3)/2 for k >= 0 (including 0, as the data of the sequence requires:
  for instance 1 = 1 + 0 is not a term). The division by 2 is exact.
* "79445 is the largest such integer" is stated with `IsGreatest`: 79445 cannot be written in this
  form, and every larger integer can (which also gives the finiteness).
-/

namespace OMA.S_oeis_a373444

/-- `n` is a practical number: every `m <= n` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

/-- The `k`-th heptagonal number. -/
def polygonal (k : ℕ) : ℕ := k * (5 * k - 3) / 2

/-- `n` is a practical number plus a heptagonal number. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ p k : ℕ, IsPractical p ∧ p + polygonal k = n

/-- Somu and Tran's conjecture on A373444: 79445 is the largest positive integer that is not a
practical number plus a heptagonal number. -/
theorem main : IsGreatest {n : ℕ | 0 < n ∧ ¬ IsRepresentable n} 79445 := by
  sorry

end OMA.S_oeis_a373444
