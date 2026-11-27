import Mathlib

/-!
# A373611: Positive integers that cannot be written as a sum of a practical number and a nonagonal number

Source: https://oeis.org/A373611
Credit: @niclorusso

Conjecture (Somu and Tran (2024), in the comments of A373611): there are finitely many such
integers, and 325808 is the largest such integer. This conjecture was checked up to 10^8.

Conventions:
* A practical number is a positive integer n such that every m with m <= n is a sum of distinct
  divisors of n (Srinivasan's definition; 1, 2, 4, 6, 8, 12, ...).
* The nonagonal numbers are k(7k-5)/2 for k >= 0 (including 0, as the data of the sequence requires:
  for instance 1 = 1 + 0 is not a term). The division by 2 is exact.
* "325808 is the largest such integer" is stated with `IsGreatest`: 325808 cannot be written in this
  form, and every larger integer can (which also gives the finiteness).
-/

namespace OMA.S_oeis_a373611

/-- `n` is a practical number: every `m <= n` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

/-- The `k`-th nonagonal number. -/
def polygonal (k : ℕ) : ℕ := k * (7 * k - 5) / 2

/-- `n` is a practical number plus a nonagonal number. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ p k : ℕ, IsPractical p ∧ p + polygonal k = n

/-- Somu and Tran's conjecture on A373611: 325808 is the largest positive integer that is not a
practical number plus a nonagonal number. -/
theorem main : IsGreatest {n : ℕ | 0 < n ∧ ¬ IsRepresentable n} 325808 := by
  sorry

end OMA.S_oeis_a373611
