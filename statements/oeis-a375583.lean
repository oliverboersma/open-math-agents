import Mathlib

/-!
# A375583: Number of ways n can be written as a sum of a practical number and two 11-gonal numbers

Source: https://oeis.org/A375583
Credit: @niclorusso

Conjecture (in the comments of A375583, checked up to 10^8): a(n) = 0 if and only if n = 11.

Conventions:
* The sequence has offset 1; n ranges over the positive integers.
* A practical number is a positive integer p such that every m with m <= p is a sum of distinct
  divisors of p (1, 2, 4, 6, 8, 12, ...).
* The 11-gonal numbers are k(9k-7)/2 for k >= 0 (0, 1, 11, 30, ...); the division by 2 is exact.
* a(n) = 0 means that n is not a practical number plus two 11-gonal numbers.
-/

namespace OMA.S_oeis_a375583

/-- `n` is a practical number: every `m <= n` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

/-- The `k`-th hendecagonal number. -/
def hendecagonal (k : ℕ) : ℕ := k * (9 * k - 7) / 2

/-- `n` is a practical number plus two 11-gonal numbers. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ p j k : ℕ, IsPractical p ∧ p + hendecagonal j + hendecagonal k = n

/-- The conjecture on A375583: a positive integer is not a practical number plus two hendecagonal
numbers if and only if it is `11`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (¬ IsRepresentable n ↔ n = 11) := by
  sorry

end OMA.S_oeis_a375583
