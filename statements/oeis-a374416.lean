import Mathlib

/-!
# A374416: Number of ways n can be written as a sum of a practical number and two nonagonal numbers

Source: https://oeis.org/A374416
Credit: @niclorusso

Conjecture (in the comments of A374416, checked up to 10^8): a(n) = 0 if and only if n = 23.

Conventions:
* The sequence has offset 1; n ranges over the positive integers.
* A practical number is a positive integer p such that every m with m <= p is a sum of distinct
  divisors of p (1, 2, 4, 6, 8, 12, ...).
* The nonagonal numbers are k(7k-5)/2 for k >= 0 (0, 1, 9, 24, ...); the division by 2 is exact.
* a(n) = 0 means that n is not a practical number plus two nonagonal numbers.
-/

namespace OMA.S_oeis_a374416

/-- `n` is a practical number: every `m <= n` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m ≤ n → ∃ s ⊆ n.divisors, ∑ i ∈ s, i = m

/-- The `k`-th nonagonal number. -/
def nonagonal (k : ℕ) : ℕ := k * (7 * k - 5) / 2

/-- `n` is a practical number plus two nonagonal numbers. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ p j k : ℕ, IsPractical p ∧ p + nonagonal j + nonagonal k = n

/-- The conjecture on A374416: a positive integer is not a practical number plus two nonagonal
numbers if and only if it is `23`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (¬ IsRepresentable n ↔ n = 23) := by
  sorry

end OMA.S_oeis_a374416
