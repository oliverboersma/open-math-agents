import Mathlib

/-!
# A294200: Primes p such that 2^p - 2 is a practical number.

Source: https://oeis.org/A294200
Credit: @darealpandaboi

Conjecture: The sequence has infinitely many terms. In other words, there are infinitely many
practical numbers of the form 2^p - 2 with p prime.

Translation notes.
* A practical number (A005153) is a positive integer n such that every smaller nonnegative
  integer is a sum of distinct divisors of n (0 is the empty sum). This is equivalent to the
  form every k <= sigma(n) is such a sum.
* For p prime, 2^p - 2 >= 2, so positivity is automatic in the set below.
* This reading reproduces the listed data: the primes p < 62 in the set are
  2, 3, 5, 7, 11, 13, 17, 19, 29, 31, 37, 41, 43, 53, 61 (checked by computer).
-/

namespace OMA.S_oeis_a294200

/-- n is practical: every m < n is a sum of distinct divisors of n. -/
def IsPractical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, m < n → ∃ s ⊆ n.divisors, ∑ d ∈ s, d = m

theorem main : {p : ℕ | p.Prime ∧ IsPractical (2 ^ p - 2)}.Infinite := by
  sorry

end OMA.S_oeis_a294200
