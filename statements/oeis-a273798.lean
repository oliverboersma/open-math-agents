import Mathlib

/-!
# A273798: Numbers of the form 2^m*p where p is prime and p < 2^m.

Source: https://oeis.org/A273798
Credit: @marcelopierry

Conjecture (in the comments of A273798): A273798 is a subsequence of A116882.

Conventions:
* A273798 lists the numbers x = 2^m * p with m >= 0, p prime and p < 2^m (data 8, 12, 16, 24,
  32, 40, ...).
* A116882 lists the k >= 1 such that (highest odd divisor of k)^2 <= k (data 1, 2, 4, 8, 12,
  ...). The highest odd divisor of k (A000265) is k with all factors 2 removed,
  k / 2^(v_2(k)).
* Both sequences are increasing listings of sets, so being a subsequence is the inclusion of
  the first set in the second.
-/

namespace OMA.S_oeis_a273798

/-- A000265(k): the highest odd divisor of k. -/
def oddPart (k : ℕ) : ℕ := k / 2 ^ k.factorization 2

/-- Membership in A116882. -/
def InA116882 (k : ℕ) : Prop := 1 ≤ k ∧ oddPart k ^ 2 ≤ k

/-- Membership in A273798. -/
def InA273798 (x : ℕ) : Prop := ∃ m p : ℕ, p.Prime ∧ p < 2 ^ m ∧ x = 2 ^ m * p

/-- The conjecture: every term of A273798 is a term of A116882. -/
theorem main : ∀ x : ℕ, InA273798 x → InA116882 x := by
  sorry

end OMA.S_oeis_a273798
