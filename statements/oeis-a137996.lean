import Mathlib

/-!
# A137996: Numbers which are not the sum of a triangular number and zero or a prime = 1 (mod 4)

Source: https://oeis.org/A137996
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A137996): n = 216 is the only number not of the form
n = p + k(k+1)/2 with p a prime or zero.

(The same comment also conjectures that the 123 listed terms A137996(1..123) are the only numbers
that cannot be written in this form with p = 0 or p = 1 (mod 4); only the first, main conjecture is
stated here.)

Conventions:
* n, k range over the natural numbers; k(k+1)/2 with k >= 0 is a triangular number (A000217,
  including 0).
* "216 is the only number not of the form" is stated as: n is of the form p + k(k+1)/2 with p = 0
  or p prime if and only if n /= 216.
-/

namespace OMA.S_oeis_a137996

/-- `n = p + k(k+1)/2` for some `k` and some `p` that is zero or a prime. -/
def IsPrimeOrZeroPlusTriangular (n : ℕ) : Prop :=
  ∃ p k : ℕ, (p = 0 ∨ p.Prime) ∧ p + k * (k + 1) / 2 = n

/-- Sun's conjecture recorded in A137996: every natural number except 216 is a prime or zero plus
a triangular number. -/
theorem main : ∀ n : ℕ, IsPrimeOrZeroPlusTriangular n ↔ n ≠ 216 := by
  sorry

end OMA.S_oeis_a137996
