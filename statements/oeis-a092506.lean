import Mathlib

/-!
# A092506: Prime numbers of the form 2^n + 1

Source: https://oeis.org/A092506
Credit: @niclorusso

Conjecture (Benoit Cloitre, Mar 02 2018, in the comments of A092506): these are the only solutions
to the equation A000010(x)+A000010(x-1)=floor((3x-2)/2).

Conventions:
* A000010 is Euler's totient (`Nat.totient`); floor((3x-2)/2) is the natural-number quotient
  `(3 * x - 2) / 2`.
* x ranges over the positive integers, as in the OEIS (A000010 has offset 1). For x >= 1 both
  x - 1 and 3x - 2 are exact natural-number subtractions; the excluded x = 0 would give 0 = 0 in
  truncated arithmetic, which is not a solution of the original equation.
* "these are the only solutions" is stated as a set equality: the positive solutions x are exactly
  the primes of the form 2^n + 1 (the terms of A092506: 2, 3, 5, 17, 257, 65537, ...).
-/

namespace OMA.S_oeis_a092506

/-- Cloitre's conjecture on A092506: the positive `x` with
`phi(x) + phi(x - 1) = floor((3x - 2)/2)` are exactly the primes of the form `2^n + 1`. -/
theorem main :
    {x : ℕ | 1 ≤ x ∧ Nat.totient x + Nat.totient (x - 1) = (3 * x - 2) / 2} =
      {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = 2 ^ n + 1} := by
  sorry

end OMA.S_oeis_a092506
