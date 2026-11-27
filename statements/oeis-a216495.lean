import Mathlib

/-!
# A216495: Primes p such that there exists a number d>0 such that numbers p-d, p-2*d are primes

Source: https://oeis.org/A216495
Credit: @niclorusso

Conjecture (in the comments of A216495): only 5 primes are not in the sequence: 2, 3, 5, 13, 37.

Conventions:
* d ranges over the positive integers. When 2d >= p the number p - 2d is not positive, hence not
  prime; correspondingly the natural-number subtraction gives 0, which is not prime either.
* "only 5 primes are not in the sequence: 2, 3, 5, 13, 37" is stated as a set equality.
-/

namespace OMA.S_oeis_a216495

/-- `p` is a term of A216495: `p` is prime and `p - d`, `p - 2d` are prime for some `d > 0`. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ ∃ d : ℕ, 0 < d ∧ (p - d).Prime ∧ (p - 2 * d).Prime

/-- The conjecture on A216495: the primes that are not terms are exactly `2, 3, 5, 13, 37`. -/
theorem main : {p : ℕ | p.Prime ∧ ¬ IsTerm p} = {2, 3, 5, 13, 37} := by
  sorry

end OMA.S_oeis_a216495
