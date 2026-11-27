import Mathlib

/-!
# A354072: Perfect numbers that are the sum of the divisors of some number

Source: https://oeis.org/A354072
Credit: @niclorusso

Conjecture (in the comments of A354072): 8128 is the only perfect number that is not in this
sequence.

Conventions:
* Perfect numbers are Mathlib's `Nat.Perfect` (n > 0 and the proper divisors of n sum to n).
* sigma(m) is the sum of the divisors of m, Mathlib's `ArithmeticFunction.sigma 1 m`, for m >= 1.
* "8128 is the only perfect number that is not a sum of divisors" is stated as a set equality.
-/

namespace OMA.S_oeis_a354072

open ArithmeticFunction

/-- The conjecture on A354072: the only perfect number that is not `sigma(m)` for any `m >= 1` is
`8128`. -/
theorem main : {n : ℕ | n.Perfect ∧ ¬ ∃ m : ℕ, 1 ≤ m ∧ sigma 1 m = n} = {8128} := by
  sorry

end OMA.S_oeis_a354072
