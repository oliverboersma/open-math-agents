import Mathlib

/-!
# A354074: Factorials that are the sum of the divisors of some m

Source: https://oeis.org/A354074
Credit: @niclorusso

Conjecture (in the comments of A354074): number 2 is the only factorial that is not in this
sequence.

Conventions:
* A factorial is k! for some k >= 0 (`Nat.factorial`; 0! = 1! = 1).
* sigma(m) is the sum of the divisors of m, Mathlib's `ArithmeticFunction.sigma 1 m`, for m >= 1.
* "2 is the only factorial that is not a sum of divisors" is stated as a set equality: the
  factorials f such that no m >= 1 has sigma(m) = f form the set {2}.
-/

namespace OMA.S_oeis_a354074

open ArithmeticFunction

/-- The conjecture on A354074: the only factorial that is not `sigma(m)` for any `m >= 1` is `2`. -/
theorem main :
    {f : ℕ | (∃ k : ℕ, k.factorial = f) ∧ ¬ ∃ m : ℕ, 1 ≤ m ∧ sigma 1 m = f} = {2} := by
  sorry

end OMA.S_oeis_a354074
