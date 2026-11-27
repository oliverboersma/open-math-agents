import Mathlib

/-!
# A249902: Numbers n such that 2n-1 and sigma(n) are both primes

Source: https://oeis.org/A249902
Credit: @niclorusso

Conjecture (in the comments of A249902): 2 and 9 are the only numbers n such that 2n - 1, 2n + 1
and sigma(n) are all primes.

Conventions:
* sigma(n) is the sum of the divisors of n, Mathlib's `ArithmeticFunction.sigma 1 n`.
* n ranges over the positive integers (for n = 0, 2n - 1 is not prime anyway).
* "the only numbers" is stated as a set equality; both qualify: (3, 5, sigma(2) = 3) and
  (17, 19, sigma(9) = 13).
-/

namespace OMA.S_oeis_a249902

open ArithmeticFunction

/-- The conjecture on A249902: the positive `n` with `2n - 1`, `2n + 1` and `sigma(n)` all prime
are exactly `2` and `9`. -/
theorem main :
    {n : ℕ | 0 < n ∧ (2 * n - 1).Prime ∧ (2 * n + 1).Prime ∧ (sigma 1 n).Prime} = {2, 9} := by
  sorry

end OMA.S_oeis_a249902
