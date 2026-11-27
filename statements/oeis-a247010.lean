import Mathlib

/-!
# OEIS A247010: primes p such that (p-3)/2 and 2*p+3 are both prime

Source: https://oeis.org/A247010 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence lists the primes `p` such that `(p-3)/2` and `2*p+3` are both prime
(7, 13, 17, 29, 89, ...). The entry records the comment:

  Conjecture: the sequence is infinite.

We formalize this conjecture: the set of such primes is infinite. For an odd prime `p` the
quotient `(p-3)/2` is exact; for `p = 2` the natural-number value is `0`, which is not prime,
matching the fact that `(2-3)/2` is not a prime.
-/

namespace OMA.S_oeis_a247010

/-- Infinitely many primes `p` have both `(p-3)/2` and `2*p+3` prime. -/
theorem main : {p : ℕ | p.Prime ∧ ((p - 3) / 2).Prime ∧ (2 * p + 3).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a247010
