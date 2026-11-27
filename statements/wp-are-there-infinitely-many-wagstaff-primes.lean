import Mathlib

/-!
# Are there infinitely many Wagstaff primes?

Source: https://en.wikipedia.org/wiki/Wagstaff_prime
Credit: @sntntHb

A Wagstaff prime is a prime of the form `(2^p + 1) / 3` where `p` is an odd prime. It is not
known whether there are infinitely many. The statement below asserts that there are.

Conventions:
- For odd `p`, `3 ∣ 2^p + 1`, so the natural-number division `(2 ^ p + 1) / 3` is exact.
- The set is indexed by the exponent `p`; distinct `p` give distinct values `(2^p + 1) / 3`,
  so infinitely many such `p` is the same as infinitely many Wagstaff primes.
-/

namespace OMA.S_wp_are_there_infinitely_many_wagstaff_primes

/-- `p` is an odd prime and `(2^p + 1) / 3` is prime. -/
def IsWagstaffExponent (p : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ ((2 ^ p + 1) / 3).Prime

theorem main : {p : ℕ | IsWagstaffExponent p}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_wagstaff_primes
