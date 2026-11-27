import Mathlib

/-!
# Are there infinitely many Lucas primes?

Source: https://en.wikipedia.org/wiki/Lucas_number#Lucas_primes
Credit: @sntntHb

The Lucas numbers are `L 0 = 2`, `L 1 = 1`, `L (n + 2) = L (n + 1) + L n`. A Lucas prime is a
Lucas number that is prime. It is not known whether there are infinitely many Lucas primes.
The statement below asserts that there are.

Conventions:
- The set is indexed by `n`. Since `L n` is strictly increasing for `n ≥ 1`, distinct indices
  give distinct values apart from finitely many, so infinitely many indices with `L n` prime is
  the same as infinitely many Lucas primes.
-/

namespace OMA.S_wp_are_there_infinitely_many_lucas_primes

/-- The Lucas numbers: `2, 1, 3, 4, 7, 11, 18, …`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

theorem main : {n : ℕ | (lucas n).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_lucas_primes
