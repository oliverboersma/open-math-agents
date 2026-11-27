import Mathlib

/-!
# Are there infinitely many Woodall primes?

Source: https://en.wikipedia.org/wiki/Woodall_prime
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a **Woodall number** is an integer of the form `n * 2 ^ n - 1` for `n ≥ 1`; a
**Woodall prime** is a Woodall number that is prime.  The open question, from "List of unsolved
problems in mathematics", is whether infinitely many Woodall numbers are prime.

So the proposition formalized below is: infinitely many `n ≥ 1` have `n * 2 ^ n - 1` prime.
-/

namespace OMA.S_wp_are_there_infinitely_many_woodall_primes

-- definitions the statement needs (no sorry, no axiom)

/-- `n` yields a **Woodall prime**: `n ≥ 1` and `n * 2 ^ n - 1` is prime. -/
def IsWoodallPrime (n : ℕ) : Prop :=
  1 ≤ n ∧ (n * 2 ^ n - 1).Prime

/-- Are there infinitely many Woodall primes? -/
theorem main : {n : ℕ | IsWoodallPrime n}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_woodall_primes
