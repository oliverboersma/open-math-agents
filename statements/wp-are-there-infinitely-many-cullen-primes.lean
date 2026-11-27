import Mathlib

/-!
# Are there infinitely many Cullen primes?

Source: https://en.wikipedia.org/wiki/Cullen_number
Credit: @timlantin

A Cullen number is a natural number of the form $C_n = n \cdot 2^n + 1$, where $n$ is a natural
number. A Cullen prime is a Cullen number that is prime. The only known Cullen primes are those for
$n = 1, 141, 4713, 5795, 6611, 18496, \ldots$ (OEIS A005849). Hooley showed that almost all Cullen
numbers are composite, but it is conjectured that there are infinitely many Cullen primes.

Including $n = 0$ changes nothing, since $C_0 = 1$ is not prime.
-/

namespace OMA.S_wp_are_there_infinitely_many_cullen_primes

/-- The `n`-th Cullen number $C_n = n \cdot 2^n + 1$. -/
def cullenNumber (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- Conjecture: there are infinitely many `n` for which the Cullen number $C_n$ is prime. -/
theorem main : {n : ℕ | (cullenNumber n).Prime}.Infinite := by
  sorry

end OMA.S_wp_are_there_infinitely_many_cullen_primes
