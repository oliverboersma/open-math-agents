import Mathlib

/-!
# A353102: Primes of the form 2^k + 3^k + 6

Source: https://oeis.org/A353102
Credit: @niclorusso

Conjecture (in the comments of A353102): There are infinitely many primes of the form
2^k + 3^k + 6.

Conventions:
* k ranges over the natural numbers.
-/

namespace OMA.S_oeis_a353102

/-- The conjecture on A353102: there are infinitely many primes of the form `2^k + 3^k + 6`. -/
theorem main : {q : ℕ | q.Prime ∧ ∃ k : ℕ, q = 2 ^ k + 3 ^ k + 6}.Infinite := by
  sorry

end OMA.S_oeis_a353102
