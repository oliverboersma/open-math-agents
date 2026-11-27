import Mathlib

/-!
# OEIS A206328: primes n^2+1 such that (n+2)^2+1 is also prime

Source: https://oeis.org/A206328 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence lists the primes of the form `n^2+1` such that `(n+2)^2+1` is also prime
(5, 17, 197, 577, ...). The entry records the comment:

  Conjecture: this sequence is infinite.

We formalize this conjecture: the set of primes `p` such that `p = n^2 + 1` for some natural
number `n` with `(n+2)^2 + 1` prime is infinite.
-/

namespace OMA.S_oeis_a206328

/-- Infinitely many primes `n^2 + 1` have `(n+2)^2 + 1` prime as well. -/
theorem main :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = n ^ 2 + 1 ∧ ((n + 2) ^ 2 + 1).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a206328
