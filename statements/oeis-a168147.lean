import Mathlib

/-!
# OEIS A168147: primes of the form 10*n^3 + 1

Source: https://oeis.org/A168147 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence lists the primes of the form `10*n^3 + 1` (11, 271, 641, ...). The entry records
the comment:

  It is conjectured that the sequence is infinite.

We formalize this conjecture: the set of primes `p` such that `p = 10*n^3 + 1` for some
natural number `n` is infinite.
-/

namespace OMA.S_oeis_a168147

/-- There are infinitely many primes of the form `10*n^3 + 1`. -/
theorem main : {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = 10 * n ^ 3 + 1}.Infinite := by
  sorry

end OMA.S_oeis_a168147
