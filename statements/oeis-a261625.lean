import Mathlib

/-!
# A261625: Number of primes p <= n such that (p-1)*n+1 is prime.

Source: https://oeis.org/A261625
Credit: @divmxnd0x

Conjecture (stated in A261625): `a(n) > 0` for all `n > 1`, i.e. for every `n > 1` there is a
prime `p ≤ n` such that `(p - 1) n + 1` is prime.

Formalization notes:
* For a prime `p`, `p - 1` in `ℕ` is the integer `p - 1`.
* With this definition `a(1), ..., a(20)` = 0, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 4, 3, 1, 5,
  2, 2 (data of A261625), and every `n` with `2 ≤ n < 3002` has such a prime.
-/

namespace OMA.S_oeis_a261625

/-- The conjecture of A261625: for every `n > 1` some prime `p ≤ n` makes `(p-1) n + 1` prime. -/
theorem main : ∀ n : ℕ, 1 < n → ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ ((p - 1) * n + 1).Prime := by
  sorry

end OMA.S_oeis_a261625
