import Mathlib

/-!
# A258140: Number of ways to write 6*n + 2 as p^2 + q with p and q both prime.

Source: https://oeis.org/A258140
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A258140): `a(n) > 0` except for
`n = 0, 1, 12, 28, 102, 117, 168, 4079`, i.e. `6n + 2` is `p^2 + q` with `p, q` prime if and only if
`n` is not one of these eight numbers.

Formalization notes:
* The statement is the equivalence, for every `n`, between the existence of primes `p, q` with
  `6n + 2 = p^2 + q` and `n` not being one of the eight exceptions.
* With this definition the number of representations for `n = 0, ..., 19` is 0, 0, 1, 1, 1, 2, 2,
  1, 1, 3, 3, 3, 0, 2, 2, 3, 2, 1, 2, 2 (data of A258140), and the `n < 1200` without a
  representation are 0, 1, 12, 28, 102, 117, 168.
-/

namespace OMA.S_oeis_a258140

/-- Sun's conjecture: `6n + 2 = p^2 + q` is solvable in primes exactly when `n` is not one of
0, 1, 12, 28, 102, 117, 168, 4079. -/
theorem main : ∀ n : ℕ, (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ 6 * n + 2 = p ^ 2 + q) ↔
    n ∉ ({0, 1, 12, 28, 102, 117, 168, 4079} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a258140
