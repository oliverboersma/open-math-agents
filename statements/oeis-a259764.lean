import Mathlib

/-!
# A259764: Least prime p such that prime(p*n)-1 is a square, or 0 if no such p exists.

Source: https://oeis.org/A259764
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A259764): `a(n) > 0` for all `n > 0`, i.e. for every `n ≥ 1`
there is a prime `p` such that `prime(p n) - 1` is a square. (Sun's further conjecture with
`prime(p n) + 2` is not stated here.)

Formalization notes:
* `prime(i)` is the `i`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (i - 1)`; primes are
  at least 2, so `prime(i) - 1` in `ℕ` is the integer `prime(i) - 1`.
* With this definition `a(1), ..., a(6)` = 3, 13, 41, 3, 11, 2, matching the data of A259764.
-/

namespace OMA.S_oeis_a259764

/-- Sun's conjecture: for every `n ≥ 1` some prime `p` makes `prime(p n) - 1` a square. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ p : ℕ, p.Prime ∧ IsSquare (Nat.nth Nat.Prime (p * n - 1) - 1) := by
  sorry

end OMA.S_oeis_a259764
