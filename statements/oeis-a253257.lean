import Mathlib

/-!
# A253257: Least positive integer k such that prime(k*n) has the form p^2 - 2 with p prime, or 0 if no such k exists.

Source: https://oeis.org/A253257
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A253257): `a(n) > 0` for all `n > 0`, i.e. for every `n ≥ 1`
there is a positive integer `k` such that `prime(k n) = p^2 - 2` for some prime `p`. This is
stronger than the conjecture that there are infinitely many primes of the form `p^2 - 2` with `p`
prime. (Sun's further conjectures with `2p^2 - 1`, `4p^2 + 1`, `p^2 + p + 1` are not stated here.)

Formalization notes:
* `prime(i)` is the `i`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (i - 1)`.
* For a prime `p`, `p^2 ≥ 4`, so `p ^ 2 - 2` in `ℕ` is the integer `p^2 - 2`.
* For `n = 1, ..., 8` the least such `k` is 1, 2, 3, 1, 3, 12, 47, 9, matching the data of A253257.
-/

namespace OMA.S_oeis_a253257

/-- Sun's conjecture: for every `n ≥ 1` some `prime(k n)`, `k ≥ 1`, equals `p^2 - 2` with `p` prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ, 1 ≤ k ∧ ∃ p : ℕ, p.Prime ∧ Nat.nth Nat.Prime (k * n - 1) = p ^ 2 - 2 := by
  sorry

end OMA.S_oeis_a253257
