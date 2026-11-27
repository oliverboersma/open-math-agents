import Mathlib

/-!
# A386996: Least positive integer m such that prime(2^m + 1) - prime(2^m) = 2*n.

Source: https://oeis.org/A386996
Credit: @mbilenko03

Conjecture (from the entry): `a(n)` exists for any positive integer `n`. In other words,
`{prime(2^m + 1) - prime(2^m) : m = 1, 2, 3, …} = {2*n : n = 1, 2, 3, …}`.

The entry's further remark ('Perhaps, for each n there are infinitely many m …') is phrased as a
possibility, not as a conjecture, and is not stated.

Conventions:
- `prime(j)` is the `j`-th prime with `prime(1) = 2`, as in the OEIS. With Mathlib's 0-indexed
  `Nat.nth Nat.Prime` (`Nat.nth Nat.Prime 0 = 2`) this is `prime j = Nat.nth Nat.Prime (j - 1)`,
  so `prime(2^m + 1) - prime(2^m) = Nat.nth Nat.Prime (2^m) - Nat.nth Nat.Prime (2^m - 1)`.
- `a(n)` exists exactly when some `m ≥ 1` gives the difference `2*n`, which is what `main` states.
  (For `m ≥ 1` both primes are odd, so every difference is even and positive; the inclusion of
  the left set in the right one is automatic.)
-/

namespace OMA.S_oeis_a386996

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 1 ≤ m ∧
      Nat.nth Nat.Prime (2 ^ m) - Nat.nth Nat.Prime (2 ^ m - 1) = 2 * n := by
  sorry

end OMA.S_oeis_a386996
