import Mathlib

/-!
# A105403: Numbers n such that prime(n)-1 and prime(n+1)-1 have the same largest prime factor.

Source: https://oeis.org/A105403
Credit: @divmxnd0x

Conjecture (Jon E. Schoenfield, Jul 25 2015): the sequence is full, i.e. its known terms
2, 30, 53, 217 are all of its terms (no more terms below 10^8).

Formalization notes:
* `prime(n)` is the `n`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (n - 1)`; the index
  `n` ranges over `n ≥ 1` (offset 1).
* `gpf m` is the largest prime factor of `m`, with the convention `gpf 1 = 0`; this convention only
  enters for `n = 1`, where `prime(1) - 1 = 1` and `prime(2) - 1 = 2` differ anyway.
* With these definitions the indices `1 ≤ n < 290` with equal largest prime factors are exactly
  2, 30, 53, 217.
-/

namespace OMA.S_oeis_a105403

/-- The largest prime factor of `m` (`0` for `m ≤ 1`). -/
def gpf (m : ℕ) : ℕ :=
  m.primeFactors.sup id

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- Schoenfield's conjecture: 2, 30, 53, 217 are the only `n ≥ 1` such that `prime(n) - 1` and
`prime(n+1) - 1` have the same largest prime factor. -/
theorem main : {n : ℕ | 1 ≤ n ∧ gpf (prime n - 1) = gpf (prime (n + 1) - 1)} = {2, 30, 53, 217} := by
  sorry

end OMA.S_oeis_a105403
