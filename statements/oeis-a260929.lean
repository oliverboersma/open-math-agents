import Mathlib

/-!
# A260929: Least positive integer k < prime(n) such that k + k' is a triangular number, where k' is the unique integer among 1,...,prime(n)-1 with k*k' == 1 (mod prime(n)), or 0 if no such k exists.

Source: https://oeis.org/A260929
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260929): `a(n) > 0` for all `n > 7`. In other words, for any
prime `p > 17` there are two integers `k` and `k'` among `1, ..., p-1` with `k k' ≡ 1 (mod p)` such
that `k + k'` is a triangular number.

Formalization notes:
* For `0 < k < p`, `k'` is `((k : ZMod p)⁻¹).val`, the representative in `{1, ..., p-1}` of the
  inverse of `k` modulo `p`.
* A triangular number is `t(t+1)/2` with `t ≥ 0`.
* The primes below 1500 with no such `k` are 2, 3, 5, 13, 17, matching the zeros of the data of
  A260929 (`a(1), a(2), a(3), a(6), a(7)`).
-/

namespace OMA.S_oeis_a260929

/-- Sun's conjecture: for every prime `p > 17` some `0 < k < p` has `k + k⁻¹ mod p` triangular. -/
theorem main : ∀ p : ℕ, p.Prime → 17 < p →
    ∃ k : ℕ, 0 < k ∧ k < p ∧ ∃ t : ℕ, k + ((k : ZMod p)⁻¹).val = t * (t + 1) / 2 := by
  sorry

end OMA.S_oeis_a260929
