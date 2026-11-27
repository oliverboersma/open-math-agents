import Mathlib

/-!
# A260928: Number of positive integers k < prime(n)/2 such that k + k' is a square, where k' is the unique integer among 1, ..., prime(n)-1 such that k*k' == 1 (mod prime(n)).

Source: https://oeis.org/A260928
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260928): `a(n) > 0` for all `n > 22`. In other words, for any
prime `p > 80` there is a positive integer `k < p/2` such that `k + k'` is a square, where `k'` is
the unique integer among `1, ..., p-1` with `k k' ≡ 1 (mod p)`.

Formalization notes:
* For `0 < k < p`, `k'` is `((k : ZMod p)⁻¹).val`, the representative in `{1, ..., p-1}` of the
  inverse of `k` modulo `p`.
* `k < p/2` is written `2 * k < p`.
* With this definition `a(1), ..., a(15)` = 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 4, 1, 1, 0, 2 (data of
  A260928), and the primes below 1500 with no such `k` are 2, 3, 5, 7, 11, 23, 29, 43, 53, 79.
-/

namespace OMA.S_oeis_a260928

/-- Sun's conjecture: for every prime `p > 80` some `0 < k < p/2` has `k + k⁻¹ mod p` a square. -/
theorem main : ∀ p : ℕ, p.Prime → 80 < p →
    ∃ k : ℕ, 0 < k ∧ 2 * k < p ∧ IsSquare (k + ((k : ZMod p)⁻¹).val) := by
  sorry

end OMA.S_oeis_a260928
