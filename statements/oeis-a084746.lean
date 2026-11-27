import Mathlib

/-!
# A084746: Smallest k such that n^k - k is a prime, or 0 if no such number exists.

Source: https://oeis.org/A084746
Credit: @divmxnd0x

Conjecture (stated in A084746): no entry is zero, i.e. for every `n ≥ 2` (the offset of the
sequence) there is some `k ≥ 1` such that `n^k - k` is prime.

Formalization notes:
* For `n ≥ 2` and every `k` we have `n ^ k ≥ k`, so the truncated subtraction `n ^ k - k` in `ℕ`
  is the integer `n^k - k`.
* `k = 0` gives `n ^ 0 - 0 = 1`, which is not prime, so requiring `0 < k` does not change the
  statement; it matches the least `k` listed in the data.
* The least such `k` for `n = 2, ..., 21` is 2, 1, 1, 2, 1, 2, 1, 2, 3, 18, 1, 2, 1, 2, 3, 6, 1,
  2, 1, 2, matching the data of A084746.
-/

namespace OMA.S_oeis_a084746

/-- The conjecture of A084746: for every `n ≥ 2` some `n^k - k` with `k ≥ 1` is prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, 0 < k ∧ (n ^ k - k).Prime := by
  sorry

end OMA.S_oeis_a084746
