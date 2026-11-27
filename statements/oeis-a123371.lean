import Mathlib

/-!
# A123371: Smallest number k>1 such that (1 + Sum[ i^(2n - 1), {i,1,k} ]) is prime, or 0 if no such number k exists.

Source: https://oeis.org/A123371
Credit: @divmxnd0x

Conjecture (stated in A123371): a(n) > 0 exists for all `n`, i.e. for every `n ≥ 1` (the offset of
the sequence) there is some `k > 1` such that `1 + ∑_{i=1}^{k} i^(2n-1)` is prime.

Formalization notes:
* For `n ≥ 1` the exponent `2 * n - 1` in `ℕ` is the odd number `2n - 1`.
* The least such `k` for `n = 1, 2, 3, 4` is 3, 3, 3, 4, matching the data of A123371.
-/

namespace OMA.S_oeis_a123371

/-- The conjecture of A123371: for every `n ≥ 1` some `1 + 1^(2n-1) + ... + k^(2n-1)` with `k > 1`
is prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 < k ∧ (1 + ∑ i ∈ Finset.Icc 1 k, i ^ (2 * n - 1)).Prime := by
  sorry

end OMA.S_oeis_a123371
