import Mathlib

/-!
# A061357: Number of 0<k<n such that n-k and n+k are both primes.

Source: https://oeis.org/A061357
Credit: @ShoQo

Conjecture (Benoit Cloitre, Apr 29 2003): for n>=4 a(n)>0.

Formalization notes:
* `a(n) > 0` means that some `k` with `0 < k < n` has `n - k` and `n + k` both prime.
* Checked for 4 ≤ n < 10^5. (Equivalent to: every even number ≥ 8 is a sum of two distinct
  primes.)
-/

namespace OMA.S_oeis_a061357

theorem main :
    ∀ n : ℕ, 4 ≤ n → ∃ k : ℕ, 0 < k ∧ k < n ∧ (n - k).Prime ∧ (n + k).Prime := by
  sorry

end OMA.S_oeis_a061357
