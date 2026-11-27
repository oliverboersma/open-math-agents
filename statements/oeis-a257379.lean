import Mathlib

/-!
# A257379: Smallest odd number k such that k * n * 2^n - 1 is prime

Source: https://oeis.org/A257379
Credit: @AkiRA-COM-FP

Formalizes the OEIS A257379 conjecture (offset 1): for every `n >= 1`, there exists an odd
natural number `k` such that `k * n * 2^n - 1` is prime.
-/

namespace OMA.S_oeis_a257379

/-- For every `n >= 1`, there exists an odd `k` such that `k * n * 2^n - 1` is prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, Odd k ∧ (k * n * 2 ^ n - 1).Prime := by
  sorry

end OMA.S_oeis_a257379
