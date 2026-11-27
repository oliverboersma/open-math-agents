import Mathlib

/-!
# A247341: Let b_k=3...3 consist of k>=1 3's. Then a(n) is the smallest k such that the concatenation 2^n b_k is prime, or a(n)=0 if there is no such prime.

Source: https://oeis.org/A247341
Credit: @LAPRAI

Formalizes the OEIS comment: Conjecture: for all n, a(n)>0.

Conventions: offset 0. `b_k = (10^k - 1) / 3` is the repdigit with `k` threes, and the decimal
concatenation of `2^n` followed by `b_k` is `2^n * 10^k + b_k`.
-/

namespace OMA.S_oeis_a247341

/-- For every `n ≥ 0` some `k ≥ 1` makes the concatenation `2^n 33...3` (`k` threes) prime. -/
theorem main : ∀ n : ℕ, ∃ k : ℕ, 1 ≤ k ∧ (2 ^ n * 10 ^ k + (10 ^ k - 1) / 3).Prime := by
  sorry

end OMA.S_oeis_a247341
