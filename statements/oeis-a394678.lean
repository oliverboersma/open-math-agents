import Mathlib

/-!
# A394678: a(n) = (n! - 1) mod n^2

Source: https://oeis.org/A394678
Credit: @xor2k

Formalizes the OEIS A394678 conjecture: Excluding the case a(4) = 7, when a(n) is a prime
number, n is a prime such that n^2 - n - 1 is a prime (A091567).

Conventions:
* offset 1, so the statement is for all `n ≥ 1` with `n ≠ 4` (the excluded case);
* `n! - 1` uses natural subtraction, which is exact since `n! ≥ 1`;
* `mod` is `%` on `ℕ`;
* membership of `n` in A091567 (primes `p` such that `p^2 - p - 1` is prime) is spelled out as
  `Nat.Prime n ∧ Nat.Prime (n ^ 2 - n - 1)`; the natural subtraction is exact for `n ≥ 2`.
-/

namespace OMA.S_oeis_a394678

/-- `a(n) = (n! - 1) mod n^2`. -/
def a (n : ℕ) : ℕ :=
  (Nat.factorial n - 1) % n ^ 2

/-- For `n ≥ 1`, `n ≠ 4`: if `a(n)` is prime then `n` is a prime with `n^2 - n - 1` prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → n ≠ 4 → Nat.Prime (a n) →
      Nat.Prime n ∧ Nat.Prime (n ^ 2 - n - 1) := by
  sorry

end OMA.S_oeis_a394678
