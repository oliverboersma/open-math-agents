import Mathlib

/-!
# A216217: Smallest k such that 6^n - 2*k*3^n - 1 and 6^n - 2*k*3^n + 1 are twin primes

Source: https://oeis.org/A216217
Credit: @niclorusso

A216217(n) (n > 1) is the smallest k such that 6^n - 2*k*3^n - 1 and 6^n - 2*k*3^n + 1 are twin
primes, or 0 if there is no solution.

Conjecture (in the comments of A216217): there is only one zero term: a(5) = 0.

Conventions:
* n ranges over n >= 2 (offset 2) and k over the positive integers; a(n) = 0 means that no k >= 1
  makes both numbers prime.
* The two numbers are integers; when 2*k*3^n >= 6^n they are not both positive, hence not both
  prime. In the natural numbers the truncated values (0 and 1) are not prime either, so natural
  subtraction gives the same condition.
* "only one zero term: a(5) = 0" is stated as: for n >= 2, no such k exists if and only if n = 5.
-/

namespace OMA.S_oeis_a216217

/-- `6^n - 2k3^n - 1` and `6^n - 2k3^n + 1` are both prime. -/
def IsTwinPair (n k : ℕ) : Prop :=
  (6 ^ n - 2 * k * 3 ^ n - 1).Prime ∧ (6 ^ n - 2 * k * 3 ^ n + 1).Prime

/-- The conjecture on A216217: for `n >= 2`, there is no `k >= 1` giving a twin prime pair if and
only if `n = 5`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ((¬ ∃ k : ℕ, 1 ≤ k ∧ IsTwinPair n k) ↔ n = 5) := by
  sorry

end OMA.S_oeis_a216217
