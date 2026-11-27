import Mathlib

/-!
# A217495: Primes of the form 2*n^2 + 46*n + 21.

Source: https://oeis.org/A217495
Credit: @sntntHb

Conjecture (stated on the OEIS page): `2^a(n) - 1` is not prime for every term `a(n)`; in other
words, these primes are included in A054723.

Conventions:
- The terms are the primes `p = 2*n^2 + 46*n + 21`. We take `n : ℕ`. Allowing all integers `n`
  gives no new primes: the polynomial is symmetric under `n ↦ -23 - n`
  (`2 * (2*n^2 + 46*n + 21) + 487 = (2*n + 23)^2`), so every `n ≤ -23` gives the same value as
  `-23 - n ≥ 0`, and for `-22 ≤ n ≤ -1` the value is negative.
-/

namespace OMA.S_oeis_a217495

/-- The quadratic `2*n^2 + 46*n + 21`. -/
def f (n : ℕ) : ℕ := 2 * n ^ 2 + 46 * n + 21

theorem main : ∀ n : ℕ, (f n).Prime → ¬ (2 ^ f n - 1).Prime := by
  sorry

end OMA.S_oeis_a217495
