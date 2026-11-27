import Mathlib

/-!
# A199800: Number of ways to write n = p+q with p, 6q-1 and 6q+1 all prime.

Source: https://oeis.org/A199800
Credit: @sntntHb

Conjecture (Zhi-Wei Sun, stated on the OEIS page): `a(n) > 0` for all `n > 11`, i.e. every integer
`n > 11` can be written as `n = p + q` with `q` a positive integer and `p`, `6q - 1`, `6q + 1` all
prime.

Conventions: `q` ranges over positive integers (the OEIS program sums over `q = 1, …, n - 1`);
with `q ≥ 1` the natural-number subtraction `6 * q - 1` is the integer `6q - 1`.
-/

namespace OMA.S_oeis_a199800

theorem main : ∀ n : ℕ, 11 < n →
    ∃ p q : ℕ, 0 < q ∧ n = p + q ∧ p.Prime ∧ (6 * q - 1).Prime ∧ (6 * q + 1).Prime := by
  sorry

end OMA.S_oeis_a199800
