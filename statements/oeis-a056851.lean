import Mathlib

/-!
# A056851: Integers n such that the number of digits in n! is a cube.

Source: https://oeis.org/A056851
Credit: @divmxnd0x

Conjecture (Ed Pegg Jr, stated in A056851): `n^3 - n = k!` has a solution if and only if `n` is
2, 3, 5 or 9 (with `k` = 3, 4, 5 and 6 respectively).

Formalization notes:
* `n` and `k` are natural numbers; `n ^ 3 ≥ n`, so the truncated subtraction `n ^ 3 - n` in `ℕ` is
  the integer `n^3 - n = (n - 1) n (n + 1)`.
* For `n = 0, 1` the left side is `0`, which is not a factorial, consistent with the statement.
* The `n < 3000` for which `n^3 - n` equals some `k!` with `k < 40` are exactly 2, 3, 5, 9.
-/

namespace OMA.S_oeis_a056851

/-- Pegg's conjecture: `n^3 - n` is a factorial exactly for `n ∈ {2, 3, 5, 9}`. -/
theorem main : ∀ n : ℕ, (∃ k : ℕ, n ^ 3 - n = k.factorial) ↔ n ∈ ({2, 3, 5, 9} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a056851
