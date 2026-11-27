import Mathlib

/-!
# A136433: a(n+2) = a(n+1)*(n mod 3 + 1) + (n mod 2 + 1), a(1) = 11

Source: https://oeis.org/A136433
Credit: @xor2k

Formalizes the OEIS A136433 conjecture (R. J. Mathar): a(n) = 6*a(n-3) + a(n-6) - 6*a(n-9).

Conventions: offset 1, so the sequence is `a 1, a 2, ...` with `a 1 = 11` and the defining
recurrence `a (n + 2) = a (n + 1) * (n % 3 + 1) + (n % 2 + 1)` for all `n ≥ 0` (this gives
`a 2 = 12`, `a 3 = 26`, `a 4 = 79`, matching the OEIS data). The value `a 0 = 0` is a
placeholder outside the OEIS range; it never enters the statement. The conjectured
recurrence is stated for every `n ≥ 10`, the smallest index for which `a (n - 9)` lies in the
OEIS range, and it is stated in `ℤ` so that the subtraction is genuine (the index subtractions
`n - 3`, `n - 6`, `n - 9` are exact since `n ≥ 10`).
-/

namespace OMA.S_oeis_a136433

/-- A136433 with offset 1: `a 1 = 11` and `a (n + 2) = a (n + 1) * (n % 3 + 1) + (n % 2 + 1)`.
The value `a 0 = 0` is a placeholder outside the OEIS range. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 11
  | n + 2 => a (n + 1) * (n % 3 + 1) + (n % 2 + 1)

/-- For all `n ≥ 10`: `a(n) = 6 a(n-3) + a(n-6) - 6 a(n-9)` (in the integers). -/
theorem main :
    ∀ n : ℕ, 10 ≤ n →
      (a n : ℤ) = 6 * a (n - 3) + a (n - 6) - 6 * a (n - 9) := by
  sorry

end OMA.S_oeis_a136433
