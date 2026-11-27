import Mathlib

/-!
# OEIS A182560: a(n) = (a(n-1) AND a(n-2)) XOR n

Source: https://oeis.org/A182560 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence is defined by `a(0) = 0`, `a(1) = 1` and `a(n) = (a(n-1) AND a(n-2)) XOR n`, where
AND and XOR are the bitwise operations (data: 0, 1, 2, 3, 6, 7, 0, 7, ...). The entry records
the comment:

  Conjecture: sequence contains infinitely many zeros.

We formalize this conjecture: the set of indices `n` with `a(n) = 0` is infinite.
-/

namespace OMA.S_oeis_a182560

/-- `a(0) = 0`, `a(1) = 1`, `a(n+2) = (a(n+1) AND a(n)) XOR (n+2)`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => (a (n + 1) &&& a n) ^^^ (n + 2)

/-- The sequence vanishes infinitely often. -/
theorem main : {n : ℕ | a n = 0}.Infinite := by
  sorry

end OMA.S_oeis_a182560
