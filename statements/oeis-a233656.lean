import Mathlib

/-!
# A233656: a(n) = 3*a(n-1) - 2*(n-1), with a(0) = 1

Source: https://oeis.org/A233656
Credit: @xor2k

Formalizes the OEIS A233656 conjecture (offset 0): Last digit of a(n) has repeating pattern
of 20 digits as follows: {1, 3, 7, 7, 5, 7, 1, 1, 9, 1, 5, 5, 3, 5, 9, 9, 7, 9, 3, 3}, with an
equal frequency of the five odd digits.

Conventions: the sequence is defined on `ℤ` (so no truncated subtraction) with `a 0 = 1` and
`a (n + 1) = 3 * a n - 2 * n`, which is `a(n) = 3*a(n-1) - 2*(n-1)` for `n ≥ 1`. All terms are
positive, so the last decimal digit of `a n` is `a n % 10`. The repeating pattern starts at
`n = 0`: the last digit of `a n` is entry number `n % 20` (counted from `0`) of `pattern`.
The equal-frequency clause is stated as: each of the digits `1, 3, 5, 7, 9` occurs exactly
`4` times in the period `pattern`.
-/

namespace OMA.S_oeis_a233656

/-- `a(0) = 1`, `a(n) = 3*a(n-1) - 2*(n-1)`. -/
def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => 3 * a n - 2 * n

/-- The conjectured period of last digits,
`{1, 3, 7, 7, 5, 7, 1, 1, 9, 1, 5, 5, 3, 5, 9, 9, 7, 9, 3, 3}`. -/
def pattern : List ℤ :=
  [1, 3, 7, 7, 5, 7, 1, 1, 9, 1, 5, 5, 3, 5, 9, 9, 7, 9, 3, 3]

/-- The last digit of `a n` is `pattern` at position `n % 20`, and each odd digit occurs
equally often (four times) in the period. -/
theorem main :
    (∀ n : ℕ, a n % 10 = pattern.getD (n % 20) 0) ∧
      (∀ d ∈ ([1, 3, 5, 7, 9] : List ℤ), pattern.count d = 4) := by
  sorry

end OMA.S_oeis_a233656
