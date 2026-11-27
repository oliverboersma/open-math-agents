import Mathlib

/-!
# OEIS A274334: numbers whose cube is the sum of 4 positive cubes

Source: https://oeis.org/A274334 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence lists, in increasing order and with offset 1, the numbers whose cube is the sum
of 4 positive cubes: 7, 12, 13, 14, 18, 20, 21, ... The entry records the comment:

  Conjecture: a(n) = n + 21 for all n > 50. - Charles R Greathouse IV, Jan 14 2017

We formalize this conjecture. The cubes need not be distinct. With offset 1, `a(n)` is the
`(n-1)`-th (zero-indexed) natural number with the property, i.e. `Nat.nth IsTerm (n - 1)`.
-/

namespace OMA.S_oeis_a274334

/-- `k` is a term: `k^3` is the sum of four positive cubes. -/
def IsTerm (k : ℕ) : Prop :=
  ∃ w x y z : ℕ, 0 < w ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧ k ^ 3 = w ^ 3 + x ^ 3 + y ^ 3 + z ^ 3

/-- The `n`-th term (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTerm (n - 1)

/-- Greathouse's conjecture: `a(n) = n + 21` for every `n > 50`. -/
theorem main : ∀ n : ℕ, 50 < n → a n = n + 21 := by
  sorry

end OMA.S_oeis_a274334
