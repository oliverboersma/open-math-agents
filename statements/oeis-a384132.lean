import Mathlib

/-!
# OEIS A384132

Source: https://oeis.org/A384132 (OEIS Foundation, CC BY-SA 4.0).
Credit: @bcrowther86-eng

A384132 lists the positive integers `k` such that `x^3 + y^3 + z^3 + w^3 = k^3` has no integer
solution with `0 < x < y < z < w`, i.e. whose cube is not a sum of four distinct positive cubes.
Data: 1, 2, ..., 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121.

Conjecture (from the sequence entry): a(27) = 121 is the largest integer whose cube cannot be
described as the sum of four distinct positive cubes.

We state it as: 121 is the greatest element of the set of such positive integers `k`. Since
`x, y, z, w` are positive, integer solutions are the same as natural-number solutions.
-/

namespace OMA.S_oeis_a384132

/-- `k ^ 3` is a sum of four distinct positive cubes. -/
def IsSumOfFourDistinctCubes (k : ℕ) : Prop :=
  ∃ x y z w : ℕ, 0 < x ∧ x < y ∧ y < z ∧ z < w ∧ x ^ 3 + y ^ 3 + z ^ 3 + w ^ 3 = k ^ 3

theorem main : IsGreatest {k : ℕ | 0 < k ∧ ¬ IsSumOfFourDistinctCubes k} 121 := by
  sorry

end OMA.S_oeis_a384132
