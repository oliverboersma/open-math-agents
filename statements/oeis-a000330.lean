import Mathlib

/-!
# OEIS A000330

Source: https://oeis.org/A000330
Credit: @Heart-galaxy

The source conjectures that every integer is a sum of three generalized square pyramidal numbers.
It also states the stronger conjecture that, for every `r ≥ 3`, every integer is a sum of three
generalized `r`-gonal pyramidal numbers. Generalized indices include negative integers. The
square pyramidal conjecture is the `r = 4` case.
-/

namespace OMA.S_oeis_a000330

def generalizedPolygonalPyramidal (r : ℕ) (n : ℤ) : ℤ :=
  n * (n + 1) * (((r : ℤ) - 2) * n - ((r : ℤ) - 5)) / 6

theorem main : ∀ r : ℕ, 3 ≤ r → ∀ z : ℤ, ∃ a b c : ℤ,
    z = generalizedPolygonalPyramidal r a + generalizedPolygonalPyramidal r b +
      generalizedPolygonalPyramidal r c := by
  sorry

end OMA.S_oeis_a000330
