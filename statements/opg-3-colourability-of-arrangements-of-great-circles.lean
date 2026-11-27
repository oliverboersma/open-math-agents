import Mathlib

/-!
# 3-Colourability of Arrangements of Great Circles

Source: https://www.openproblemgarden.org/op/3_colourability_of_arrangements_of_great_circles
Credit: @lzvxck

The source: consider a set `S` of great circles on a sphere with no three circles meeting at a
point. The arrangement graph of `S` has a vertex for each intersection point, and an edge for
each arc directly connecting two intersection points. Conjecture: every arrangement graph of a
set of great circles is 3-colourable.

Conventions: the sphere is the unit sphere of `ℝ³`, and the `k` great circles are given by
normal vectors `n i ≠ 0`: circle `i` is the set of unit vectors `x` with `⟪n i, x⟫ = 0`. Any
three distinct circles have no common point, which for great circles means any three normals
are linearly independent; in particular the circles are distinct. We take `k ≥ 3` (with at
most two circles the arrangement graph has at most two vertices). Then each circle carries
`2(k-1) ≥ 4` intersection points, symmetric under `x ↦ -x`, so consecutive points on a circle
are never antipodal and are joined by the shorter arc between them. Two intersection points
`p ≠ q`, `q ≠ -p`, on a common circle `i` are therefore adjacent exactly when no intersection
point on circle `i` lies strictly inside the shorter arc, which is the set of unit vectors
`a p + b q` with `a, b > 0`.
-/

namespace OMA.S_opg_3_colourability_of_arrangements_of_great_circles

/-- `x` lies on the great circle with normal `v`. -/
def OnCircle (v x : EuclideanSpace ℝ (Fin 3)) : Prop := ‖x‖ = 1 ∧ inner ℝ v x = 0

/-- `x` is an intersection point of two of the circles. -/
def IsVertex {k : ℕ} (n : Fin k → EuclideanSpace ℝ (Fin 3)) (x : EuclideanSpace ℝ (Fin 3)) :
    Prop :=
  ∃ i j, i ≠ j ∧ OnCircle (n i) x ∧ OnCircle (n j) x

/-- `p` and `q` are joined by an arc of the arrangement: consecutive intersection points on a
common circle. -/
def IsArc {k : ℕ} (n : Fin k → EuclideanSpace ℝ (Fin 3)) (p q : EuclideanSpace ℝ (Fin 3)) :
    Prop :=
  p ≠ q ∧ q ≠ -p ∧ ∃ i, OnCircle (n i) p ∧ OnCircle (n i) q ∧
    ∀ r, IsVertex n r → OnCircle (n i) r → ¬ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ r = a • p + b • q

/-- **3-colourability of arrangements of great circles (Felsner, Hurtado, Noy, Streinu).**
The arrangement graph of `k ≥ 3` great circles, no three through a common point, has a proper
colouring with three colours. -/
theorem main : ∀ (k : ℕ) (n : Fin k → EuclideanSpace ℝ (Fin 3)), 3 ≤ k →
    (∀ i j l, i ≠ j → i ≠ l → j ≠ l → LinearIndependent ℝ ![n i, n j, n l]) →
      ∃ c : EuclideanSpace ℝ (Fin 3) → Fin 3, ∀ p q, IsVertex n p → IsVertex n q →
        IsArc n p q → c p ≠ c q := by
  sorry

end OMA.S_opg_3_colourability_of_arrangements_of_great_circles
