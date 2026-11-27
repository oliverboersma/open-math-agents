import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Set.Card

/-!
# Equal-angle triple intersections inside an equilateral triangle

At each vertex take the m interior rays that divide its angle into m+1
equal parts. Trigonometric Ceva identifies an interior triple intersection
with exactly one ordered choice of three rays whose cyclic sine ratios
multiply to one. This is the sine form of the tangent ratio in the entry.
The formula gives the coefficients of its conjectured ordinary generating function.

Source: https://oeis.org/A387471
Credit: @DomTheDeveloper
-/

namespace OMA.S_oeis_a387471

/-- For the ray numbered i from zero, the ratio is sin(theta)/sin(pi/3-theta). -/
noncomputable def ratio (m i : ℕ) : ℝ :=
  let x : ℝ := ((i : ℝ) + 1) * Real.pi / (3 * ((m : ℝ) + 1))
  Real.sin x / Real.sin (Real.pi / 3 - x)

/-- Independent ordered indices select the rays at the three labelled vertices. -/
noncomputable def d (m : ℕ) : ℕ :=
  Set.ncard {t : Fin m × Fin m × Fin m |
    ratio m t.1 * ratio m t.2.1 * ratio m t.2.2 = 1}

/-- In the odd case m=2n-1, the count has one correction term every five indices. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    d (2 * n - 1) = if 5 ∣ n then 6 * n + 7 else 6 * n - 5 := by
  sorry

end OMA.S_oeis_a387471
