import Mathlib

/-!
# Mahler's volume-product conjecture

Source: https://en.wikipedia.org/wiki/Mahler_volume
Credit: @LAPRAI

For every convex body `K ⊂ ℝⁿ` symmetric about the origin, `vol(K) · vol(K°) ≥ 4ⁿ / n!`, where
`K°` is the polar body; equality holds for the cube (and its polar, the cross-polytope).

## Encoding

* `ℝⁿ` is `EuclideanSpace ℝ (Fin n)`, with its standard inner product and Lebesgue measure
  `MeasureTheory.volume`.
* A *convex body* is a compact convex set with nonempty interior (the source's definition).
* *Symmetric about the origin*: `x ∈ K → -x ∈ K`.
* The *polar body* is `K° = {y | ⟪x, y⟫ ≤ 1 for all x ∈ K}`.
* Volumes are taken in `ℝ≥0∞`; for a convex body both are finite and positive, so the product is
  the source's Mahler volume.
-/

namespace OMA.S_wpc_mahler_conjecture

open MeasureTheory

/-- The polar body `K° = {y | ⟪x, y⟫ ≤ 1 for all x ∈ K}`. -/
def polarBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ x ∈ K, inner ℝ x y ≤ (1 : ℝ)}

/-- A convex body: a compact convex set with nonempty interior. -/
def IsConvexBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- **Mahler's conjecture.** Every origin-symmetric convex body `K ⊂ ℝⁿ` satisfies
`vol(K) · vol(K°) ≥ 4ⁿ / n!`. -/
theorem main : ∀ (n : ℕ) (K : Set (EuclideanSpace ℝ (Fin n))),
    IsConvexBody K → (∀ x ∈ K, -x ∈ K) →
    (4 : ENNReal) ^ n / (n.factorial : ENNReal) ≤ volume K * volume (polarBody K) := by
  sorry

end OMA.S_wpc_mahler_conjecture
