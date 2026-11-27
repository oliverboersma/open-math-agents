import Mathlib

/-!
# Albertson conjecture

Source: https://en.wikipedia.org/wiki/Albertson_conjecture
Credit: @sauronsoul-bit

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wp_albertson_conjecture

-- definitions the statement needs (no sorry, no axiom)

/-- A valid drawing of a simple graph G on the plane ℝ × ℝ -/
structure Drawing {V : Type*} (G : SimpleGraph V) where
  pos : V → ℝ × ℝ
  injective_pos : Function.Injective pos
  edgeCurve : G.edgeSet → C(unitInterval, ℝ × ℝ)
  -- For each edge e = {u, v}, edgeCurve e connects pos u and pos v
  -- The curve does not pass through any vertex other than its endpoints
  endpoints : ∀ e : G.edgeSet, ∀ u v, e.1 = s(u, v) → (edgeCurve e 0 = pos u ∧ edgeCurve e 1 = pos v) ∨ (edgeCurve e 0 = pos v ∧ edgeCurve e 1 = pos u)
  no_vertex_interior : ∀ e : G.edgeSet, ∀ t : unitInterval, t ≠ 0 → t ≠ 1 → ∀ w : V, edgeCurve e t ≠ pos w

/-- A crossing is a pair of distinct edges whose curves intersect at a point that is not a vertex -/
def Drawing.crossingPoints {V : Type*} {G : SimpleGraph V} (d : Drawing G) : Set (ℝ × ℝ) := {p | ∃ (e₁ e₂ : G.edgeSet) (t₁ t₂ : unitInterval), e₁ ≠ e₂ ∧ d.edgeCurve e₁ t₁ = p ∧ d.edgeCurve e₂ t₂ = p ∧ ∀ w : V, p ≠ d.pos w}

/-- The crossing number of a graph G is the minimum number of crossings over all possible drawings -/
noncomputable def crossingNumber {V : Type*} (G : SimpleGraph V) : ℕ∞ := sInf { n : ℕ∞ | ∃ d : Drawing G, (d.crossingPoints.encard : ℕ∞) = n }

theorem main : ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (n : ℕ), G.chromaticNumber = (n : ℕ∞) → crossingNumber (⊤ : SimpleGraph (Fin n)) ≤ crossingNumber G := by
  sorry

end OMA.S_wp_albertson_conjecture
