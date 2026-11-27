import Mathlib

/-!
# Is there a metric on the plane for which (unit) circles are triangles?

Source: https://math.stackexchange.com/questions/4769164/is-there-a-metric-on-the-plane-for-which-unit-circles-are-triangles
Credit: @mgv27

With the Euclidean metric on $\mathbb R^2$ unit circles are circles; with the $\ell^1$ metric
they are squares; suitable path metrics give hexagons and other even-sided polygons.
Is there a metric on $\mathbb R^2$ (that gives the usual topology) for which circles, or at
least unit circles, are triangles?

Formalization notes:
* We formalize the weaker "at least unit circles" version, in the natural "yes" reading:
  there is a (symmetric, as clarified by the asker in comments) metric `d` on `ℝ × ℝ` inducing
  the usual topology such that for every point `x`, the unit circle `{y | d x y = 1}` is the
  boundary of a nondegenerate triangle. The triangles may vary with `x` (not required to be
  congruent or translates). Commenters expect the answer to be negative.
* No norm works (unit balls of norms are symmetric), so `d` need not be translation invariant.
* `IsMetric d` lists the metric axioms; nonnegativity follows from them.
* `InducesUsualTopology d`: a set is open in the product topology of `ℝ × ℝ` iff it is open
  for `d`-balls.
* A triangle is `[a,b] ∪ [b,c] ∪ [c,a]` for non-collinear `a, b, c`.
-/

namespace OMA.S_mse_4769164

/-- `d` satisfies the axioms of a (symmetric) metric on `ℝ × ℝ`. -/
def IsMetric (d : ℝ × ℝ → ℝ × ℝ → ℝ) : Prop :=
  (∀ x y, d x y = 0 ↔ x = y) ∧ (∀ x y, d x y = d y x) ∧ (∀ x y z, d x z ≤ d x y + d y z)

/-- The open sets of the metric `d` are exactly the usual open sets of `ℝ × ℝ`. -/
def InducesUsualTopology (d : ℝ × ℝ → ℝ × ℝ → ℝ) : Prop :=
  ∀ U : Set (ℝ × ℝ), IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, d x y < ε → y ∈ U

/-- `S` is the boundary of a nondegenerate triangle in the plane. -/
def IsTriangle (S : Set (ℝ × ℝ)) : Prop :=
  ∃ a b c : ℝ × ℝ, (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0 ∧
    S = segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a

/-- There is a metric on the plane, inducing the usual topology, all of whose unit circles
are triangles. -/
theorem main :
    ∃ d : ℝ × ℝ → ℝ × ℝ → ℝ, IsMetric d ∧ InducesUsualTopology d ∧
      ∀ x : ℝ × ℝ, IsTriangle {y | d x y = 1} := by
  sorry

end OMA.S_mse_4769164
