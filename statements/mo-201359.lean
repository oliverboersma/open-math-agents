import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Convex.Basic

/-!
# Disks centered on one side of a shortest area-bisecting chord

Source: https://mathoverflow.net/questions/201359
Credit: @LDJAI

A planar convex region is a compact convex body with nonempty interior.
Both sides include the bisecting line, which has area zero. A nonzero
normal represents an oriented line. Its chord length is the diameter
of its intersection with the body. The source asks for a positive
universal lower bound. The suggested one-quarter value is a further question.
-/

namespace OMA.S_mo_201359

open MeasureTheory

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def side (C : Set Plane) (u : Plane) (t : ℝ) : Set Plane :=
  {x ∈ C | inner ℝ u x ≤ t}

def opposite (C : Set Plane) (u : Plane) (t : ℝ) : Set Plane :=
  {x ∈ C | t ≤ inner ℝ u x}

def bisects (C : Set Plane) (u : Plane) (t : ℝ) : Prop :=
  u ≠ 0 ∧ volume (side C u t) = volume (opposite C u t)

noncomputable def chordLength (C : Set Plane) (u : Plane) (t : ℝ) : ℝ :=
  Metric.diam {x ∈ C | inner ℝ u x = t}

theorem main : ∃ α : ℝ, 0 < α ∧
    ∀ (C : Set Plane), IsCompact C → Convex ℝ C → (interior C).Nonempty →
    ∀ (u : Plane) (t : ℝ), bisects C u t →
    (∀ (v : Plane) (s : ℝ), bisects C v s → chordLength C u t ≤ chordLength C v s) →
    ∀ (p : Plane), p ∈ side C u t → ∀ (r : ℝ), 0 < r →
      ENNReal.ofReal α * volume (C ∩ Metric.closedBall p r) ≤
        volume (side C u t ∩ Metric.closedBall p r) := by
  sorry

end OMA.S_mo_201359
