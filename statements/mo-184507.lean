import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Arclength of horizontal slices of a continuously differentiable graph

Arnaud Chéritat, MathOverflow 184507, October 15, 2014.
https://mathoverflow.net/questions/184507

The function is represented on the ambient plane. Both the smoothness
hypothesis and the derivative are taken within the closed unit square, so
values outside the square do not affect the question. The horizontal partial
derivative is the differential evaluated on the vector (1, 0).
-/

namespace OMA.S_mo_184507

def interval : Set ℝ := Set.Icc 0 1

def square : Set (ℝ × ℝ) := interval ×ˢ interval

noncomputable def sliceLength (f : ℝ × ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.sqrt (1 + (fderivWithin ℝ f square (x, y) (1, 0)) ^ 2)

theorem main :
    ∀ f : ℝ × ℝ → ℝ, ContDiffOn ℝ 1 f square → ContDiffOn ℝ 1 (sliceLength f) interval := by
  sorry

end OMA.S_mo_184507
