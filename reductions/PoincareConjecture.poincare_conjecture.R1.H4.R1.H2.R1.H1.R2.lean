import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Separate the scalar bound on survival across a finite surgery trace from
the geometric construction of such traces and reconstruction at extinction.
The coefficient of the width is normalized to 3 / (4t + 1).
-/

open Filter Set
open scoped Manifold ContDiff EuclideanGeometry Topology

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2

def H1 : Prop :=
  let Φ := fun (w : ℝ → ℝ) (t : ℝ) =>
    w t * (4 * t + 1) ^ (-(3 / 4) : ℝ) + 2 * Real.pi * (4 * t + 1) ^ (1 / 4 : ℝ)
  ∀ (n : ℕ) (t : ℕ → ℝ) (w : ℕ → ℝ → ℝ), t 0 = 0 → Monotone t →
    (∀ i < n, ContinuousOn (w i) (Icc (t i) (t (i + 1)))) →
    (∀ i < n, ∀ x ∈ Ico (t i) (t (i + 1)), ∀ r > 0,
      ∃ᶠ y in 𝓝[>] x, (y - x)⁻¹ * (Φ (w i) y - Φ (w i) x) < r) →
    (∀ i < n, w (i + 1) (t (i + 1)) ≤ w i (t (i + 1))) →
    0 ≤ w 0 0 → 0 ≤ w n (t n) →
    t n ≤ ((1 + w 0 0 / (2 * Real.pi)) ^ 4 - 1) / 4

def H2 : Prop :=
  let Φ := fun (w : ℝ → ℝ) (t : ℝ) =>
    w t * (4 * t + 1) ^ (-(3 / 4) : ℝ) + 2 * Real.pi * (4 * t + 1) ^ (1 / 4 : ℝ)
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [CompactSpace M] [SecondCountableTopology M] [IsManifold (𝓡 3) ∞ M]
    [SimplyConnectedSpace M],
    ∃ a : ℝ, 0 ≤ a ∧ ∀ T ≥ 0,
      (∃ f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
        ContMDiff (𝓡 3) (𝓡 3) ∞ f ∧ ∀ x, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f x)) ∨
      ∃ (n : ℕ) (t : ℕ → ℝ) (w : ℕ → ℝ → ℝ),
        t 0 = 0 ∧ t n = T ∧ Monotone t ∧ w 0 0 = a ∧ 0 ≤ w n (t n) ∧
        (∀ i < n, ContinuousOn (w i) (Icc (t i) (t (i + 1)))) ∧
        (∀ i < n, ∀ x ∈ Ico (t i) (t (i + 1)), ∀ r > 0,
          ∃ᶠ y in 𝓝[>] x, (y - x)⁻¹ * (Φ (w i) y - Φ (w i) x) < r) ∧
        (∀ i < n, w (i + 1) (t (i + 1)) ≤ w i (t (i + 1)))

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1.H1 := by
  intro compare geometry M _ _ _ _ _ _ _
  obtain ⟨a, ha, trace⟩ := geometry M
  let cutoff := ((1 + a / (2 * Real.pi)) ^ 4 - 1) / 4
  have hpow : 1 ≤ (1 + a / (2 * Real.pi)) ^ 4 := by
    have hdiv : 0 ≤ a / (2 * Real.pi) := div_nonneg ha (by positivity)
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (le_add_of_nonneg_right hdiv) 4
  have hcutoff : 0 ≤ cutoff := div_nonneg (sub_nonneg.mpr hpow) (by norm_num)
  rcases trace (cutoff + 1) (by positivity) with h | ⟨n, t, w, h0, hT, hm, hw, hf, hc, hs, hj⟩
  · exact h
  · have hinit : 0 ≤ w 0 0 := by simpa only [hw] using ha
    have hle := compare n t w h0 hm hc hs hj hinit hf
    rw [hT, hw] at hle
    exact False.elim (by
      change cutoff + 1 ≤ cutoff at hle
      linarith)

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H4_R1_H2_R1_H1_R2
