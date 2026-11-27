import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R2
import Mathlib

-- Step Green3.green_3.R1.H2.R1.H2.R2.H2: hypothesis H2 of reduction Green3.green_3.R1.H2.R1.H2.R2
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Green3StepR2H2

open MeasureTheory Set Filter Topology

/-- The antiderivative `-(u - a + 1) * exp (-u)` of `(u - a) * exp (-u)`. -/
lemma hasDerivAt_aux (a u : ℝ) :
    HasDerivAt (fun u : ℝ => -(u - a + 1) * Real.exp (-u)) ((u - a) * Real.exp (-u)) u := by
  have h1 : HasDerivAt (fun u : ℝ => a - 1 - u) (-1) u := (hasDerivAt_id' u).const_sub (a - 1)
  have h2 : HasDerivAt (fun u : ℝ => Real.exp (-u)) (Real.exp (-u) * -1) u :=
    (hasDerivAt_neg u).exp
  have h3 := h1.mul h2
  have e : (fun u : ℝ => -(u - a + 1) * Real.exp (-u)) =
      fun u : ℝ => (a - 1 - u) * Real.exp (-u) := by
    funext u
    ring
  rw [e]
  exact h3.congr_deriv (by ring)

lemma tendsto_aux (a : ℝ) :
    Tendsto (fun u : ℝ => -(u - a + 1) * Real.exp (-u)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => u ^ 1 * Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h2 : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h3 : Tendsto (fun u : ℝ => -(u ^ 1 * Real.exp (-u)) + (a - 1) * Real.exp (-u)) atTop
      (𝓝 (-0 + (a - 1) * 0)) := h1.neg.add (h2.const_mul (a - 1))
  have e : (fun u : ℝ => -(u - a + 1) * Real.exp (-u)) =
      fun u : ℝ => -(u ^ 1 * Real.exp (-u)) + (a - 1) * Real.exp (-u) := by
    funext u
    ring
  rw [e]
  simpa using h3

theorem main (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * max (u - a) 0) (Set.Ioi 0) ∧
      (∫ u in Set.Ioi (0 : ℝ), Real.exp (-u) * max (u - a) 0) = Real.exp (-a) := by
  have hpos : ∀ x ∈ Ioi a, 0 ≤ (x - a) * Real.exp (-x) := by
    intro x hx
    have : a < x := hx
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  have hint' : IntegrableOn (fun u : ℝ => (u - a) * Real.exp (-u)) (Ioi a) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_aux a x) hpos (tendsto_aux a)
  have hval : ∫ u in Ioi a, (u - a) * Real.exp (-u) = Real.exp (-a) := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_aux a x) hint' (tendsto_aux a)]
    ring
  have heq1 : EqOn (fun u : ℝ => (u - a) * Real.exp (-u))
      (fun u : ℝ => Real.exp (-u) * max (u - a) 0) (Ioi a) := by
    intro u hu
    have : a < u := hu
    simp only
    rw [max_eq_left (by linarith)]
    ring
  have heq0 : EqOn (fun _ : ℝ => (0 : ℝ)) (fun u : ℝ => Real.exp (-u) * max (u - a) 0) (Ioc 0 a) := by
    intro u hu
    have : u ≤ a := hu.2
    simp only
    rw [max_eq_right (by linarith), mul_zero]
  have hi1 : IntegrableOn (fun u : ℝ => Real.exp (-u) * max (u - a) 0) (Ioi a) :=
    hint'.congr_fun heq1 measurableSet_Ioi
  have hi0 : IntegrableOn (fun u : ℝ => Real.exp (-u) * max (u - a) 0) (Ioc 0 a) :=
    (integrableOn_zero).congr_fun heq0 measurableSet_Ioc
  have hU : Ioc 0 a ∪ Ioi a = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi ha
  have hdisj : Disjoint (Ioc 0 a) (Ioi a) := by
    rw [Set.disjoint_left]
    intro u hu1 hu2
    exact absurd hu1.2 (not_le.mpr hu2)
  refine ⟨hU ▸ hi0.union hi1, ?_⟩
  rw [← hU, setIntegral_union hdisj measurableSet_Ioi hi0 hi1,
    ← setIntegral_congr_fun measurableSet_Ioc heq0, ← setIntegral_congr_fun measurableSet_Ioi heq1,
    hval]
  simp

end Green3StepR2H2

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1_H2_R2.H2 :=
  fun a ha => Green3StepR2H2.main a ha
