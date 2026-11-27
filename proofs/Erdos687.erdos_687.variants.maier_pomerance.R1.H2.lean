import OMAReductions.R_Erdos687_erdos_687_variants_maier_pomerance_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Asymptotics Filter

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_maier_pomerance_R1.H2 := by
  intro C ε hε
  have hlog : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (isLittleO_log_rpow_rpow_atTop C hε).comp_tendsto hlog
  refine ((isBigO_refl (fun x : ℕ ↦ (x : ℝ) * Real.log x ^ (2 : ℝ)) atTop).mul
    hsmall.isBigO).congr' EventuallyEq.rfl ?_
  filter_upwards [hlog.eventually_ge_atTop 0] with x hx
  change ((x : ℝ) * Real.log x ^ (2 : ℝ)) * Real.log x ^ ε = _
  rw [mul_assoc, ← Real.rpow_add' hx (by linarith : (2 : ℝ) + ε ≠ 0)]
