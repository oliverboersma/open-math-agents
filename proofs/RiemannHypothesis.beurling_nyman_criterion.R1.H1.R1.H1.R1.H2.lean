import OMAReductions.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1_H1_R1
import Mathlib

/-! A half-line approximation controls the local L² error and the first moment. -/
open RiemannHypothesis MeasureTheory Set Filter
open scoped ENNReal

namespace HalfLineError

theorem controls (n : ℕ) (c : Fin n → ℝ) :
    let θ := fun i : Fin n => 1 / ((i.val : ℝ) + 1)
    let μ := volume.restrict (Ioc (0 : ℝ) 1)
    let one := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ)
    let E := eLpNorm (fun x : ℝ => (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x -
      ∑ i, c i * fractScalarInv (θ i) x) 2 (volume.restrict (Ioi 0))
    E ≠ ⊤ → dist one (fractScalarInvSumL2 n c θ) + |∑ i, c i * θ i| ≤ 3 * E.toReal := by
  dsimp only
  let θ (i : Fin n) : ℝ := 1 / ((i.val : ℝ) + 1)
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  let ν := volume.restrict (Ioc (1 : ℝ) 2)
  let ρ := volume.restrict (Ioi (0 : ℝ))
  let one := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ)
  let f (x : ℝ) := ∑ i, c i * fractScalarInv (θ i) x
  let g (x : ℝ) := (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x - f x
  let y := fractScalarInvSumL2 n c θ
  let m := ∑ i, c i * θ i
  let E := eLpNorm g 2 ρ
  change E ≠ ⊤ → dist one y + |m| ≤ 3 * E.toReal
  intro hE
  have μle : μ ≤ ρ := Measure.restrict_mono_set volume (fun _ hx => hx.1)
  have νle : ν ≤ ρ := Measure.restrict_mono_set volume (fun _ hx => zero_lt_one.trans hx.1)
  have hparts : ∀ᵐ x ∂μ, ∀ i : Fin n,
      (c i • (fractScalarInv_memLp2 (θ i)).toLp (fractScalarInv (θ i))) x =
        c i * fractScalarInv (θ i) x := by
    apply ae_all_iff.2
    intro i
    filter_upwards [Lp.coeFn_smul (c i) ((fractScalarInv_memLp2 (θ i)).toLp (fractScalarInv (θ i))),
      (fractScalarInv_memLp2 (θ i)).coeFn_toLp] with x hsmul ht
    rw [hsmul]
    change c i * (fractScalarInv_memLp2 (θ i)).toLp (fractScalarInv (θ i)) x =
      c i * fractScalarInv (θ i) x
    rw [ht]
  have hy : (y : ℝ → ℝ) =ᵐ[μ] f := by
    unfold y fractScalarInvSumL2
    apply (Lp.coeFn_fun_finsetSum Finset.univ _).trans
    filter_upwards [hparts] with x hx
    exact Finset.sum_congr rfl (fun i _ => hx i)
  have hone : (one : ℝ → ℝ) =ᵐ[μ] (Ioc (0 : ℝ) 1).indicator (fun _ => 1) := by
    have h := indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := measure_ne_top μ univ) (c := (1 : ℝ))
    filter_upwards [h, ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx hx'
    simpa [one, indicator_of_mem hx'] using hx
  have hlocal : dist one y ≤ E.toReal := by
    rw [Lp.dist_edist, Lp.edist_def, eLpNorm_congr_ae (hone.sub hy)]
    exact ENNReal.toReal_mono hE (eLpNorm_mono_measure g μle)
  have htail : ∀ x ∈ Ioc (1 : ℝ) 2, g x = -(m / x) := by
    intro x hx
    have hx0 : 0 < x := zero_lt_one.trans hx.1
    have hf (i : Fin n) : fractScalarInv (θ i) x = θ i / x := by
      apply Int.fract_eq_self.mpr
      have ht0 : 0 ≤ θ i := by dsimp [θ]; positivity
      have ht1 : θ i ≤ 1 := by
        apply (div_le_one (by positivity : 0 < (i.val : ℝ) + 1)).2
        linarith [Nat.cast_nonneg (α := ℝ) i.val]
      exact ⟨div_nonneg ht0 hx0.le, (div_lt_one hx0).2 (ht1.trans_lt hx.1)⟩
    have hout : x ∉ Ioc (0 : ℝ) 1 := fun h => hx.1.not_ge h.2
    simp [g, f, m, indicator_of_notMem hout, hf, ← mul_div_assoc, ← Finset.sum_div]
  have hab : eLpNorm (fun _ : ℝ => |m| / 2) 2 ν ≤ E := by
    refine (eLpNorm_mono_ae (f := fun _ : ℝ => |m| / 2) (g := g) ?_).trans
      (eLpNorm_mono_measure g νle)
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx.1
    have hmnonneg : 0 ≤ |m| / 2 := by positivity
    rw [Real.norm_of_nonneg hmnonneg, htail x hx, norm_neg,
      Real.norm_eq_abs, abs_div, abs_of_pos hx0]
    exact div_le_div_of_nonneg_left (abs_nonneg m) hx0 hx.2
  have hv : ν univ = 1 := by norm_num [ν, Measure.restrict_apply_univ, Real.volume_Ioc]
  rw [eLpNorm_const' _ (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp : (2 : ℝ≥0∞) ≠ ⊤), hv, ENNReal.one_rpow, mul_one,
    Real.enorm_eq_ofReal (show 0 ≤ |m| / 2 by positivity)] at hab
  have hreal := ENNReal.toReal_mono hE hab
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ |m| / 2)] at hreal
  linarith

end HalfLineError

theorem OMA.solution : OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1_H1_R1.H2 := HalfLineError.controls