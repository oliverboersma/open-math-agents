import OMAReductions.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1_H1_R1
import Mathlib

/-! The explicit damped limit is equation (2.4) of Báez-Duarte,
arXiv:math/0205003. On every interval (b,∞) with b positive, its
error is bounded by C(b,d)/x, where C(b,d) tends to zero with the
damping d. The remaining analytic estimates concern truncation of
the Möbius sum and concentration at the origin. -/
namespace OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1_H1_R1_H1_R1
open Filter ArithmeticFunction Finset Set MeasureTheory RiemannHypothesis
open scoped Topology ENNReal ArithmeticFunction.Moebius

def H1 : Prop :=
  let F := fun d x : ℝ => (riemannZeta (1 + (d : ℂ)))⁻¹.re / x -
    ∑ a ∈ Finset.Ioc 0 ⌊1/x⌋₊, (moebius a : ℝ) / (a : ℝ) ^ d * (⌊1 / ((a:ℝ)*x)⌋ : ℝ)
  RiemannHypothesis → ∀ᶠ d : ℝ in 𝓝[>] 0, ∀ η : ℝ, 0 < η → ∃ n : ℕ,
    eLpNorm (fun x => (∑ i : Fin n, ((moebius (i.val+1) : ℝ) / ((i.val:ℝ)+1)^d) * fractScalarInv (1/((i.val:ℝ)+1)) x) - F d x) 2 (volume.restrict (Ioi 0)) < ENNReal.ofReal η

def H2 : Prop :=
  let F := fun d x : ℝ => (riemannZeta (1 + (d : ℂ)))⁻¹.re / x -
    ∑ a ∈ Finset.Ioc 0 ⌊1/x⌋₊, (moebius a : ℝ) / (a : ℝ) ^ d * (⌊1 / ((a:ℝ)*x)⌋ : ℝ)
  RiemannHypothesis → ∀ η : ℝ, 0 < η → ∃ b : ℝ, 0 < b ∧ ∀ᶠ d : ℝ in 𝓝[>] 0,
    eLpNorm (fun x => F d x + (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x) 2 (volume.restrict (Ioc 0 b)) < ENNReal.ofReal η

lemma moebius_floor (N : ℕ) :
    ∑ a ∈ Finset.Ioc 0 N, moebius a * ((N / a : ℕ) : ℤ) = if 0 < N then 1 else 0 := by
  rw [← sum_Ioc_mul_zeta_eq_sum, moebius_mul_coe_zeta]
  simp [ArithmeticFunction.one_apply, Finset.mem_Ioc]

  rfl

lemma moebius_floor_indicator (x : ℝ) (hx : 0 < x) :
    ∑ a ∈ Finset.Ioc 0 ⌊1/x⌋₊, moebius a * ⌊1 / ((a:ℝ)*x)⌋ =
      (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℤ)) x := by
  have point (a : ℕ) : ⌊1 / ((a:ℝ)*x)⌋ = ((⌊1/x⌋₊ / a : ℕ) : ℤ) := by
    rw [← Nat.floor_div_natCast, Int.natCast_floor_eq_floor (by positivity)]
    congr 1
    rw [div_div, mul_comm]
  simp_rw [point]
  rw [moebius_floor, Set.indicator_apply]
  simp only [Nat.floor_pos, le_div_iff₀ hx, one_mul, Set.mem_Ioc, hx, true_and]

lemma reciprocal_zeta (x : ℝ) :
    Tendsto (fun d : ℝ => (riemannZeta (1 + (d : ℂ)))⁻¹.re / x)
      (𝓝[>] 0) (𝓝 0) := by
  have hd : Tendsto (fun d : ℝ => (d : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))
  have hs : Tendsto (fun d : ℝ => 1 + (d : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using (tendsto_const_nhds (x := (1:ℂ))).add hd
    · filter_upwards [self_mem_nhdsWithin] with d (hd : 0 < d)
      simpa using hd.ne'
  have hr := riemannZeta_residue_one.comp hs
  have hr' : Tendsto (fun d : ℝ => (d:ℂ) * riemannZeta (1+(d:ℂ))) (𝓝[>] 0) (𝓝 1) := by
    simpa [Function.comp_def] using hr
  have hquot := hd.div hr' one_ne_zero
  have hi : Tendsto (fun d : ℝ => (riemannZeta (1+(d:ℂ)))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    apply (show Tendsto _ _ (𝓝 (0:ℂ)) from (by simpa using hquot)).congr'
    filter_upwards [self_mem_nhdsWithin] with d (hd : 0 < d)
    simp [div_mul_eq_div_div, div_self (by exact_mod_cast hd.ne' : (d:ℂ) ≠ 0)]
  simpa [Function.comp_def] using (Complex.continuous_re.continuousAt.tendsto.comp hi).div_const x

lemma awayFromZero :
  let F := fun d x : ℝ => (riemannZeta (1 + (d : ℂ)))⁻¹.re / x -
    ∑ a ∈ Finset.Ioc 0 ⌊1/x⌋₊, (moebius a : ℝ) / (a : ℝ) ^ d * (⌊1 / ((a:ℝ)*x)⌋ : ℝ)
  ∀ b : ℝ, 0 < b → Tendsto (fun d => eLpNorm (fun x => F d x + (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x) 2 (volume.restrict (Ioi b))) (𝓝[>] 0) (𝓝 0) := by
  let dampedLimit := fun d x : ℝ => (riemannZeta (1 + (d : ℂ)))⁻¹.re / x -
    ∑ a ∈ Finset.Ioc 0 ⌊1/x⌋₊, (moebius a : ℝ) / (a : ℝ) ^ d * (⌊1 / ((a:ℝ)*x)⌋ : ℝ)
  let coeffError (a : ℕ) (d : ℝ) : ℝ :=
    (moebius a : ℝ) - (moebius a : ℝ) / (a:ℝ)^d
  let errorBound (b d : ℝ) : ℝ :=
    |(riemannZeta (1 + (d : ℂ)))⁻¹.re| +
    ∑ a ∈ Finset.Ioc 0 ⌊1/b⌋₊, |coeffError a d|
  have errorBound_tendsTo (b : ℝ) : Tendsto (errorBound b) (𝓝[>] 0) (𝓝 0) := by
    have hsum : Tendsto (fun d : ℝ => ∑ a ∈ Finset.Ioc 0 ⌊1/b⌋₊, |coeffError a d|)
        (𝓝[>] 0) (𝓝 (∑ _a ∈ Finset.Ioc 0 ⌊1/b⌋₊, (0:ℝ))) := by
      apply tendsto_finsetSum
      intro a ha
      have pos : 0 < (a:ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp ha).1
      have cont : ContinuousAt (fun d => |coeffError a d|) 0 :=
        (continuousAt_const.sub (continuousAt_const.div (Real.continuousAt_const_rpow pos.ne') (by simp))).abs
      simpa [coeffError] using cont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    unfold errorBound
    simpa [errorBound] using (reciprocal_zeta 1).abs.add hsum
  have error_le {b x : ℝ} (hb : 0 < b) (hx : b < x) (d : ℝ) :
      |dampedLimit d x + (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x| ≤
        errorBound b d / x := by
    have xp := hb.trans hx
    have hid := congrArg (fun z : ℤ => (z:ℝ)) (moebius_floor_indicator x xp)
    have hreal : ∑ a ∈ Finset.Ioc 0 ⌊1/x⌋₊, (moebius a : ℝ) * (⌊1/((a:ℝ)*x)⌋ : ℝ) =
        (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x := by
      simpa [Set.indicator_apply, Int.cast_ite] using hid
    dsimp only [dampedLimit]
    rw [← hreal, sub_add_eq_add_sub, add_sub_assoc, ← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    apply (abs_add_le ..).trans
    dsimp only [errorBound]
    rw [abs_div, abs_of_pos xp, add_div]
    apply add_le_add_right
    calc
      _ ≤ ∑ a ∈ Finset.Ioc 0 ⌊1/x⌋₊, |coeffError a d * (⌊1/((a:ℝ)*x)⌋ : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.Ioc 0 ⌊1/x⌋₊, |coeffError a d| * (1/x) := by
        apply Finset.sum_le_sum
        intro a ha
        have a1 : (1:ℝ) ≤ a := by exact_mod_cast (Finset.mem_Ioc.mp ha).1
        have nonneg : 0 ≤ ((⌊1/((a:ℝ)*x)⌋:ℤ):ℝ) := by
          exact_mod_cast Int.floor_nonneg.mpr (by positivity : 0 ≤ 1/((a:ℝ)*x))
        rw [abs_mul, abs_of_nonneg nonneg]
        gcongr
        exact (Int.floor_le _).trans (one_div_le_one_div_of_le xp (by nlinarith))
      _ ≤ _ := by
        rw [← Finset.sum_mul, ← div_eq_mul_one_div]
        gcongr
  have away_zero {b : ℝ} (hb : 0 < b) :
      Tendsto (fun d => eLpNorm (fun x => dampedLimit d x +
        (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x) 2 (volume.restrict (Set.Ioi b)))
        (𝓝[>] 0) (𝓝 0) := by
    let m := volume.restrict (Set.Ioi b)
    let v := fun x : ℝ => x⁻¹
    have hv : MemLp v 2 m := by
      apply (memLp_two_iff_integrable_sq (by fun_prop : AEStronglyMeasurable v m)).mpr
      have hint := integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hb
      have eqn (x : ℝ) : v x ^ 2 = x ^ (-2:ℝ) := by
        rw [show (-2:ℝ) = ((-2:ℤ):ℝ) by norm_num, Real.rpow_intCast]
        simp [v]
      simp_rw [eqn]
      exact hint
    have estimate (d : ℝ) : eLpNorm (fun x => dampedLimit d x +
        (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x) 2 m ≤
        ‖errorBound b d‖ₑ * eLpNorm v 2 m := by
      rw [← eLpNorm_const_smul]
      apply eLpNorm_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have h := error_le hb (show b < x from hx) d
      change |_| ≤ |errorBound b d * x⁻¹|
      exact h.trans (by simpa [div_eq_mul_inv] using le_abs_self (errorBound b d * x⁻¹))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ (fun _ => bot_le) estimate
    have h := (errorBound_tendsTo b).enorm
    simpa using ENNReal.Tendsto.mul_const h (Or.inr hv.eLpNorm_lt_top.ne)
  exact fun _ hb => away_zero hb

lemma splitNorm (f : ℝ → ℝ) {b : ℝ} (hb : 0 < b) :
    eLpNorm f 2 (volume.restrict (Ioi 0)) ≤ eLpNorm f 2 (volume.restrict (Set.Ioc 0 b)) +
      eLpNorm f 2 (volume.restrict (Ioi b)) := by
  have hdis : Disjoint (Set.Ioc 0 b) (Ioi b) := Set.disjoint_left.mpr fun _ h k => (not_lt_of_ge h.2) k
  rw [← Ioc_union_Ioi_eq_Ioi hb.le, Measure.restrict_union hdis measurableSet_Ioi]
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
    (by norm_num : (2:ℝ≥0∞) ≠ ⊤), lintegral_add_measure]
  apply ENNReal.rpow_add_le_add_rpow <;> norm_num

set_option maxHeartbeats 1200000 in
theorem main : H1 → H2 → OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1_H1_R1.H1 := by
  intro trunc origin rh ε hε
  let F := fun d x : ℝ => (riemannZeta (1 + (d : ℂ)))⁻¹.re / x -
    ∑ a ∈ Finset.Ioc 0 ⌊1/x⌋₊, (moebius a : ℝ) / (a : ℝ) ^ d * (⌊1 / ((a:ℝ)*x)⌋ : ℝ)
  let χ := (Set.Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ))
  let m := volume.restrict (Ioi (0:ℝ))
  let η := ε/3
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨b,hb,small⟩ := origin rh η hη
  have away := (awayFromZero b hb).eventually_lt_const (ENNReal.ofReal_pos.mpr hη)
  obtain ⟨d, hd, hnear, hfar⟩ := ((trunc rh).and (small.and away)).exists
  obtain ⟨n,hn⟩ := hd η hη
  let S := fun x : ℝ => ∑ i : Fin n, ((moebius (i.val+1) : ℝ) / ((i.val:ℝ)+1)^d) * fractScalarInv (1/((i.val:ℝ)+1)) x
  have center : eLpNorm (fun x => F d x + χ x) 2 m < ENNReal.ofReal η + ENNReal.ofReal η :=
    (splitNorm _ hb).trans_lt (ENNReal.add_lt_add hnear hfar)
  have hFm : Measurable (F d) := by
    let g := fun (p : ℝ × ℕ) => ∑ a ∈ Finset.Ioc 0 p.2,
      (moebius a : ℝ) / (a:ℝ)^d * (⌊1 / ((a:ℝ)*p.1)⌋ : ℝ)
    have hg : Measurable g := measurable_from_prod_countable_left fun j => by dsimp [g]; fun_prop
    apply Measurable.sub (f := fun x : ℝ => (riemannZeta (1+(d:ℂ)))⁻¹.re / x) (g := fun x : ℝ => g (x,⌊1/x⌋₊)) (by fun_prop)
    exact hg.comp (measurable_id.prodMk (by fun_prop : Measurable (fun x : ℝ => ⌊1/x⌋₊)))
  have hSm : AEStronglyMeasurable S m := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro i _
    exact (aEStronglyMeasurable_fractScalarInv _).restrict.const_mul _
  have hχ : Measurable χ := measurable_const.indicator measurableSet_Ioc
  have tri := eLpNorm_add_le (p := (2:ℝ≥0∞))
      (hSm.sub hFm.aestronglyMeasurable) (hFm.aestronglyMeasurable.add hχ.aestronglyMeasurable) (by norm_num)
  refine ⟨n,fun i => -((moebius (i.val+1) : ℝ) / ((i.val:ℝ)+1)^d),?_⟩
  have eqn : (fun x => χ x - ∑ i : Fin n, -((moebius (i.val+1) : ℝ) / ((i.val:ℝ)+1)^d) *
      fractScalarInv (1/((i.val:ℝ)+1)) x) =
      (fun x => S x - F d x) + (fun x => F d x + χ x) := by
    ext x
    simp [S,Finset.sum_neg_distrib]; ring
  change eLpNorm _ 2 m < _
  rw [eqn]
  apply tri.trans_lt
  calc
    _ < ENNReal.ofReal η + (ENNReal.ofReal η + ENNReal.ofReal η) := ENNReal.add_lt_add hn center
    _ = _ := by rw [← ENNReal.ofReal_add hη.le hη.le, ← ENNReal.ofReal_add hη.le (by positivity)]; congr 1; dsimp [η]; ring

end OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1_H1_R1_H1_R1
