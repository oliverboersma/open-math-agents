import FormalConjectures.Arxiv.«2303.01089».FurstenbergTimesPTimesQ
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.Fourier.AddCircle

/-!
A counterexample to weak convergence under tripling of an atomless doubling-invariant measure.
The Baire-category argument specializes Badea and Grivaux (arXiv:2303.01089). Long odd orbit
lengths are obtained by adding a small rational displacement to an existing periodic point.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal Classical
open Arxiv.id2303_01089

namespace FurstenbergWitness

noncomputable section

private abbrev T := UnitAddCircle

private def M (d : ℕ) : ℕ := 2 ^ d - 1

private lemma M_pos {d : ℕ} (hd : 0 < d) : 0 < M d := by
  change 0 < 2^d - 1
  have : 1 < (2:ℕ)^d := one_lt_pow₀ (by decide) (by omega)
  omega

private lemma M_add (d : ℕ) : M d + 1 = 2^d := by
  have ht : 0 < (2:ℕ)^d := by positivity
  exact Nat.sub_add_cancel ht

private def step (i : ℕ) (x : T) : T := (2^i : ℕ) • x

private lemma step_add (a b : ℕ) (x : T) : step (a+b) x = step a (step b x) := by
  unfold step
  rw [pow_add, Nat.mul_comm (2^a), mul_nsmul]

private lemma is_period_iff (d : ℕ) (x : T) : step d x = x ↔ M d • x = 0 := by
  unfold step
  rw [← M_add d, add_nsmul, one_nsmul, add_eq_right]

private lemma repeated_period {x : T} {k : ℕ} (hk : step k x = x) (j : ℕ) :
    step (k*j) x = x := by
  induction j with
  | zero => simp [step]
  | succ j ih => rw [Nat.mul_succ, step_add, hk, ih]

private def interp (m : ℕ) : T := ((1 / (m : ℝ) : ℝ) : T)

private lemma interp_torsion {m : ℕ} (hm : 0 < m) (a : ℕ) :
    a • interp m = 0 ↔ m ∣ a := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  unfold interp
  rw [← AddCircle.coe_nsmul (1:ℝ), AddCircle.coe_eq_zero_iff]
  simp only [nsmul_eq_mul, zsmul_eq_mul, mul_one]
  constructor
  · rintro ⟨t,ht⟩
    have hv : (a : ℝ) = (m : ℝ)*(t : ℝ) := by
      field_simp at ht
      linarith
    have hi : (m : ℤ) ∣ (a : ℤ) := ⟨t, by exact_mod_cast hv⟩
    exact_mod_cast hi
  · rintro ⟨b,rfl⟩
    refine ⟨(b:ℤ), ?_⟩
    push_cast
    field_simp

private def empiricalMeasure (d : ℕ) (x : T) : Measure T :=
  (d : ℝ≥0∞)⁻¹ • ∑ i ∈ range d, Measure.dirac (step i x)

private def empirical (d : ℕ) (hd : 0 < d) (x : T) : ProbabilityMeasure T :=
  ⟨empiricalMeasure d x, ⟨by
    have hne : (d : ℝ≥0∞) ≠ 0 := by positivity
    simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), sum_const, card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hne (by simp)⟩⟩

private lemma empirical_apply {d : ℕ} {hd : 0 < d} {x : T}
    {s : Set T} (hs : MeasurableSet s) :
    ((empirical d hd x : ProbabilityMeasure T) : Measure T) s =
      (d : ℝ≥0∞)⁻¹ * (((range d).filter (fun i => step i x ∈ s)).card : ℝ≥0∞) := by
  classical
  change empiricalMeasure d x s = _
  simp only [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply' _ hs, smul_eq_mul, card_eq_sum_ones, Nat.cast_sum, sum_filter,
    Set.indicator_apply, Pi.one_apply, apply_ite, Nat.cast_one, Nat.cast_zero]

private lemma empirical_integral {d : ℕ} {hd : 0 < d} {x : T} {f : T → ℝ}
    (_hf : Continuous f) :
    (∫ z, f z ∂(empirical d hd x : Measure T)) =
      (∑ i ∈ range d, f (step i x)) / d := by
  change (∫ z, f z ∂empiricalMeasure d x) = _
  unfold empiricalMeasure
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [integral_dirac, div_eq_mul_inv, mul_comm]
  · exact fun i _ => integrable_dirac (by finiteness)

private def PM (a : ℕ) (μ : ProbabilityMeasure T) : ProbabilityMeasure T :=
  μ.map (Tn_continuous a).measurable.aemeasurable

private lemma PM_cont (a : ℕ) : Continuous (PM a) :=
  ProbabilityMeasure.continuous_map (Tn_continuous a)

private lemma PM_empirical {a d : ℕ} {hd : 0 < d} {x : T}
    (h : Tn a x = x) : PM a (empirical d hd x) = empirical d hd x := by
  apply ProbabilityMeasure.toMeasure_injective
  change (empiricalMeasure d x).map (Tn a) = empiricalMeasure d x
  unfold empiricalMeasure
  rw [Measure.map_smul, Measure.map_finset_sum (Tn_continuous a).measurable.aemeasurable]
  simp_rw [Measure.map_dirac' (Tn_continuous a).measurable]
  congr 1
  apply sum_congr rfl
  intro i _
  congr 1
  unfold step Tn at *
  rw [← mul_nsmul, mul_comm, mul_nsmul, h]

private lemma PM_doubling {d : ℕ} {hd : 0 < d} {x : T}
    (h : step d x = x) : PM 2 (empirical d hd x) = empirical d hd x := by
  apply ProbabilityMeasure.toMeasure_injective
  change (empiricalMeasure d x).map (Tn 2) = empiricalMeasure d x
  unfold empiricalMeasure
  rw [Measure.map_smul, Measure.map_finset_sum (Tn_continuous 2).measurable.aemeasurable]
  simp_rw [Measure.map_dirac' (Tn_continuous 2).measurable]
  have he (i : ℕ) : Tn 2 (step i x) = step (i+1) x := by
    rw [Nat.add_comm, step_add]
    rfl
  simp only [he]
  congr 1
  obtain ⟨j,rfl⟩ : ∃ j, d = j+1 := ⟨d-1,by omega⟩
  rw [sum_range_succ, sum_range_succ']
  rw [h]
  simp [step, add_comm]


private lemma odd_coprime {d : ℕ} (hd : Odd d) : (3:ℕ).Coprime (M d) := by
  apply (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
  intro hdvd
  obtain ⟨k,rfl⟩ := hd
  have h4 : 4 ≡ 1 [MOD 3] := by decide
  have he : (2:ℕ)^(2*k+1) ≡ 2 [MOD 3] := by
    simpa [pow_add, pow_mul] using (h4.pow k).mul_right 2
  have hz := Nat.mod_eq_zero_of_dvd hdvd
  have ht := congrArg (fun a : ℕ => a % 3) (M_add (2*k+1))
  simp [Nat.add_mod, hz] at ht
  have he' : (2:ℕ)^(2*k+1) % 3 = 2 := he
  omega

private lemma recurrent {d : ℕ} {hd : 0 < d} {x : T} (hodd : Odd d)
    (hx : step d x = x) (N : ℕ) : ∃ j ≥ N, PM (3^j) (empirical d hd x) = empirical d hd x := by
  let j := (M d).totient * (N+1)
  have hj : N ≤ j := by
    have hpos := Nat.totient_pos.mpr (M_pos hd)
    dsimp [j]
    nlinarith
  refine ⟨j, hj, PM_empirical ?_⟩
  have hmod : (3:ℕ)^j ≡ 1 [MOD M d] := by
    simpa [j, pow_mul] using (Nat.ModEq.pow_totient (odd_coprime hodd)).pow (N+1)
  have hpos : 0 < (3:ℕ)^j := by positivity
  obtain ⟨l,hl⟩ := (Nat.modEq_iff_dvd' (show 1 ≤ (3:ℕ)^j by omega)).mp hmod.symm
  have hj' : (3:ℕ)^j = M d * l + 1 := by omega
  change (3^j : ℕ) • x = x
  rw [hj', add_nsmul, one_nsmul, mul_nsmul,
    (is_period_iff d x).mp hx, nsmul_zero, zero_add]

private def spread (k j : ℕ) := k * (2*j+1)

private lemma spread_pos {k : ℕ} (hk : 0 < k) (j : ℕ) : 0 < spread k j :=
  Nat.mul_pos hk (by omega)

private lemma spread_odd {k : ℕ} (hk : Odd k) (j : ℕ) : Odd (spread k j) :=
  hk.mul ⟨j, rfl⟩

private lemma spread_tendsto {k : ℕ} (hk : 0 < k) : Tendsto (spread k) atTop atTop := by
  refine tendsto_atTop_mono (fun j => ?_) tendsto_id
  change j ≤ k * (2*j+1)
  nlinarith

private def perturbed (k j : ℕ) (x : T) := x + interp (M (spread k j))

private lemma perturbed_period {k : ℕ} (hk : 0 < k) {x : T} (hx : step k x = x) (j : ℕ) :
    step (spread k j) (perturbed k j x) = perturbed k j x := by
  apply (is_period_iff _ _).mpr
  unfold perturbed
  have hh : M (spread k j) • x = 0 := (is_period_iff _ _).mp (repeated_period hx _)
  rw [nsmul_add, hh]
  rw [(interp_torsion (M_pos (spread_pos hk j)) _).mpr dvd_rfl, add_zero]

private lemma perturbed_init_inj {k : ℕ} (hk : 0 < k) {x : T} (hx : step k x = x) (j : ℕ) :
    Set.InjOn (fun i => step i (perturbed k j x)) (Set.Iio (spread k j-k)) := by
  let y := perturbed k j x
  have hne (a b : ℕ) (hab : a < b) (hb : b < spread k j-k) :
      step a y ≠ step b y := by
    intro heq
    have hpow : (2:ℕ)^a < 2^b := pow_lt_pow_right₀ (by decide) hab
    let e : ℕ := 2^b-2^a
    have hadd : e + 2^a = 2^b := Nat.sub_add_cancel hpow.le
    have he : e • y + step a y = step b y := by
      change e • y + (2^a : ℕ) • y = (2^b : ℕ) • y
      rw [← add_nsmul, hadd]
    have hzero : e • y = 0 := add_eq_right.mp (he.trans heq.symm)
    have hprod : (e * M k) • y = 0 := by
      rw [mul_nsmul, hzero, nsmul_zero]
    have hz : (e * M k) • interp (M (spread k j)) = 0 := by
      rw [Nat.mul_comm e, mul_nsmul] at hprod ⊢
      change e • (M k • (x + interp (M (spread k j)))) = 0 at hprod
      rw [nsmul_add, (is_period_iff _ _).mp hx, zero_add] at hprod
      exact hprod
    have hdvd := (interp_torsion (M_pos (spread_pos hk j)) _).mp hz
    have hpositive : 0 < e * M k := Nat.mul_pos (Nat.sub_pos_of_lt hpow) (M_pos hk)
    have hle := Nat.le_of_dvd hpositive hdvd
    have hmul : e * M k < (2:ℕ)^(b+k) := by
      rw [pow_add]
      calc
        _ ≤ (2:ℕ)^b * M k := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
        _ < _ := Nat.mul_lt_mul_of_pos_left (by have := M_add k; omega) (by positivity)
    have hlast : (2:ℕ)^(b+k) < 2^(spread k j) := pow_lt_pow_right₀ (by decide) (by omega)
    have := M_add (spread k j)
    omega
  intro i hi l hl heq
  rcases lt_trichotomy i l with h | h | h
  · exact False.elim (hne i l h hl heq)
  · exact h
  · exact False.elim (hne l i h hi heq.symm)

private lemma period_sum {k : ℕ} {x : T} (hx : step k x = x) (f : T → ℝ) (l : ℕ) :
    (∑ i ∈ range (k*l), f (step i x)) = (l:ℝ) * (∑ i ∈ range k, f (step i x)) := by
  induction l with
  | zero => simp
  | succ l ih =>
      rw [Nat.mul_succ, sum_range_add, ih]
      have he (i : ℕ) : step (k*l+i) x = step i x := by
        rw [Nat.add_comm, step_add, repeated_period hx l]
      simp only [he, Nat.cast_succ]
      ring

private lemma close_steps {k : ℕ} (hk : 0 < k) (j i K : ℕ) (hi : i+K ≤ spread k j)
    (x : T) : dist (step i (perturbed k j x)) (step i x) ≤ 2 / (2:ℝ)^K := by
  have hm : 0 < M (spread k j) := M_pos (spread_pos hk j)
  have hmR : (0:ℝ) < M (spread k j) := by exact_mod_cast hm
  have hm' : (2:ℝ)^(spread k j) ≤ 2 * (M (spread k j) : ℝ) := by
    have hh : (M (spread k j) : ℝ) + 1 = (2:ℝ)^(spread k j) := by
      exact_mod_cast M_add (spread k j)
    have h := (show (1:ℝ) ≤ M (spread k j) from by exact_mod_cast hm)
    linarith
  have hp : (2:ℝ)^i * (2:ℝ)^K ≤ (2:ℝ)^(spread k j) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hi
  rw [dist_eq_norm]
  change ‖(2^i : ℕ) • (x + interp (M (spread k j))) - (2^i : ℕ) • x‖ ≤ _
  rw [nsmul_add, add_sub_cancel_left, interp, ← AddCircle.coe_nsmul (1:ℝ)]
  refine QuotientAddGroup.norm_mk_le_norm.trans ?_
  rw [nsmul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), Nat.cast_pow, Nat.cast_ofNat]
  rw [one_div, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hmR (by positivity)).2
  exact hp.trans hm'

private lemma perturbed_tendsto {k : ℕ} (hk : 0 < k) {x : T} (hx : step k x = x) :
    Tendsto (fun j => empirical (spread k j) (spread_pos hk j) (perturbed k j x))
      atTop (𝓝 (empirical k hk x)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  simp_rw [empirical_integral f.continuous]
  have he (j : ℕ) :
      (∑ i ∈ range (spread k j), f (step i x)) / (spread k j : ℝ) =
      (∑ i ∈ range k, f (step i x)) / (k : ℝ) := by
    rw [spread, period_sum hx, Nat.cast_mul]
    field_simp
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ,hδ,hnear⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (η/2) (by positivity)
  obtain ⟨K,hK⟩ : ∃ K : ℕ, 2 / δ < (2:ℝ)^K :=
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).eventually
      (eventually_gt_atTop (2/δ))).exists
  have hK' : 2 / (2:ℝ)^K < δ := by
    have h := (div_lt_iff₀ hδ).mp hK
    exact (div_lt_iff₀ (by positivity)).mpr (by linarith)
  let C : ℝ := ‖f‖
  have hC : 0 ≤ C := norm_nonneg f
  have hN (z : T) : |f z| ≤ C := by
    rw [← Real.norm_eq_abs]
    exact BoundedContinuousFunction.norm_coe_le_norm f z
  have ht : Tendsto (fun j => (spread k j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (spread_tendsto hk)
  filter_upwards [(spread_tendsto hk).eventually (eventually_ge_atTop K),
    ht.eventually (eventually_gt_atTop ((2*C*K)/(η/2)))] with j hj hsize
  let d := spread k j
  have hdR : (0:ℝ) < d := by exact_mod_cast spread_pos hk j
  rw [← he j, Real.dist_eq, ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hdR]
  let g (i : ℕ) := f (step i (perturbed k j x)) - f (step i x)
  change |∑ i ∈ range d, g i| / (d:ℝ) < η
  have hsmall (i : ℕ) (hi : i ∈ range (d-K)) : |g i| ≤ η/2 := by
    have hdist := close_steps hk j i K (by have := mem_range.mp hi; dsimp [d] at this; omega) x
    simpa [g, Real.dist_eq] using (hnear (hdist.trans_lt hK')).le
  have hbig (i : ℕ) : |g i| ≤ 2*C := by
    simpa [two_mul] using (abs_sub _ _).trans (add_le_add (hN _) (hN _))
  have hsplit : d-K+K=d := Nat.sub_add_cancel hj
  rw [← hsplit, sum_range_add]
  rw [hsplit]
  apply (div_lt_iff₀ hdR).mpr
  have ha : |∑ i ∈ range (d-K), g i| ≤ (d-K:ℕ) * (η/2) := by
    rw [← Real.norm_eq_abs]
    simpa using ((norm_sum_le (range (d-K)) g).trans (sum_le_sum
      (fun i hi => by simpa [Real.norm_eq_abs] using hsmall i hi)) :
      ‖∑ i ∈ range (d-K), g i‖ ≤ ∑ _i ∈ range (d-K), η/2)
  have hb : |∑ i ∈ range K, g (d-K+i)| ≤ K * (2*C) := by
    rw [← Real.norm_eq_abs]
    simpa using ((norm_sum_le (range K) (fun i => g (d-K+i))).trans (sum_le_sum
      (fun i _ => by simpa [Real.norm_eq_abs] using hbig (d-K+i))) :
      ‖∑ i ∈ range K, g (d-K+i)‖ ≤ ∑ _i ∈ range K, 2*C)
  have hsub : ((d-K:ℕ):ℝ) ≤ d := by exact_mod_cast Nat.sub_le d K
  have hbound := mul_le_mul_of_nonneg_right hsub (show 0 ≤ η/2 by positivity)
  have ht' := (div_lt_iff₀ (show 0 < η/2 by positivity)).mp (show _ < (d:ℝ) from hsize)
  linarith [(abs_add_le _ _).trans (add_le_add ha hb)]

private def SmallBalls (ε : ℝ≥0∞) (μ : ProbabilityMeasure T) : Prop :=
  ∃ F : Finset T, ∃ r : T → ℝ, (∀ x : T, ∃ a ∈ F, x ∈ Metric.ball a (r a)) ∧
    ∀ a ∈ F, (μ : Measure T) (Metric.closedBall a (r a)) < ε

private lemma smallBalls_open (ε : ℝ≥0∞) : IsOpen {μ : ProbabilityMeasure T | SmallBalls ε μ} := by
  rw [isOpen_iff_mem_nhds]
  rintro μ ⟨F,r,hF,hsmall⟩
  have he (a) (ha : a ∈ F) :
      ∀ᶠ ν : ProbabilityMeasure T in 𝓝 μ, (ν : Measure T) (Metric.closedBall a (r a)) < ε :=
    eventually_lt_of_limsup_lt
      ((ProbabilityMeasure.limsup_measure_closed_le_of_tendsto tendsto_id
        Metric.isClosed_closedBall).trans_lt (hsmall a ha))
  exact ((eventually_all_finset F).2 he).mono (fun ν hν => ⟨F,r,hF,hν⟩)

private lemma balls_for_empirical {d k : ℕ} (hd : 0 < d) (hkd : k ≤ d) (x : T)
    (hinj : Set.InjOn (fun i => step i x) (Set.Iio (d-k)))
    {ε : ℝ≥0∞} (he : (d:ℝ≥0∞)⁻¹ * ((k+1:ℕ):ℝ≥0∞) < ε) :
    SmallBalls ε (empirical d hd x) := by
  classical
  let S : Finset T := (range d).image (fun i => step i x)
  have hsep (u : T) : ∃ r>0, ∀ v ∈ S, v ∈ Metric.closedBall u r → v = u := by
    let V : Set T := ((S : Set T) \ {u})ᶜ
    have hu : u ∈ V := by simp [V]
    have ho : IsOpen V := ((S.finite_toSet).sdiff).isClosed.isOpen_compl
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp ho u hu
    refine ⟨r/2,by positivity,fun v hvs hv => ?_⟩
    have hvV := hball (Metric.closedBall_subset_ball (by linarith : r/2 < r) hv)
    by_contra hvu
    exact hvV ⟨hvs,hvu⟩
  choose r hr hs using hsep
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover (fun u : T => Metric.ball u (r u))
    (fun _ => Metric.isOpen_ball) (by
      intro u _
      exact Set.mem_iUnion.mpr ⟨u,Metric.mem_ball_self (hr u)⟩)
  refine ⟨F,r,fun u => ?_,fun a _ => ?_⟩
  · simpa using hF (Set.mem_univ u)
  · rw [empirical_apply Metric.isClosed_closedBall.measurableSet]
    apply lt_of_le_of_lt _ he
    gcongr
    let P (i : ℕ) : Prop := step i x ∈ Metric.closedBall a (r a)
    have hone : ((range (d-k)).filter P).card ≤ 1 := by
      apply card_le_one.mpr
      intro i hi j hj
      obtain ⟨hi,hi'⟩ := mem_filter.mp hi
      obtain ⟨hj,hj'⟩ := mem_filter.mp hj
      have hiD : i ∈ range d := mem_range.mpr ((mem_range.mp hi).trans_le (Nat.sub_le _ _))
      have hjD : j ∈ range d := mem_range.mpr ((mem_range.mp hj).trans_le (Nat.sub_le _ _))
      apply hinj (mem_range.mp hi) (mem_range.mp hj)
      exact (hs a _ (mem_image_of_mem _ hiD) hi').trans
        (hs a _ (mem_image_of_mem _ hjD) hj').symm
    have hsub : (range d).filter P ⊆ (range (d-k)).filter P ∪ Ico (d-k) d := by
      intro i hi
      obtain ⟨hi,hi'⟩ := mem_filter.mp hi
      by_cases hh : i < d-k
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr hh,hi'⟩)
      · exact mem_union_right _ (mem_Ico.mpr ⟨le_of_not_gt hh,mem_range.mp hi⟩)
    have hh := (card_le_card hsub).trans (card_union_le _ _)
    rw [Nat.card_Ico] at hh
    change ((range d).filter P).card ≤ k+1
    omega

private def generators : Set (ProbabilityMeasure T) :=
  {μ | ∃ (d : ℕ) (hd : 0 < d) (x : T), Odd d ∧ step d x = x ∧ μ = empirical d hd x}

private abbrev State := ↥(closure generators)

private lemma dense_from_generators {P : Set (ProbabilityMeasure T)}
    (h : generators ⊆ closure (generators ∩ P)) :
    Dense (Subtype.val ⁻¹' P : Set State) := by
  intro x
  rw [closure_subtype]
  apply (closure_mono ?_) ((closure_minimal h isClosed_closure) x.property)
  intro μ hμ
  exact ⟨⟨μ, subset_closure hμ.1⟩,hμ.2,rfl⟩

private lemma smallBalls_dense (ε : ℝ≥0∞) (he : 0 < ε) :
    Dense (Subtype.val ⁻¹' {μ | SmallBalls ε μ} : Set State) := by
  apply dense_from_generators
  rintro μ ⟨k,hk,x,ho,hx,rfl⟩
  apply mem_closure_of_tendsto (perturbed_tendsto hk hx)
  have hquot : ∀ᶠ j : ℕ in atTop, (spread k j : ℝ≥0∞)⁻¹ * ((k+1:ℕ):ℝ≥0∞) < ε := by
    have ht : Tendsto (fun j => (spread k j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (spread_tendsto hk)
    by_cases ht' : ε = ⊤
    · exact Eventually.of_forall (fun j => by
        rw [ht']
        exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (by exact_mod_cast spread_pos hk j)) (by simp))
    have hpos : 0 < ε.toReal := ENNReal.toReal_pos he.ne' ht'
    filter_upwards [ht.eventually (eventually_gt_atTop ((k+1:ℕ)/ε.toReal))] with j hj
    have hj0 : (0:ℝ) < spread k j := by exact_mod_cast spread_pos hk j
    apply (ENNReal.toReal_lt_toReal (by
      exact (ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr
        (by exact_mod_cast spread_pos hk j)) (by simp)).ne) ht').mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_lt_iff₀ hj0).mpr
    have hh := (div_lt_iff₀ hpos).mp hj
    nlinarith
  filter_upwards [hquot] with j hj
  have hp := perturbed_period hk hx j
  constructor
  · exact ⟨spread k j,spread_pos hk j,perturbed k j x,spread_odd ho j,hp,rfl⟩
  · exact balls_for_empirical _ (by dsimp [spread]; nlinarith) _
      (perturbed_init_inj hk hx j) hj

private def evalNorm (μ : ProbabilityMeasure T) : ℝ :=
  ∫ x : T, ‖x‖ ∂(μ : Measure T)

private lemma eval_cont : Continuous evalNorm :=
  ProbabilityMeasure.continuous_integral_continuousMap (⟨_,continuous_norm⟩ : C(T,ℝ))

private def Recur (N : ℕ) (μ : ProbabilityMeasure T) : Prop :=
  ∃ j ≥ N, |evalNorm (PM (3^j) μ)-evalNorm μ| < (1 / ((N:ℝ)+1))

private lemma recur_open (N : ℕ) : IsOpen {μ : ProbabilityMeasure T | Recur N μ} := by
  have he : {μ : ProbabilityMeasure T | Recur N μ} =
      ⋃ j : {j : ℕ // N ≤ j}, {μ | |evalNorm (PM (3^j.val) μ)-evalNorm μ| < 1/((N:ℝ)+1)} := by
    ext μ
    simp [Recur]
  rw [he]
  exact isOpen_iUnion fun j => isOpen_lt ((eval_cont.comp (PM_cont _)).sub eval_cont).abs continuous_const

private lemma recur_dense (N : ℕ) : Dense (Subtype.val ⁻¹' {μ | Recur N μ} : Set State) := by
  apply dense_from_generators
  rintro μ ⟨d,hd,x,ho,hx,rfl⟩
  have hD : empirical d hd x ∈ generators := ⟨d,hd,x,ho,hx,rfl⟩
  obtain ⟨j,hj,h⟩ := recurrent (hd := hd) ho hx N
  exact subset_closure ⟨hD,j,hj,by rw [h, sub_self, abs_zero]; positivity⟩

private lemma independent_two_three : Nat.MultiplicativelyIndependent 2 3 := by
  rintro ⟨q,hq⟩
  change (q:ℝ) = Real.log 2 / Real.log 3 at hq
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hqpos : (0:ℝ) < q := hq ▸ (div_pos (Real.log_pos (by norm_num)) h3)
  have hqpos' : (0:ℚ) < q := by exact_mod_cast hqpos
  have hnum : 0 < q.num := Rat.num_pos.mpr hqpos'
  let a := q.num.toNat
  let b := q.den
  have hb : 0 < b := q.den_pos
  have ha : 0 < a := by dsimp [a]; omega
  have ha' : (a:ℤ) = q.num := Int.toNat_of_nonneg hnum.le
  have haR : (a:ℝ) = (q.num:ℝ) := by exact_mod_cast ha'
  have hab : (q:ℝ) = (a:ℝ)/(b:ℝ) := by rw [Rat.cast_def, haR]
  have he : (b:ℝ) * Real.log 2 = (a:ℝ) * Real.log 3 := by
    rw [hab] at hq
    have h1 := (div_eq_div_iff (show (b:ℝ) ≠ 0 by positivity) h3.ne').mp hq
    linarith
  have hpow : (2:ℕ)^b = 3^a := by
    have hlog : Real.log ((2:ℝ)^b) = Real.log ((3:ℝ)^a) := by
      rw [Real.log_pow, Real.log_pow, he]
    have h := congrArg Real.exp hlog
    rw [Real.exp_log (by positivity), Real.exp_log (by positivity)] at h
    exact_mod_cast h
  have habs : (2:ℕ) ∣ 3^a := hpow ▸ dvd_pow_self _ hb.ne'
  exact (by decide : ¬ (2:ℕ) ∣ 3) (Nat.Prime.dvd_of_dvd_pow Nat.prime_two habs)

private def tau (N : ℕ) : ℝ≥0∞ := (↑(N+1:ℕ) : ℝ≥0∞)⁻¹

private lemma tau_pos (N : ℕ) : 0 < tau N :=
  ENNReal.inv_pos.mpr (by simp)

private lemma atomless_from_small {μ : ProbabilityMeasure T}
    (h : ∀ N, SmallBalls (tau N) μ) :
    Arxiv.id2303_01089.MeasureTheory.IsAtomLess (μ : Measure T) := by
  constructor
  intro A hA ha
  have ha' : 0 < ((μ : Measure T) A).toReal := ENNReal.toReal_pos ha.1.ne' (by finiteness)
  obtain ⟨N,hN⟩ := exists_nat_gt (((μ : Measure T) A).toReal)⁻¹
  have hsmall : tau N < (μ : Measure T) A := by
    apply (ENNReal.toReal_lt_toReal (by
      exact (ENNReal.inv_lt_top.mpr (by positivity : 0 < ((N+1:ℕ) : ℝ≥0∞))).ne) (by finiteness)).mp
    simp only [tau, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [inv_lt_comm₀ (by positivity : 0 < ((N+1:ℕ):ℝ)) ha']
    push_cast
    linarith
  obtain ⟨F,r,hF,hs⟩ := h N
  let U (p : T) := A ∩ Metric.closedBall p (r p)
  have hzero (p : T) (hp : p ∈ F) : (μ : Measure T) (U p) = 0 := by
    apply (ha.2 _ Set.inter_subset_left (hA.inter Metric.isClosed_closedBall.measurableSet)).resolve_right
    have hle := measure_mono (μ := (μ : Measure T))
      (Set.inter_subset_right : U p ⊆ Metric.closedBall p (r p))
    exact ne_of_lt (hle.trans_lt ((hs p hp).trans hsmall))
  have hcover : A ⊆ ⋃ p ∈ F, U p := by
    intro x hx
    obtain ⟨p,hp,hxp⟩ := hF x
    exact Set.mem_iUnion₂.mpr ⟨p,hp,hx,Metric.ball_subset_closedBall hxp⟩
  have hUnion : (μ : Measure T) (⋃ p ∈ F, U p) = 0 :=
    (measure_biUnion_null_iff F.countable_toSet).mpr hzero
  exact ha.1.not_ge ((measure_mono hcover).trans_eq hUnion)

private lemma positive_haar : 0 < evalNorm UnitAddCircle.ProbabilityMeasure := by
  have hz : interp 2 ≠ 0 := by
    intro hh
    have h := (interp_torsion (m := 2) (by decide) 1).mp (by simpa using hh)
    norm_num at h
  change 0 < ∫ x : T, ‖x‖
  exact integral_pos_of_integrable_nonneg_nonzero (x := interp 2)
    continuous_norm (continuous_norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fun _ => norm_nonneg _) (norm_ne_zero_iff.mpr hz)

private lemma threshold_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 1 / ((N:ℝ)+1) < ε := by
  have ht : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n:ℝ) ≤ (n:ℝ)+1)
      tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_gt_atTop (1/ε))] with N hN
  exact (div_lt_iff₀ (by positivity)).mpr (by
    have h := (div_lt_iff₀ hε).mp hN
    linarith)

private lemma witness : ∃ μ : ProbabilityMeasure T,
    Arxiv.id2303_01089.MeasureTheory.IsAtomLess (μ : Measure T) ∧
    MeasurePreserving (Tn 2) μ μ ∧
    ¬ Tendsto (fun n : ℕ => PM (3^n) μ) atTop (𝓝 UnitAddCircle.ProbabilityMeasure) := by
  have hclosed : IsClosed (closure generators) := isClosed_closure
  let _ : CompactSpace State := isCompact_iff_compactSpace.mp hclosed.isCompact
  let U (N : ℕ) : Set State := Subtype.val ⁻¹'
    ({μ : ProbabilityMeasure T | SmallBalls (tau N) μ} ∩ {μ | Recur N μ})
  have hOpen (N) : IsOpen (U N) :=
    ((smallBalls_open (tau N)).inter (recur_open N)).preimage continuous_subtype_val
  have hDense (N) : Dense (U N) :=
    (smallBalls_dense (tau N) (tau_pos N)).inter_of_isOpen_right (recur_dense N)
      ((recur_open N).preimage continuous_subtype_val)
  have hall := dense_iInter_of_isOpen hOpen hDense
  let A : Set State := {μ | evalNorm μ.val < evalNorm UnitAddCircle.ProbabilityMeasure / 2}
  have hAo : IsOpen A := isOpen_lt (eval_cont.comp continuous_subtype_val) continuous_const
  have hAne : A.Nonempty := by
    let μ := empirical 1 (by decide) (0:T)
    have hd : μ ∈ generators := ⟨1,by decide,0,by decide,by simp [step],rfl⟩
    refine ⟨⟨μ,subset_closure hd⟩,?_⟩
    change evalNorm μ < _
    unfold evalNorm
    rw [show (μ : Measure T) = Measure.dirac (0:T) by
      simp [μ,empirical,empiricalMeasure,step]]
    simp only [integral_dirac, norm_zero]
    exact half_pos positive_haar
  obtain ⟨x,hx,hxu⟩ := hall.inter_open_nonempty A hAo hAne
  let μ := x.val
  have hAll (N : ℕ) : SmallBalls (tau N) μ ∧ Recur N μ := Set.mem_iInter.mp hxu N
  have hEq : PM 2 μ = μ := by
    apply (closure_minimal ?_ (isClosed_eq (PM_cont 2) continuous_id)) x.property
    rintro _ ⟨d,hd,z,_,hz,rfl⟩
    exact PM_doubling hz
  refine ⟨μ,atomless_from_small (fun N => (hAll N).1),
    ⟨(Tn_continuous 2).measurable,congrArg ProbabilityMeasure.toMeasure hEq⟩,?_⟩
  intro ht
  let a := evalNorm UnitAddCircle.ProbabilityMeasure
  let b := evalNorm μ
  let ε := (a-b)/4
  have hab : b < a := (show b < a/2 from hx).trans (by linarith [positive_haar])
  have hε : 0 < ε := by dsimp [ε]; linarith
  have htc := (eval_cont.tendsto UnitAddCircle.ProbabilityMeasure).comp ht
  have hnear : ∀ᶠ n : ℕ in atTop, |evalNorm (PM (3^n) μ)-a| < ε := by
    simpa [Real.dist_eq] using Metric.tendsto_nhds.mp htc ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((hnear.and (threshold_small hε)))
  obtain ⟨j,hj,hrec⟩ := (hAll N).2
  have h1 := (hN j hj).1
  have h2 := hrec.trans (hN N le_rfl).2
  have h3 : |a - evalNorm (PM (3^j) μ)| < ε := by rw [abs_sub_comm]; exact h1
  have h4 : a - evalNorm (PM (3^j) μ) < ε := (le_abs_self _).trans_lt h3
  have h5 : evalNorm (PM (3^j) μ) - b < ε := (le_abs_self _).trans_lt h2
  dsimp [ε] at h4 h5
  linarith

end
end FurstenbergWitness

/-- A counterexample from periodic orbit measures and Baire category. -/
theorem OMA.solution : type_of% @Arxiv.id2303_01089.conjecture_1_4 := by
  intro h
  obtain ⟨μ, ha, hp, hnot⟩ := FurstenbergWitness.witness
  exact hnot (h 2 3 (by decide) (by decide) FurstenbergWitness.independent_two_three μ ha hp)