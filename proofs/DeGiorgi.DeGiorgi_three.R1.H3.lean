import OMAReductions.R_DeGiorgi_DeGiorgi_three_R1

/-!
# A weighted Liouville theorem in space

Credit: adapted from the merged proof of DeGiorgi.DeGiorgi_two.R1.H3 by @dk8827 (PR #1322),
the planar weighted Liouville theorem. The pointwise bound on `v q` is replaced by the
quadratic growth of its square integral, which bounds the weighted cutoff energy directly.

Dilates of a single smooth bump have uniformly bounded Dirichlet energy in
dimension two. Testing the weak equation by the solution times the squared
bump first bounds the total weighted energy. The gradient of the bump then
localizes the same estimate to the tail, forcing that energy to vanish.
This is the planar argument of Ghoussoub and Gui (1998).
-/

namespace OMA.SpaceLiouville

open EuclideanGeometry InnerProductSpace MeasureTheory Metric Set Filter
open scoped Gradient

private abbrev Plane := ℝ^3

private theorem gradient_continuous {u : Plane → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (∇ u) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hu.continuous_fderiv one_ne_zero)

private theorem gradient_compact {u : Plane → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (∇ u) := by
  apply hu.mono'
  intro x hx
  apply support_fderiv_subset ℝ
  change fderiv ℝ u x ≠ 0
  intro he
  exact hx (by simp [gradient, he])

private theorem norm_gradient {u : Plane → ℝ} (x : Plane) :
    ‖∇ u x‖ = ‖fderiv ℝ u x‖ :=
  (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

private noncomputable def baseBump : ContDiffBump (0 : Plane) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private noncomputable def cutoff (r : ℝ) (x : Plane) : ℝ := baseBump (r⁻¹ • x)

private theorem cutoff_smooth (r : ℝ) : ContDiff ℝ 1 (cutoff r) := by
  have h : ContDiff ℝ 1 (fun x : Plane => r⁻¹ • x) := contDiff_id.const_smul _
  exact baseBump.contDiff.comp h

private theorem cutoff_compact {r : ℝ} (hr : 0 < r) : HasCompactSupport (cutoff r) :=
  baseBump.hasCompactSupport.comp_smul (inv_ne_zero hr.ne')

private theorem cutoff_bounds (r : ℝ) (x : Plane) : 0 ≤ cutoff r x ∧ cutoff r x ≤ 1 :=
  ⟨baseBump.nonneg, baseBump.le_one⟩

private theorem cutoff_one {r : ℝ} (hr : 0 < r) {x : Plane}
    (hx : x ∈ closedBall (0 : Plane) r) : cutoff r x = 1 := by
  apply baseBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    inv_mul_eq_div, div_le_iff₀ hr, show baseBump.rIn = 1 from rfl, one_mul]
  exact mem_closedBall_zero_iff.mp hx

private theorem cutoff_zero {r : ℝ} (hr : 0 < r) {x : Plane}
    (hx : x ∉ closedBall (0 : Plane) (2 * r)) : cutoff r x = 0 := by
  apply baseBump.zero_of_le_dist
  change 2 ≤ dist (r⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    inv_mul_eq_div, le_div_iff₀ hr]
  exact le_of_lt (lt_of_not_ge (fun he => hx (mem_closedBall_zero_iff.mpr he)))

private theorem gradient_zero_of_cutoff_zero {r : ℝ} {x : Plane} (h : cutoff r x = 0) :
    ∇ (cutoff r) x = 0 := by
  have hmin : IsLocalMin (cutoff r) x :=
    Eventually.of_forall fun y => by rw [h]; exact (cutoff_bounds r y).1
  simp [gradient, hmin.fderiv_eq_zero]

private theorem gradient_zero_of_cutoff_one {r : ℝ} {x : Plane} (h : cutoff r x = 1) :
    ∇ (cutoff r) x = 0 := by
  have hmax : IsLocalMax (cutoff r) x :=
    Eventually.of_forall fun y => by rw [h]; exact (cutoff_bounds r y).2
  simp [gradient, hmax.fderiv_eq_zero]

private theorem cutoff_fderiv (r : ℝ) (x : Plane) :
    fderiv ℝ (cutoff r) x =
      (fderiv ℝ (fun y : Plane => baseBump y) (r⁻¹ • x)).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ Plane) := by
  let L : Plane →L[ℝ] Plane := r⁻¹ • ContinuousLinearMap.id ℝ Plane
  have hdiff : Differentiable ℝ (fun y : Plane => baseBump y) :=
    (baseBump.contDiff (n := 1)).differentiable (by norm_num)
  exact ((hdiff (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv

private theorem cutoff_gradient_norm {r : ℝ} (hr : 0 < r) (M : ℝ)
    (hM : ∀ x : Plane, ‖fderiv ℝ (fun y : Plane => baseBump y) x‖ ≤ M)
    (x : Plane) : ‖∇ (cutoff r) x‖ ≤ M / r := by
  rw [norm_gradient, cutoff_fderiv]
  apply ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, ContinuousLinearMap.norm_id, mul_one,
    div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hM _) (inv_nonneg.mpr hr.le)

private theorem compact_gradient_square {u : Plane → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (fun x => ‖∇ u x‖ ^ 2) := by
  apply (gradient_compact hu).mono'
  intro x hx
  apply subset_closure
  change ∇ u x ≠ 0
  intro he
  exact hx (by simp [he])

private theorem cutoff_weighted_bound (f : Plane → ℝ) (hf : Continuous f) (C₀ : ℝ)
    (hgrow : ∀ R : ℝ, 1 ≤ R → (∫ x in ball (0 : Plane) R, (f x) ^ 2) ≤ C₀ * R ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → (∫ x, (f x) ^ 2 * ‖∇ (cutoff r) x‖ ^ 2) ≤ K := by
  obtain ⟨M, hM⟩ := (baseBump.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((baseBump.contDiff (n := 1)).continuous_fderiv one_ne_zero)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hC0 : 0 ≤ C₀ := by
    have h := hgrow 1 le_rfl
    have h0 : 0 ≤ ∫ x in ball (0 : Plane) 1, (f x) ^ 2 :=
      setIntegral_nonneg measurableSet_ball (fun x _ => sq_nonneg _)
    nlinarith
  refine ⟨9 * C₀ * M ^ 2, by positivity, ?_⟩
  intro r hr
  have hr0 : 0 < r := by linarith
  have hcompact : HasCompactSupport (fun x => (f x) ^ 2 * ‖∇ (cutoff r) x‖ ^ 2) :=
    (compact_gradient_square (cutoff_compact hr0)).mul_left
  have hcont : Continuous (fun x => (f x) ^ 2 * ‖∇ (cutoff r) x‖ ^ 2) :=
    (hf.pow 2).mul ((gradient_continuous (cutoff_smooth r)).norm.pow 2)
  have hInt := hcont.integrable_of_hasCompactSupport (μ := volume) hcompact
  have hfi : IntegrableOn (fun x => (f x) ^ 2) (ball (0 : Plane) (3 * r)) :=
    ((hf.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) (3 * r))).mono_set
      ball_subset_closedBall
  calc
    _ = ∫ x in ball (0 : Plane) (3 * r), (f x) ^ 2 * ‖∇ (cutoff r) x‖ ^ 2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hx' : x ∉ closedBall (0 : Plane) (2 * r) := by
        intro h
        apply hx
        rw [mem_ball_zero_iff]
        rw [mem_closedBall_zero_iff] at h
        linarith
      rw [gradient_zero_of_cutoff_zero (cutoff_zero hr0 hx')]
      simp
    _ ≤ ∫ x in ball (0 : Plane) (3 * r), (f x) ^ 2 * (M / r) ^ 2 := by
      apply setIntegral_mono_on hInt.integrableOn (hfi.mul_const _) measurableSet_ball
      intro x _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (cutoff_gradient_norm hr0 M hM x) 2) (sq_nonneg _)
    _ = (∫ x in ball (0 : Plane) (3 * r), (f x) ^ 2) * (M / r) ^ 2 := integral_mul_const _ _
    _ ≤ (C₀ * (3 * r) ^ 2) * (M / r) ^ 2 :=
      mul_le_mul_of_nonneg_right (hgrow _ (by linarith)) (sq_nonneg _)
    _ = 9 * C₀ * M ^ 2 := by field_simp; ring

end OMA.SpaceLiouville

namespace OMA.SpaceLiouville

open EuclideanGeometry InnerProductSpace MeasureTheory Filter Set Metric
open scoped Gradient

private noncomputable def energy (v q : Plane → ℝ) (x : Plane) : ℝ :=
  (v x) ^ 2 * ‖∇ q x‖ ^ 2

private theorem energy_continuous {v q : Plane → ℝ}
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) : Continuous (energy v q) :=
  (hv.continuous.pow 2).mul ((gradient_continuous hq).norm.pow 2)

private theorem energy_nonneg (v q : Plane → ℝ) (x : Plane) : 0 ≤ energy v q x := by
  unfold energy
  positivity

private theorem energy_cutoff_integrable {v q η : Plane → ℝ}
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) (hη : ContDiff ℝ 1 η)
    (hs : HasCompactSupport η) : Integrable (fun x => (η x) ^ 2 * energy v q x) := by
  have hx : HasCompactSupport (fun x => (η x) ^ 2 * energy v q x) := by
    apply hs.mono'
    intro x h
    apply subset_closure
    change η x ≠ 0
    intro he
    exact h (by simp [he])
  exact ((hη.continuous.pow 2).mul (energy_continuous hv hq)).integrable_of_hasCompactSupport hx

private theorem young {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    2 * a * b ≤ δ * a ^ 2 + b ^ 2 / δ := by
  apply sub_nonneg.mp
  have he : δ * a ^ 2 + b ^ 2 / δ - 2 * a * b = (δ * a - b) ^ 2 / δ := by
    field_simp [hδ.ne']
    ring
  rw [he]
  exact div_nonneg (sq_nonneg _) hδ.le

private theorem test_gradient {q η : Plane → ℝ} (hq : ContDiff ℝ 1 q)
    (hη : ContDiff ℝ 1 η) (x : Plane) :
    ∇ (fun y => q y * (η y) ^ 2) x =
      (η x) ^ 2 • ∇ q x + (2 * q x * η x) • ∇ η x := by
  have hqd := (hq.differentiable one_ne_zero x)
  have hηd := (hη.differentiable one_ne_zero x)
  have hm := fderiv_fun_mul (c := q) (d := fun y => (η y) ^ 2) hqd (hηd.pow 2)
  have hp := fderiv_fun_pow 2 hηd
  unfold gradient
  rw [hm, hp]
  simp only [map_add, map_smul, show 2 - (1 : ℕ) = 1 by decide, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat, smul_smul]
  rw [add_comm]
  congr 1
  congr 1
  ring

private theorem weak_energy_estimate (v q η A : Plane → ℝ) (δ : ℝ)
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) (hvpos : ∀ x, 0 < v x)
    (hη0 : ∀ x, 0 ≤ η x) (hδ : 0 < δ)
    (hweak : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, (v x) ^ 2 * inner ℝ (∇ q x) (∇ ψ x)) = 0)
    (hAi : Integrable A) (hA0 : ∀ x, 0 ≤ A x)
    (hA : ∀ x, ∇ η x ≠ 0 → (η x) ^ 2 * energy v q x ≤ A x) :
    (∫ x, (η x) ^ 2 * energy v q x) ≤
      δ * (∫ x, A x) + (1 / δ) * (∫ x, (v x * q x) ^ 2 * ‖∇ η x‖ ^ 2) := by
  let ψ := fun x => q x * (η x) ^ 2
  have hψ : ContDiff ℝ 1 ψ := hq.mul (hη.pow 2)
  have hψc : HasCompactSupport ψ := by
    apply hηc.mono'
    intro x hx
    apply subset_closure
    change η x ≠ 0
    intro he
    exact hx (by simp [ψ, he])
  let F := fun x => (v x) ^ 2 * inner ℝ (∇ q x) (∇ ψ x)
  have hFc : HasCompactSupport F := by
    apply (gradient_compact hψc).mono'
    intro x hx
    apply subset_closure
    change ∇ ψ x ≠ 0
    intro he
    apply hx
    change (v x) ^ 2 * inner ℝ (∇ q x) (∇ ψ x) = 0
    rw [he, inner_zero_right, mul_zero]
  have hFi : Integrable F :=
    ((hv.continuous.pow 2).mul
      ((gradient_continuous hq).inner (gradient_continuous hψ))).integrable_of_hasCompactSupport hFc
  have hFzero : (∫ x, F x) = 0 := hweak ψ hψ hψc
  have hGi : Integrable (fun x => (v x * q x) ^ 2 * ‖∇ η x‖ ^ 2) :=
    (((hv.continuous.mul hq.continuous).pow 2).mul
      ((gradient_continuous hη).norm.pow 2)).integrable_of_hasCompactSupport
      (compact_gradient_square hηc).mul_left
  have hCross (x : Plane) :
      F x = (η x) ^ 2 * energy v q x +
        2 * (η x) * (v x) ^ 2 * (q x) * inner ℝ (∇ q x) (∇ η x) := by
    simp only [F, ψ, test_gradient hq hη, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, energy]
    ring
  have hpoint (x : Plane) :
      (η x) ^ 2 * energy v q x ≤ F x + δ * A x + (1 / δ) * ((v x * q x) ^ 2 * ‖∇ η x‖ ^ 2) := by
    rw [hCross]
    by_cases hz : ∇ η x = 0
    · simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), inner_zero_right, mul_zero,
        add_zero]
      exact le_add_of_nonneg_right (mul_nonneg hδ.le (hA0 x))
    have hb : -(v x * q x * inner ℝ (∇ q x) (∇ η x)) ≤
        |v x * q x| * (‖∇ q x‖ * ‖∇ η x‖) := by
      calc
        _ ≤ |v x * q x * inner ℝ (∇ q x) (∇ η x)| := neg_le_abs _
        _ = |v x * q x| * |inner ℝ (∇ q x) (∇ η x)| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    have hxb := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * η x * v x by
      exact mul_nonneg (mul_nonneg (by norm_num) (hη0 x)) (hvpos x).le)
    have hxy := young hδ (η x * v x * ‖∇ q x‖) (|v x * q x| * ‖∇ η x‖)
    rw [show (|v x * q x| * ‖∇ η x‖) ^ 2 = (v x * q x) ^ 2 * ‖∇ η x‖ ^ 2 by
      rw [mul_pow, sq_abs]] at hxy
    have hxa := mul_le_mul_of_nonneg_left (hA x hz) hδ.le
    unfold energy at hxa
    simp only [div_eq_mul_inv] at hxy ⊢
    nlinarith only [hxb, hxy, hxa]
  have hi := integral_mono (energy_cutoff_integrable hv hq hη hηc)
    ((hFi.add (hAi.const_mul δ)).add (hGi.const_mul (1 / δ))) hpoint
  simp only [Pi.add_apply] at hi
  have hsum1 : (∫ x, F x + δ * A x) = (∫ x, F x) + ∫ x, δ * A x :=
    integral_add hFi (hAi.const_mul δ)
  have hsum2 : (∫ x, F x + δ * A x + (1 / δ) * ((v x * q x) ^ 2 * ‖∇ η x‖ ^ 2)) =
      (∫ x, F x + δ * A x) + ∫ x, (1 / δ) * ((v x * q x) ^ 2 * ‖∇ η x‖ ^ 2) := by
    simpa only [Pi.add_apply] using
      integral_add (hFi.add (hAi.const_mul δ)) (hGi.const_mul (1 / δ))
  rw [hsum2, hsum1, hFzero, zero_add, integral_const_mul, integral_const_mul] at hi
  exact hi

end OMA.SpaceLiouville

namespace OMA.SpaceLiouville

open EuclideanGeometry InnerProductSpace MeasureTheory Metric Set Filter
open scoped Gradient Topology

theorem constant_of_weak_divergence (v q : Plane → ℝ)
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) (hvpos : ∀ x, 0 < v x)
    (hb : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : Plane) R, (v x * q x) ^ 2) ≤ C * R ^ 2)
    (hweak : ∀ η : Plane → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x) ^ 2 * inner ℝ (∇ q x) (∇ η x)) = 0) :
    ∃ c : ℝ, ∀ x, q x = c := by
  classical
  obtain ⟨C, hC⟩ := hb
  obtain ⟨K, hK0, hCut⟩ := cutoff_weighted_bound (fun x => v x * q x)
    (hv.continuous.mul hq.continuous) C hC
  let E := energy v q
  let r := fun m : ℕ => (m : ℝ) + 1
  let S := fun m => closedBall (0 : Plane) (r m)
  let W := fun m x => (cutoff (r m) x) ^ 2 * E x
  have hp (m : ℕ) : 0 < r m := by dsimp [r]; positivity
  have hp1 (m : ℕ) : 1 ≤ r m := by dsimp [r]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hS (m : ℕ) : MeasurableSet (S m) := measurableSet_closedBall
  have hEc : Continuous E := energy_continuous hv hq
  have hE0 (x : Plane) : 0 ≤ E x := energy_nonneg _ _ _
  have hWi (m : ℕ) : Integrable (W m) :=
    energy_cutoff_integrable hv hq (cutoff_smooth _) (cutoff_compact (hp m))
  have hW0 (m : ℕ) (x : Plane) : 0 ≤ W m x :=
    mul_nonneg (sq_nonneg _) (hE0 x)
  have hLocal (m : ℕ) : (∫ x in S m, E x) ≤ ∫ x, W m x := by
    calc
      _ = ∫ x in S m, W m x := by
        apply setIntegral_congr_fun (hS m)
        intro x hx
        change E x = (cutoff (r m) x) ^ 2 * E x
        rw [cutoff_one (hp m) hx, one_pow, one_mul]
      _ ≤ _ := setIntegral_le_integral (hWi _) (ae_of_all _ (hW0 _))
  have hBound (m : ℕ) : (∫ x in S m, E x) ≤ 4 * K := by
    have h1 := weak_energy_estimate v q (cutoff (r m)) (W m) (1 / 2)
      hv hq (cutoff_smooth _) (cutoff_compact (hp m)) hvpos
      (fun x => (cutoff_bounds _ x).1) (by norm_num) hweak (hWi m) (hW0 m) (by simp [W, E])
    change (∫ x, W m x) ≤ (1 / 2) * (∫ x, W m x) +
      (1 / (1 / 2)) * (∫ x, (v x * q x) ^ 2 * ‖∇ (cutoff (r m)) x‖ ^ 2) at h1
    have h2 := mul_le_mul_of_nonneg_left (hCut (r m) (hp1 m))
      (by positivity : (0 : ℝ) ≤ 1 / (1 / 2))
    linarith [hLocal m]
  have hrTop : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hCover : AECover (volume : Measure Plane) atTop S := aecover_closedBall hrTop
  have hEi : Integrable E := hCover.integrable_of_integral_bounded_of_nonneg_ae
    (4 * K)
    (fun m => hEc.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
    (ae_of_all _ hE0) (Eventually.of_forall hBound)
  let I := ∫ x, E x
  have hLimit : Tendsto (fun m : ℕ => ∫ x in S m, E x) atTop (𝓝 I) :=
    hCover.integral_tendsto_of_countably_generated hEi
  have hTail : Tendsto (fun m : ℕ => ∫ x in (S m)ᶜ, E x) atTop (𝓝 (0 : ℝ)) := by
    have hsub : Tendsto (fun m : ℕ => I - ∫ x in S m, E x) atTop (𝓝 (I - I)) :=
      tendsto_const_nhds.sub hLimit
    rw [sub_self] at hsub
    exact hsub.congr fun m => (setIntegral_compl (hS m) hEi).symm
  have hBig (δ : ℝ) (hδ : 0 < δ) : I ≤ (1 / δ) * K := by
    have hEst (m : ℕ) : (∫ x in S m, E x) ≤
        δ * (∫ x in (S m)ᶜ, E x) + (1 / δ) * K := by
      let A := (S m)ᶜ.indicator E
      have hAi : Integrable A := hEi.indicator (hS m).compl
      have hA0 (x : Plane) : 0 ≤ A x := by
        by_cases hx : x ∈ (S m)ᶜ
        · rw [show A x = E x from indicator_of_mem hx _]
          exact hE0 x
        · rw [show A x = 0 from indicator_of_notMem hx _]
      have hDom (x : Plane) (hx : ∇ (cutoff (r m)) x ≠ 0) : W m x ≤ A x := by
        have hxS : x ∈ (S m)ᶜ := fun h =>
          hx (gradient_zero_of_cutoff_one (cutoff_one (hp m) h))
        rw [show A x = E x from indicator_of_mem hxS _]
        change (cutoff (r m) x) ^ 2 * E x ≤ E x
        have hη := cutoff_bounds (r m) x
        exact mul_le_of_le_one_left (hE0 x) (pow_le_one₀ hη.1 hη.2)
      have h1 := weak_energy_estimate v q (cutoff (r m)) A δ
        hv hq (cutoff_smooth _) (cutoff_compact (hp m)) hvpos
        (fun x => (cutoff_bounds _ x).1) hδ hweak hAi hA0 hDom
      change (∫ x, W m x) ≤ δ * (∫ x, A x) +
        (1 / δ) * (∫ x, (v x * q x) ^ 2 * ‖∇ (cutoff (r m)) x‖ ^ 2) at h1
      rw [show (∫ x, A x) = ∫ x in (S m)ᶜ, E x from integral_indicator (hS m).compl] at h1
      have h2 := mul_le_mul_of_nonneg_left (hCut (r m) (hp1 m))
        (by positivity : 0 ≤ 1 / δ)
      linarith [hLocal m]
    have hright : Tendsto (fun m => δ * (∫ x in (S m)ᶜ, E x) + (1 / δ) * K)
        atTop (𝓝 ((1 / δ) * K)) := by
      simpa only [mul_zero, zero_add] using (tendsto_const_nhds.mul hTail).add
        (tendsto_const_nhds (x := (1 / δ) * K))
    exact le_of_tendsto_of_tendsto hLimit hright (Eventually.of_forall hEst)
  have hI : I = 0 := by
    have hI0 : 0 ≤ I := integral_nonneg hE0
    by_contra h
    have hIp : 0 < I := lt_of_le_of_ne hI0 (fun h0 => h h0.symm)
    let δ := (K + 1) / I
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have h1 := hBig δ hδ
    have h2 : I * δ ≤ K := (le_div_iff₀ hδ).mp (by
      simpa only [div_mul_eq_mul_div, one_mul] using h1)
    have hd : I * δ = K + 1 := by dsimp [δ]; field_simp [hIp.ne']
    linarith
  have hAE : E =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hE0 hEi).mp hI
  have hzero : E = 0 := (hEc.ae_eq_iff_eq volume continuous_zero).mp hAE
  have hfzero (x : Plane) : fderiv ℝ q x = 0 := by
    have hx := congrFun hzero x
    change (v x) ^ 2 * ‖∇ q x‖ ^ 2 = 0 at hx
    have hy : ‖∇ q x‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ (hvpos x).ne')
    have hnorm : ‖∇ q x‖ = 0 := by
      by_contra h
      exact (pow_ne_zero _ h) hy
    have hg : ∇ q x = 0 := norm_eq_zero.mp hnorm
    rw [← toDual_gradient, hg, map_zero]
  exact ⟨q 0, fun x => is_const_of_fderiv_eq_zero (hq.differentiable one_ne_zero) hfzero x 0⟩

end OMA.SpaceLiouville

theorem OMA.solution : OMA.R_DeGiorgi_DeGiorgi_three_R1.H3 := by
  exact OMA.SpaceLiouville.constant_of_weak_divergence
