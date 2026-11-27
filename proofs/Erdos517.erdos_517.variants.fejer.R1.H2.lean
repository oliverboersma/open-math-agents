import OMAReductions.R_Erdos517_erdos_517_variants_fejer_R1
import Mathlib.Analysis.Complex.Liouville

/-! A zero-count limit theorem for polynomial approximations on closed disks. -/

open Filter Metric Polynomial Set
open scoped Topology

namespace OMA.FejerZeros

/-- Factoring out roots within distance A of c leaves a polynomial whose value
at c is bounded by its maximum on the circle of radius 3A. -/
private theorem centerBound (p : ℂ[X]) (s : Multiset ℂ) (hp : p ≠ 0)
    (hs : s ≤ p.roots) {c : ℂ} {A M : ℝ} (hA : 0 < A)
    (hnear : ∀ r ∈ s, ‖c - r‖ ≤ A)
    (hcircle : ∀ z ∈ sphere c (3 * A), ‖p.eval z‖ ≤ M) :
    ‖p.eval c‖ ≤ M * (1 / 2 : ℝ) ^ s.card := by
  obtain ⟨q, hq⟩ := (s.prod_X_sub_C_dvd_iff_le_roots hp).2 hs
  have heval (z : ℂ) :
      ‖p.eval z‖ = (s.map fun r => ‖z - r‖).prod * ‖q.eval z‖ := by
    rw [hq, eval_mul, norm_mul, eval_multiset_prod]
    congr 1
    simpa [Multiset.map_map, Function.comp_def] using
      (map_multiset_prod (normHom.toMonoidHom : ℂ →* ℝ) (s.map fun r => z - r))
  have hqCircle (z : ℂ) (hz : z ∈ sphere c (3 * A)) :
      ‖q.eval z‖ ≤ M / (2 * A) ^ s.card := by
    have hl (r : ℂ) (hr : r ∈ s) : 2 * A ≤ ‖z - r‖ := by
      have htriangle := dist_triangle z r c
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, norm_sub_rev r c,
        mem_sphere_iff_norm.mp hz] at htriangle
      linarith [hnear r hr]
    have hfactor : (2 * A) ^ s.card ≤ (s.map fun r => ‖z - r‖).prod := by
      simpa using Multiset.prod_map_le_prod_map₀ (s := s) (fun _ => 2 * A)
        (fun r => ‖z - r‖) (fun _ _ => by positivity) hl
    refine (le_div_iff₀ (by positivity)).2 ?_
    rw [mul_comm]
    have hzBound := hcircle z hz
    rw [heval] at hzBound
    exact (mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)).trans hzBound
  have hqc : ‖q.eval c‖ ≤ M / (2 * A) ^ s.card := by
    simpa using Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 0
      (show 0 < 3 * A by positivity) q.differentiable.diffContOnCl hqCircle
  have hfactor : (s.map fun r => ‖c - r‖).prod ≤ A ^ s.card := by
    simpa using Multiset.prod_map_le_prod_map₀ (s := s) (fun r => ‖c - r‖)
      (fun _ => A) (fun _ _ => norm_nonneg _) hnear
  rw [heval]
  calc
    _ ≤ A ^ s.card * (M / (2 * A) ^ s.card) :=
      mul_le_mul hfactor hqc (norm_nonneg _) (by positivity)
    _ = M * (1 / 2 : ℝ) ^ s.card := by
      rw [show A ^ s.card * (M / (2 * A) ^ s.card) =
        M * (A ^ s.card / (2 * A) ^ s.card) by ring, ← div_pow]
      congr 2
      field_simp

/-- Uniform convergence excludes polynomial roots from every compact set on
which the limit has no zeros. -/
private theorem eventuallyRootFree (P : ℕ → ℂ[X]) {f : ℂ → ℂ} (hf : Continuous f)
    (hu : ∀ R : ℝ, TendstoUniformlyOn (fun j z => (P j).eval z) f atTop (closedBall 0 R))
    {K : Set ℂ} {R : ℝ} (hK : IsCompact K) (hKR : K ⊆ closedBall 0 R)
    (hnz : ∀ z ∈ K, f z ≠ 0) :
    ∀ᶠ j in atTop, ∀ z ∈ K, (P j).eval z ≠ 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne hf.norm.continuousOn
  have hpos : 0 < ‖f z₀‖ := norm_pos_iff.mpr (hnz _ hz₀)
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hu R)) _ hpos] with j hj
  intro z hz he
  have hd := hj z (hKR hz)
  rw [he] at hd
  have hle : ‖f z₀‖ ≤ ‖f z‖ := hmin hz
  simp only [dist_eq_norm, sub_zero] at hd
  exact (not_lt_of_ge hle) hd

end OMA.FejerZeros

open OMA.FejerZeros

set_option maxHeartbeats 600000 in
theorem OMA.solution : OMA.R_Erdos517_erdos_517_variants_fejer_R1.H2 := by
  classical
  intro P f hAnalytic hUniform hMany hFinite
  have hContinuous : Continuous f :=
    continuousOn_univ.mp hAnalytic.continuousOn
  obtain ⟨B, hB⟩ := (hFinite.image (fun z => ‖z‖)).bddAbove
  let R₀ := max B 0 + 1
  have hR₀ : 0 < R₀ := by dsimp [R₀]; linarith [le_max_right B 0]
  have hzeros (z : ℂ) (hz : f z = 0) : ‖z‖ < R₀ := by
    exact (hB (mem_image_of_mem (fun z => ‖z‖) hz)).trans_lt
      (by dsimp [R₀]; linarith [le_max_left B 0])
  let c : ℂ := (R₀ : ℂ)
  have hcnorm : ‖c‖ = R₀ := by simp [c, Complex.norm_real, abs_of_pos hR₀]
  have hcnz : f c ≠ 0 := fun hc => (lt_irrefl R₀) (hcnorm ▸ hzeros c hc)
  let A : ℝ := R₀ + ‖c‖
  have hA : 0 < A := by dsimp [A]; positivity
  let S : ℝ := 3 * A + ‖c‖
  have hcS : c ∈ closedBall 0 S := by
    simpa [Metric.mem_closedBall, S] using (show ‖c‖ ≤ 3 * A + ‖c‖ by linarith)
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : ℂ) S).bddAbove_image
    hContinuous.norm.continuousOn
  let M := M₀ + 1
  have hM : 0 ≤ M := by
    have h := hM₀ (mem_image_of_mem _ hcS)
    dsimp [M]
    linarith [norm_nonneg (f c)]
  have heSmall : 0 < ‖f c‖ / 2 := half_pos (norm_pos_iff.mpr hcnz)
  have ht : Tendsto (fun m : ℕ => M * (1 / 2 : ℝ) ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num)).const_mul M
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds heSmall)).exists
  obtain ⟨R, hR⟩ := hMany m
  let K := closedBall (0 : ℂ) R ∩ {z : ℂ | R₀ ≤ ‖z‖}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hKfree := eventuallyRootFree P hContinuous hUniform hK (fun _ hz => hz.1)
    (fun z hz hzero => (not_lt_of_ge hz.2) (hzeros z hzero))
  have hUb := Metric.tendstoUniformlyOn_iff.mp (hUniform S)
  obtain ⟨j, hjR, hjK, hj⟩ :=
    (hR.and (hKfree.and (hUb _ (lt_min zero_lt_one heSmall)))).exists
  have hLower : ‖f c‖ / 2 < ‖(P j).eval c‖ := by
    have hclose := (hj c hcS).trans_le (min_le_right _ _)
    rw [dist_eq_norm] at hclose
    linarith [norm_sub_norm_le (f c) ((P j).eval c)]
  have hp : P j ≠ 0 := by
    intro he
    simp [he, not_lt_of_ge heSmall.le] at hLower
  let s := (P j).roots.filter (fun z => ‖z‖ ≤ R)
  have hnear (r : ℂ) (hr : r ∈ s) : ‖c - r‖ ≤ A := by
    have ⟨hroot, hrR⟩ := Multiset.mem_filter.mp hr
    have hrR₀ : ‖r‖ < R₀ := by
      by_contra! hge
      exact hjK r ⟨by simpa using hrR, hge⟩ ((mem_roots hp).mp hroot)
    exact (norm_sub_le c r).trans (by dsimp [A]; linarith)
  have hcircle (z : ℂ) (hz : z ∈ sphere c (3 * A)) : ‖(P j).eval z‖ ≤ M := by
    have hzS : z ∈ closedBall (0 : ℂ) S := by
      have ht := dist_triangle z c (0 : ℂ)
      rw [mem_sphere.mp hz] at ht
      simpa [Metric.mem_closedBall, S] using ht
    have hclose := (hj z hzS).trans_le (min_le_left _ _)
    rw [dist_comm, dist_eq_norm] at hclose
    dsimp [M]
    linarith [norm_sub_norm_le ((P j).eval z) (f z), hM₀ (mem_image_of_mem _ hzS)]
  have hUpper := centerBound (P j) s hp (Multiset.filter_le _ _) hA hnear hcircle
  have hdec : (1 / 2 : ℝ) ^ s.card ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hjR
  exact (not_lt_of_ge (hUpper.trans (mul_le_mul_of_nonneg_left hdec hM)))
    (hm.trans hLower)
