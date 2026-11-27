import OMAReductions.R_Erdos1042_erdos_1042_variants_universal_R1
import Mathlib

/-! A two-interval family via quadratic pullbacks of the Chebyshev lemniscates.
The Chebyshev roots, separation and compactness lemmas are adapted from
@Genbox (open-math-agents 1aa4f45ad130335f4061714cc0c74c2b865116e8
and b86a4bdab6fdd064bb2d2cea7f4173586f0a518a). -/
open Polynomial Set Filter
open scoped BigOperators ENNReal Topology
open Polynomial.Chebyshev (T)

private noncomputable def OMA.cheb (n : ℕ) : ℂ[X] :=
  if n = 0 then 1 else Polynomial.Chebyshev.C ℂ (n : ℤ)

private theorem OMA.cheb_degree_monic (n : ℕ) : (cheb n).natDegree = n ∧ (cheb n).Monic := by
  have hC (m : ℕ) :
      (Polynomial.Chebyshev.C ℂ (m : ℤ)).natDegree = m ∧
      (m ≠ 0 → (Polynomial.Chebyshev.C ℂ (m : ℤ)).Monic) := by
    induction m using Nat.twoStepInduction with
    | zero => simp
    | one => simp
    | more m hm hm₁ =>
      let p := (X : ℂ[X]) * Polynomial.Chebyshev.C ℂ ((m + 1 : ℕ) : ℤ)
      let q := Polynomial.Chebyshev.C ℂ (m : ℤ)
      have hp : p.Monic := monic_X.mul (hm₁.2 (by omega))
      have hpd : p.natDegree = m + 2 := by
        change ((X : ℂ[X]) * Polynomial.Chebyshev.C ℂ ((m + 1 : ℕ) : ℤ)).natDegree = _
        rw [monic_X.natDegree_mul (hm₁.2 (by omega)), natDegree_X, hm₁.1]
        omega
      have hlt : q.natDegree < p.natDegree := by
        change (Polynomial.Chebyshev.C ℂ (m : ℤ)).natDegree < p.natDegree
        rw [hm.1, hpd]
        omega
      have he : Polynomial.Chebyshev.C ℂ ((m + 2 : ℕ) : ℤ) = p - q := by
        dsimp [p, q]
        exact Polynomial.Chebyshev.C_add_two ℂ (m : ℤ)
      rw [he, natDegree_sub_eq_left_of_natDegree_lt hlt, hpd]
      exact ⟨rfl, fun _ => hp.sub_of_left (degree_lt_degree hlt)⟩
  by_cases hn : n = 0
  · simp [hn, cheb]
  · simpa only [cheb, if_neg hn] using ⟨(hC n).1, (hC n).2 hn⟩

private theorem OMA.cheb_eval_real_scaled (n : ℕ) (x : ℝ) (hn : n ≠ 0) :
    (cheb n).eval (((2 * x : ℝ)) : ℂ) = (((2 * (T ℝ (n : ℤ)).eval x : ℝ)) : ℂ) := by
  rw [cheb, if_neg hn, ← Polynomial.Chebyshev.map_C Complex.ofRealHom]
  rw [show ((↑(2 * x) : ℂ)) = Complex.ofRealHom (2 * x) by rfl, eval_map_apply]
  have he := congrArg (eval x) (Polynomial.Chebyshev.C_comp_two_mul_X ℝ (n : ℤ))
  exact congrArg Complex.ofReal (by simpa only [eval_comp, eval_mul, eval_ofNat, eval_X] using he)

private def OMA.chebSegment : Set ℂ := Complex.ofReal '' Icc (-2 : ℝ) 2

private theorem OMA.cheb_eval_le_two (n : ℕ) {z : ℂ} (hz : z ∈ chebSegment) :
    ‖(cheb n).eval z‖ ≤ 2 := by
  by_cases hn : n = 0
  · simp [cheb, hn]
  obtain ⟨x, hx, rfl⟩ := hz
  have he : (cheb n).eval (x : ℂ) = (((2 * (T ℝ (n : ℤ)).eval (x / 2) : ℝ)) : ℂ) := by
    rw [← cheb_eval_real_scaled n (x / 2) hn]
    congr 2
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hx' : |x / 2| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hh := Polynomial.Chebyshev.abs_eval_T_real_le_one (n : ℤ) hx'
  linarith

private noncomputable def OMA.chebAngle (n i : ℕ) : ℝ :=
  (2 * (i : ℝ) + 1) * Real.pi / (2 * (n : ℝ))

private noncomputable def OMA.chebPoint (n : ℕ) (i : Fin n) : ℂ :=
  ((2 * Real.cos (chebAngle n i) : ℝ) : ℂ)

private theorem OMA.cheb_angle_mem (n : ℕ) (i : Fin n) :
    chebAngle n i ∈ Ioo (0 : ℝ) Real.pi := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from Nat.zero_lt_of_lt i.isLt)
  have hiR : (i : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
  unfold chebAngle
  refine ⟨by positivity, (div_lt_iff₀ (by positivity)).2 ?_⟩
  have h := mul_lt_mul_of_pos_right (show 2 * (i : ℝ) + 1 < 2 * n by linarith) Real.pi_pos
  linarith

private theorem OMA.cheb_point_mem (n : ℕ) (i : Fin n) : chebPoint n i ∈ chebSegment := by
  refine ⟨2 * Real.cos (chebAngle n i), ?_, rfl⟩
  exact ⟨by linarith [Real.neg_one_le_cos (chebAngle n i)],
    by linarith [Real.cos_le_one (chebAngle n i)]⟩

private theorem OMA.cheb_cos_zero (n : ℕ) (i : Fin n) :
    Real.cos ((n : ℝ) * chebAngle n i) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.zero_lt_of_lt i.isLt).ne'
  rw [Real.cos_eq_zero_iff]
  refine ⟨(i : ℕ), ?_⟩
  unfold chebAngle
  push_cast
  field_simp

private theorem OMA.cheb_point_eval_zero (n : ℕ) (i : Fin n) : (cheb n).eval (chebPoint n i) = 0 := by
  have hn : n ≠ 0 := (Nat.zero_lt_of_lt i.isLt).ne'
  rw [chebPoint, cheb_eval_real_scaled n _ hn, Polynomial.Chebyshev.T_real_cos]
  simp [cheb_cos_zero]

private theorem OMA.cheb_eval_mid_node (n : ℕ) (hn : n ≠ 0) (k : ℕ) (hk : k ≤ n) :
    ‖(cheb n).eval ((2 * Polynomial.Chebyshev.node n k : ℝ) : ℂ)‖ = 2 := by
  rw [cheb_eval_real_scaled n _ hn, Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr hk)]
  simp

private theorem OMA.cheb_points_separated {n : ℕ} {i j : Fin n} (hij : i < j) :
    (chebPoint n j).re < 2 * Polynomial.Chebyshev.node n ((i : ℕ) + 1) ∧
      2 * Polynomial.Chebyshev.node n ((i : ℕ) + 1) < (chebPoint n i).re := by
  let k : ℕ := (i : ℕ) + 1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n from Nat.zero_lt_of_lt i.isLt)
  have hjR : (k : ℝ) ≤ j := by exact_mod_cast (show k ≤ (j : ℕ) from Nat.succ_le_of_lt hij)
  let θ := (k : ℝ) * Real.pi / n
  have hθ : θ = (2 * (k : ℝ)) * Real.pi / (2 * (n : ℝ)) := by dsimp [θ]; ring
  have hlt₁ : chebAngle n i < θ := by
    rw [hθ, chebAngle]
    apply div_lt_div_of_pos_right _ (by positivity)
    have he : (k : ℝ) = (i : ℝ) + 1 := by simp [k]
    exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
  have hlt₂ : θ < chebAngle n j := by
    rw [hθ, chebAngle]
    apply div_lt_div_of_pos_right _ (by positivity)
    exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos
  have hi := cheb_angle_mem n i
  have hj := cheb_angle_mem n j
  have h₁ := Real.cos_lt_cos_of_nonneg_of_le_pi (hi.1.le.trans hlt₁.le) hj.2.le hlt₂
  have h₂ := Real.cos_lt_cos_of_nonneg_of_le_pi hi.1.le (hlt₂.le.trans hj.2.le) hlt₁
  change 2 * Real.cos (chebAngle n j) < 2 * Real.cos θ ∧
    2 * Real.cos θ < 2 * Real.cos (chebAngle n i)
  exact ⟨by linarith, by linarith⟩

private theorem OMA.cheb_point_injective (n : ℕ) : Function.Injective (chebPoint n) := by
  intro i j heq
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hs := cheb_points_separated hij
    rw [heq] at hs
    exact False.elim ((lt_irrefl _) (hs.1.trans hs.2))
  · rfl
  · have hs := cheb_points_separated hij
    rw [heq] at hs
    exact False.elim ((lt_irrefl _) (hs.1.trans hs.2))

private theorem OMA.cheb_roots (n : ℕ) :
    (cheb n).roots = (Finset.univ.image (chebPoint n)).val := by
  classical
  refine roots_eq_of_degree_eq_card (fun z hz => ?_) ?_
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact cheb_point_eval_zero n i
  · rw [Finset.card_image_of_injective _ (cheb_point_injective n), Finset.card_univ,
      Fintype.card_fin, degree_eq_natDegree (cheb_degree_monic n).2.ne_zero,
      (cheb_degree_monic n).1]

private theorem OMA.cheb_factor (n : ℕ) : cheb n = ∏ i, (X - C (chebPoint n i)) := by
  classical
  calc
    cheb n = ((cheb n).roots.map fun z => X - C z).prod :=
      (IsAlgClosed.splits (cheb n)).eq_prod_roots_of_monic (cheb_degree_monic n).2
    _ = ∏ z ∈ Finset.univ.image (chebPoint n), (X - C z) := by rw [cheb_roots]; rfl
    _ = _ := Finset.prod_image (fun x _ y _ h => cheb_point_injective n h)

private theorem OMA.cheb_eval_prod (n : ℕ) (z : ℂ) :
    (cheb n).eval z = ∏ i, (z - chebPoint n i) := by
  rw [cheb_factor]
  simp [eval_prod]

private theorem OMA.cheb_det_upper {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, z i ∈ chebSegment) :
    ‖(Matrix.vandermonde z).det‖ ≤ (2 * (n : ℝ)) ^ n := by
  classical
  let M := Matrix.of (fun i j : Fin n => (cheb j).eval (z i))
  have hdet : (Matrix.vandermonde z).det = M.det :=
    Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde z (fun j : Fin n => cheb j)
      (fun i => (cheb_degree_monic i).1) (fun i => (cheb_degree_monic i).2)
  rw [hdet]
  have hbound := Matrix.det_le (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ))
    (A := M) (x := (2 : ℝ)) (fun i j => cheb_eval_le_two j (hz i))
  change ‖M.det‖ ≤ _ at hbound
  have hn : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
  calc
    ‖M.det‖ ≤ (n.factorial : ℝ) * (2 : ℝ) ^ n := by
      simpa only [Fintype.card_fin, nsmul_eq_mul] using hbound
    _ ≤ (2 * (n : ℝ)) ^ n := by
      rw [mul_pow, mul_comm (2 ^ n)]
      exact mul_le_mul_of_nonneg_right hn (by positivity)

private theorem OMA.edist_prod_eq_det {n : ℕ} (z : Fin n → ℂ) :
    (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, edist (z i) (z j)) =
      ENNReal.ofReal ‖(Matrix.vandermonde z).det‖ := by
  rw [Matrix.det_vandermonde]
  rw [norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
  apply Finset.prod_congr rfl
  intro i _
  rw [norm_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ => norm_nonneg _)]
  apply Finset.prod_congr rfl
  intro j _
  rw [edist_dist, dist_eq_norm, norm_sub_rev]

private theorem OMA.cheb_nth_upper (n : ℕ) :
    Erdos1042.nthDiameter chebSegment n ≤
      (ENNReal.ofReal ((2 * (n : ℝ)) ^ n)) ^ (1 / ((n.choose 2 : ℕ) : ℝ)) := by
  unfold Erdos1042.nthDiameter
  refine iSup_le fun z => iSup_le fun hz => ?_
  rw [edist_prod_eq_det]
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (cheb_det_upper z hz)) (by positivity)
private theorem OMA.cheb_nth_upper_limit :
    Tendsto (fun n : ℕ => (ENNReal.ofReal ((2 * (n : ℝ)) ^ n)) ^
      (1 / ((n.choose 2 : ℕ) : ℝ))) atTop (𝓝 1) := by
  have hscale : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlog : Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ)) / ((n : ℝ) - 1)) atTop (𝓝 0) := by
    refine ((Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) (-1) 1 (by norm_num)).comp hscale).congr ?_
    intro n
    simp only [Function.comp_apply, pow_one]
    congr 1
    ring
  have hlim : Tendsto (fun n : ℕ => Real.exp (2 * (Real.log (2 * (n : ℝ)) / ((n : ℝ) - 1))))
      atTop (𝓝 1) := by
    have hsmall : Tendsto (fun n : ℕ => 2 * (Real.log (2 * (n : ℝ)) / ((n : ℝ) - 1)))
        atTop (𝓝 0) := by simpa only [mul_zero] using hlog.const_mul (2 : ℝ)
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hsmall
  have hlim' : Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp (2 * (Real.log (2 * (n : ℝ)) / ((n : ℝ) - 1))))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one] using
      (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp hlim
  refine hlim'.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < (2 * (n : ℝ)) ^ n := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hpos.le (by positivity), Real.rpow_def_of_pos hpos,
    Real.log_pow, Nat.cast_choose_two]
  congr 2
  field_simp
private theorem OMA.cheb_strict_component_root (p : ℂ[X]) (hdeg : 0 < p.natDegree)
    {c : ℝ} (hc : 0 < c) (hbounded : Bornology.IsBounded {z : ℂ | ‖p.eval z‖ < c})
    {z : ℂ} (hz : ‖p.eval z‖ < c) :
    ∃ r ∈ connectedComponentIn {q : ℂ | ‖p.eval q‖ < c} z, p.eval r = 0 := by
  let S := {q : ℂ | ‖p.eval q‖ < c}
  let D := Metric.ball (0 : ℂ) c
  let U := connectedComponentIn S z
  have hzS : z ∈ S := hz
  have hUS : U ⊆ S := connectedComponentIn_subset S z
  have hzU : z ∈ U := mem_connectedComponentIn hzS
  have hU : IsConnected U := isConnected_connectedComponentIn_iff.mpr hzS
  have hD : IsPreconnected D := (convex_ball (0 : ℂ) c).isPreconnected
  have hSopen : IsOpen S := isOpen_lt p.continuous.norm continuous_const
  have hmap : IsOpenMap p.eval := by
    have han : AnalyticOnNhd ℂ p.eval univ := fun v _ => p.differentiable.analyticAt v
    rcases han.is_constant_or_isOpenMap with ⟨w, heq⟩ | hopen
    · have hpconst : p = C w := Polynomial.funext (fun x => by simpa using heq x)
      rw [hpconst, natDegree_C] at hdeg
      omega
    · exact hopen
  have hzD : p.eval z ∈ D := by simpa [D, Metric.mem_ball, dist_zero_right] using hz
  have hpart : closure U ∩ S ⊆ U := by
    have hpre : IsPreconnected (closure U ∩ S) :=
      hU.isPreconnected.subset_closure
        (fun q hq => ⟨subset_closure hq, hUS hq⟩) inter_subset_left
    exact hpre.subset_connectedComponentIn ⟨subset_closure hzU, hzS⟩ inter_subset_right
  have hcl : IsClosed (p.eval '' closure U) :=
    (((hbounded.subset hUS).isCompact_closure).image p.continuous).isClosed
  have hclSub : closure (p.eval '' U) ⊆ p.eval '' closure U :=
    closure_minimal (image_mono subset_closure) hcl
  have hsurj := hD.subset_of_closure_inter_subset (hmap _ hSopen.connectedComponentIn)
    ⟨p.eval z, hzD, ⟨z, hzU, rfl⟩⟩ (by
      intro w hw
      obtain ⟨q, hq, rfl⟩ := hclSub hw.1
      have hqS : q ∈ S := by
        simpa [S, D, Metric.mem_ball, dist_zero_right] using hw.2
      exact ⟨q, hpart ⟨hq, hqS⟩, rfl⟩)
  exact hsurj (Metric.mem_ball_self hc)
private theorem OMA.counting_prod_index {R M : Type*} [CommMonoid M] (s : Multiset R)
    (g : R → M) : (s.map g).prod = ∏ i : Fin s.toList.length, g (s.toList.get i) := by
  rw [← List.prod_ofFn]
  change _ = (List.ofFn (g ∘ s.toList.get)).prod
  rw [← List.map_ofFn, List.ofFn_get]
  simp

private theorem OMA.counting_sublevel_compact (p : ℂ[X]) (hp : p.Monic)
    (hdeg : 0 < p.natDegree) (c : ℝ) (hc : 0 ≤ c) :
    IsCompact {z : ℂ | ‖p.eval z‖ ≤ c} := by
  classical
  have hclosed : IsClosed {z : ℂ | ‖p.eval z‖ ≤ c} := isClosed_le p.continuous.norm continuous_const
  have hfin : (p.rootSet ℂ).Finite := p.rootSet_finite _
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hfin.isBounded
  have hroot (r : ℂ) (hr : r ∈ p.roots) : ‖r‖ < R := by
    have he : p.eval r = 0 := (mem_roots hp.ne_zero).1 hr
    have hrC : r ∈ p.rootSet ℂ := hp.mem_rootSet.mpr (by simpa using he)
    simpa [Metric.mem_ball, dist_zero_right] using hR hrC
  refine Metric.isCompact_of_isClosed_isBounded hclosed
    (Metric.isBounded_ball.subset (t := Metric.ball (0 : ℂ) (R + c + 1)) ?_)
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  by_contra! h
  have hbound (i : Fin p.roots.toList.length) : c + 1 ≤ ‖z - p.roots.toList.get i‖ := by
    have hr := hroot (p.roots.toList.get i) (Multiset.mem_toList.mp (List.get_mem _ i))
    have ht := norm_add_le (z - p.roots.toList.get i) (p.roots.toList.get i)
    rw [sub_add_cancel] at ht
    linarith
  have hL : p.roots.toList.length = p.natDegree := by
    simpa using (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hprod : (c + 1) ^ p.natDegree ≤ ‖p.eval z‖ := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hp, counting_prod_index, norm_prod]
    have hprod : (∏ _ : Fin p.roots.toList.length, (c + 1)) ≤
        ∏ i, ‖z - p.roots.toList.get i‖ :=
      Finset.prod_le_prod (s := Finset.univ) (fun _ _ => by positivity) (fun i _ => hbound i)
    simpa [hL] using hprod
  have hpow : c + 1 ≤ (c + 1) ^ p.natDegree := by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ c + 1 by linarith) (by omega : 1 ≤ p.natDegree)
  change ‖p.eval z‖ ≤ c at hz
  linarith [hpow.trans hprod]
private theorem OMA.base_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (fun i : Fin n => connectedComponentIn (Erdos1047.strictSublevelSet (cheb n) 1) (chebPoint n i)) := by
  classical
  let U := Erdos1047.strictSublevelSet (cheb n) 1
  let F (i : Fin n) := connectedComponentIn U (chebPoint n i)
  have hroot (i : Fin n) : chebPoint n i ∈ U := by
    change ‖(cheb n).eval (chebPoint n i)‖ < 1
    simp [cheb_point_eval_zero]
  have hsep {i j : Fin n} (hij : i < j) : F i ≠ F j := by
    intro hEq
    let x : ℝ := 2 * Polynomial.Chebyshev.node n ((i : ℕ) + 1)
    have hmid : (chebPoint n j).re < x ∧ x < (chebPoint n i).re := cheb_points_separated hij
    have hB (z : ℂ) (hz : z ∈ U) : z.re ≠ x := by
      intro hx
      have hp : ‖(cheb n).eval ((z.re : ℝ) : ℂ)‖ ≤ ‖(cheb n).eval z‖ := by
        rw [cheb_eval_prod, cheb_eval_prod, norm_prod, norm_prod]
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro k _
        simp only [chebPoint, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        simpa only [chebPoint, Complex.sub_re, Complex.ofReal_re] using
          Complex.abs_re_le_norm (z - chebPoint n k)
      have hxv : ‖(cheb n).eval (x : ℂ)‖ = 2 :=
        cheb_eval_mid_node n (by omega) ((i : ℕ) + 1) (by omega)
      rw [hx, hxv] at hp
      change ‖(cheb n).eval z‖ < 1 at hz
      linarith
    have hR : chebPoint n i ∈ F i := mem_connectedComponentIn (hroot i)
    have hL : chebPoint n j ∈ F i := hEq ▸ mem_connectedComponentIn (hroot j)
    have hConn : IsConnected (F i) := isConnected_connectedComponentIn_iff.mpr (hroot i)
    have h := hConn.isPreconnected.lt_of_ne Complex.continuous_re.continuousOn
      (fun z hz => hB z (connectedComponentIn_subset _ _ hz))
      ⟨chebPoint n i, hR, hmid.2⟩ hL
    exact (not_lt_of_ge hmid.1.le) h
  have hinj : Function.Injective F := by
    intro i j h
    rcases lt_trichotomy i j with hij | hij | hij
    · exact (hsep hij h).elim
    · exact hij
    · exact (hsep hij h.symm).elim
  exact hinj
namespace DoubleInterval
open OMA
set_option maxHeartbeats 900000 in
private lemma quadratic_family (t : ℝ) (ht : 3 ≤ t) (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : ℂ[X], Erdos1042.MonicWithRootsIn
      {z : ℂ | z^2 - (t : ℂ) ∈ chebSegment} (n*2) f ∧ Erdos1042.numComponents f = n*2 := by
  classical
  let P := (X : ℂ[X])^2-C (t : ℂ)
  let q := (cheb n).comp P
  let h (z : ℂ) := z^2-(t:ℂ)
  let U := Erdos1047.strictSublevelSet q 1
  let V := Erdos1047.strictSublevelSet (cheb n) 1
  have hdegP : P.natDegree = 2 := natDegree_X_pow_sub_C
  have hmon : q.Monic := (cheb_degree_monic n).2.comp (monic_X_pow_sub_C _ (by decide : 2≠0)) (by omega)
  have hdeg : q.natDegree = n*2 := by change ((cheb n).comp P).natDegree = _; rw [natDegree_comp,hdegP,(cheb_degree_monic n).1]
  have hev (z : ℂ) : q.eval z = (cheb n).eval (h z) := by simp [q,P,h,eval_comp]
  have image_sub : h '' U ⊆ V := by
    rintro _ ⟨z,hz,rfl⟩
    change ‖(cheb n).eval (h z)‖ < 1
    rw [← hev]; exact hz
  have hcont : Continuous h := by dsimp [h]; fun_prop
  let y (i : Fin n) : ℝ := (chebPoint n i).re
  have he (i : Fin n) : (y i : ℂ) = chebPoint n i := rfl
  have hy (i : Fin n) : -2 ≤ y i ∧ y i ≤ 2 := by
    obtain ⟨v,hv,hv'⟩ := cheb_point_mem n i
    simpa [y,← hv'] using hv
  have hpos (i : Fin n) : 0 < Real.sqrt (t+y i) := Real.sqrt_pos.mpr (by linarith [(hy i).1])
  let v (j : Bool × Fin n) : ℂ := if j.1 then (Real.sqrt (t+y j.2) : ℂ) else -(Real.sqrt (t+y j.2) : ℂ)
  have hv (j : Bool × Fin n) : h (v j) = chebPoint n j.2 := by
    obtain ⟨b,i⟩ := j
    have hs := congrArg Complex.ofReal (Real.sq_sqrt (by linarith [(hy i).1] : 0 ≤ t+y i))
    push_cast at hs
    cases b <;> simp [v,h,hs,← he]
  have hroot (j : Bool × Fin n) : q.eval (v j) = 0 := by rw [hev,hv,cheb_point_eval_zero]
  have hmem (j : Bool × Fin n) : v j ∈ U := by change ‖q.eval _‖ < 1; simp [hroot]
  have root_id {z : ℂ} (hz : q.eval z = 0) : ∃ j, v j = z := by
    have hbase := (mem_roots (cheb_degree_monic n).2.ne_zero).mpr ((hev z) ▸ hz)
    rw [cheb_roots] at hbase
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (show h z ∈ Finset.univ.image (chebPoint n) from hbase)
    have eqsq : z^2=(v (true,i))^2 := by
      have heq : h z = h (v (true,i)) := hi.symm.trans (hv (true,i)).symm
      change z^2-(t:ℂ)=(v (true,i))^2-(t:ℂ) at heq
      linear_combination heq
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp eqsq with heq | heq
    · exact ⟨(true,i),heq.symm⟩
    · exact ⟨(false,i), by simpa [v] using heq.symm⟩
  have barrier (z : ℂ) (hz : z ∈ U) : z.re ≠ 0 := by
    intro hre
    have hreal : (h z).re = -z.im^2-t := by simp [h,pow_two,Complex.mul_re,hre]
    have hb (i : Fin n) : 1 ≤ ‖h z - chebPoint n i‖ := by
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      rw [Complex.sub_re,hreal]
      change 1 ≤ |-(z.im ^ 2) - t - y i|
      exact le_abs.mpr (Or.inr (by nlinarith [(hy i).1,sq_nonneg z.im]))
    have H : 1 ≤ ‖q.eval z‖ := by
      rw [hev,cheb_eval_prod,norm_prod]
      exact Finset.one_le_prod (fun i _ => hb i)
    exact (not_lt_of_ge H) hz
  let A (j : Bool × Fin n) := connectedComponentIn U (v j)
  have hinj : Function.Injective A := by
    rintro ⟨b,i⟩ ⟨c,j⟩ hEq
    have hA : v (c,j) ∈ A (b,i) := hEq ▸ mem_connectedComponentIn (hmem _)
    have hB := hcont.continuousOn.mapsTo_connectedComponentIn (hmem (b,i)) hA
    have H := connectedComponentIn_mono _ image_sub hB
    rw [hv,hv] at H
    have hij := base_injective n hn (connectedComponentIn_eq H)
    change i = j at hij
    subst j
    have posneg : A (true,i) ≠ A (false,i) := by
      intro e
      have hc := (isConnected_connectedComponentIn_iff.mpr (hmem (true,i))).isPreconnected
      have ha : v (true,i) ∈ A (true,i) := mem_connectedComponentIn (hmem _)
      have hb : v (false,i) ∈ A (true,i) := e ▸ mem_connectedComponentIn (hmem _)
      have nz := hc.lt_of_ne Complex.continuous_re.continuousOn
        (fun z hz => barrier z (connectedComponentIn_subset _ _ hz))
        ⟨v (true,i), ha, by simpa [v] using hpos i⟩ hb
      simp [v] at nz
      linarith [hpos i]
    cases b <;> cases c <;> simp_all
  have hbound : Bornology.IsBounded U := (counting_sublevel_compact q hmon (by omega) 1 zero_le_one).isBounded.subset
    (fun z hz => (show ‖q.eval z‖ < 1 from hz).le)
  have hcover : Erdos1047.componentsIn U = Set.range A := by
    ext T
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨w,hw,hw0⟩ := cheb_strict_component_root q (by omega) (c:=1) zero_lt_one hbound hz
      obtain ⟨j,hj⟩ := root_id hw0
      refine ⟨j,?_⟩
      change connectedComponentIn U (v j) = _
      rw [hj]
      exact (connectedComponentIn_eq hw).symm
    · rintro ⟨j,rfl⟩
      exact ⟨v j,hmem j,rfl⟩
  refine ⟨q,⟨hmon,hdeg,?_⟩,?_⟩
  · intro z hz
    obtain ⟨j,rfl⟩ := root_id ((mem_roots hmon.ne_zero).mp hz)
    change h (v j) ∈ chebSegment
    rw [hv]
    exact cheb_point_mem n _
  · change (Erdos1047.componentsIn U).ncard = n*2
    rw [hcover,Set.ncard_range_of_injective hinj]
    simp [Nat.mul_comm]
end DoubleInterval
private lemma DoubleInterval.prod_prod_Ioi_const {M : Type*} [CommMonoid M] (n : ℕ) (c : M) :
    (∏ i : Fin n, ∏ _ ∈ Finset.Ioi i, c) = c ^ (n.choose 2) := by
  simp_rw [Finset.prod_const, Fin.card_Ioi]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i), Finset.sum_range_reflect (fun i : ℕ => i) n,
    Finset.sum_range_id, Nat.choose_two_right]
namespace DoubleInterval
open OMA Erdos1042
private lemma interval_width (G : Set ℂ) (r : ℝ) (hr : 0 < r)
    (hsub : G ⊆ Complex.ofReal '' Icc 0 r) (hcap : transfiniteDiameter G = 1) : 4 ≤ r := by
  let a : ℝ := r/4
  have ha : 0 < a := by dsimp [a]; positivity
  let c := ENNReal.ofReal a
  let w (z : ℂ) : ℂ := ((z.re/a - 2 : ℝ) : ℂ)
  have hw (z : ℂ) (hz : z ∈ G) : w z ∈ chebSegment := by
    obtain ⟨s,hs,rfl⟩ := hsub hz
    refine ⟨s/a-2,⟨?_,?_⟩,rfl⟩
    · have := div_nonneg hs.1 ha.le
      linarith
    · have := (div_le_iff₀ ha).2 (show s ≤ 4*a by dsimp [a]; linarith [hs.2])
      linarith
  have he (z : ℂ) (hz : z ∈ G) : z = (a : ℂ)*(w z+2) := by
    obtain ⟨s,hs,rfl⟩ := hsub hz
    simp [w]
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
  have hed (z b : ℂ) (hz : z∈G) (hb : b∈G) : edist z b = c*edist (w z) (w b) := by
    rw [edist_dist,edist_dist,dist_eq_norm,dist_eq_norm,
      show z-b = (a:ℂ)*(w z - w b) by calc
        _ = (a:ℂ)*(w z+2)-(a:ℂ)*(w b+2) := congrArg₂ (·-·) (he z hz) (he b hb)
        _ = _ := by ring,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,ENNReal.ofReal_mul ha.le]
  have bound (n : ℕ) (hn : 2 ≤ n) : nthDiameter G n ≤ c * nthDiameter chebSegment n := by
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    have hz' : ∀ i, w (z i) ∈ chebSegment := fun i => hw _ (hz i)
    have H : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, edist (w (z i)) (w (z j))) ^
        (1 / ((n.choose 2 : ℕ):ℝ)) ≤ nthDiameter chebSegment n :=
      le_iSup_of_le (fun i => w (z i)) (le_iSup_of_le hz' le_rfl)
    refine le_trans ?_ (mul_le_mul_right H c)
    have Hprod : (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, edist (z i) (z j)) =
        c^n.choose 2*(∏ i : Fin n, ∏ j ∈ Finset.Ioi i, edist (w (z i)) (w (z j))) := by
      simp_rw [fun i j => hed (z i) (z j) (hz i) (hz j), Finset.prod_mul_distrib]
      rw [prod_prod_Ioi_const]
    rw [Hprod,ENNReal.mul_rpow_of_nonneg _ _ (by positivity),one_div,ENNReal.pow_rpow_inv_natCast (Nat.choose_ne_zero hn)]
  let u (n : ℕ) := (ENNReal.ofReal ((2*(n:ℝ))^n))^(1/((n.choose 2:ℕ):ℝ))
  have hu : Tendsto (fun n => c*u n) atTop (𝓝 c) := by
    simpa [u] using (ENNReal.Tendsto.const_mul cheb_nth_upper_limit (Or.inr (show c ≠ ∞ from ENNReal.ofReal_ne_top)) : Tendsto _ _ _)
  have h : transfiniteDiameter G ≤ c := by
    change limsup _ atTop ≤ _
    rw [← hu.limsup_eq]
    exact limsup_le_limsup ((eventually_ge_atTop (2:ℕ)).mono fun n hn =>
      (bound n hn).trans (mul_le_mul_right (cheb_nth_upper n) c))
  rw [hcap] at h
  have h' : 1 ≤ a := (ENNReal.ofReal_le_ofReal_iff ha.le).1 (by simpa [c] using h)
  dsimp [a] at h'
  linarith
end DoubleInterval
noncomputable section
namespace LemniscateMotion
open Set Filter Metric Polynomial Erdos1042 Erdos1047
open scoped ENNReal

private def motion (c u : ℂ) (hu : u ≠ 0) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ u hu).trans (Homeomorph.addLeft c)

private lemma component_image (e : ℂ ≃ₜ ℂ) (S : Set ℂ) :
    (componentsIn (e '' S)).ncard = (componentsIn S).ncard := by
  have h : componentsIn (e '' S) = (fun T : Set ℂ => e '' T) '' componentsIn S := by
    ext T
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨connectedComponentIn S z,⟨z,hz,rfl⟩,e.image_connectedComponentIn hz⟩
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨e z,mem_image_of_mem _ hz,e.image_connectedComponentIn hz⟩
  rw [h,Set.ncard_image_of_injective _ (Set.image_injective.mpr e.injective)]

private lemma transfer {F G : Set ℂ} {p : ℂ[X]} {n : ℕ} (c u : ℂ) (hunit : ‖u‖ = 1)
    (hin : ∀ z ∈ F, c+u*z ∈ G) (hp : MonicWithRootsIn F n p) (hc : numComponents p=n) :
    ∃ g : ℂ[X], MonicWithRootsIn G n g ∧ numComponents g=n := by
  have hu : u ≠ 0 := norm_ne_zero_iff.mp (hunit.trans_ne one_ne_zero)
  let e := motion c u hu
  let l : ℂ[X] := C u⁻¹ * (X - C c)
  let g : ℂ[X] := C (u^n) * p.comp l
  have hl : l.natDegree = 1 := by simp [l,natDegree_C_mul,hu]
  have hlc : l.leadingCoeff = u⁻¹ := by simp [l, leadingCoeff_mul]
  have hgm : g.Monic := by
    change g.leadingCoeff = 1
    simp [g,leadingCoeff_mul,leadingCoeff_comp (show l.natDegree ≠ 0 by omega),hlc,hp.1.leadingCoeff,hp.2.1,hu]
  have hev (z : ℂ) : g.eval (e z) = u^n * p.eval z := by
    change g.eval (c+u*z) = _
    simp [g,l,eval_comp,hu]
  refine ⟨g, ⟨hgm,?_,?_⟩,?_⟩
  · rw [show g = C (u^n) * p.comp l from rfl, natDegree_C_mul (pow_ne_zero _ hu), natDegree_comp, hl, mul_one, hp.2.1]
  · intro w hw
    let z := e.symm w
    have he : e z = w := e.apply_symm_apply _
    have hz : p.eval z = 0 := by
      have h := (mem_roots hgm.ne_zero).1 hw
      change g.eval w = 0 at h
      rw [←he,hev] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hu)
    rw [←he]
    exact hin _ (hp.2.2 _ ((mem_roots hp.1.ne_zero).2 hz))
  · have him : strictSublevelSet g 1 = e '' strictSublevelSet p 1 := by
      ext w
      obtain ⟨z,rfl⟩ := e.surjective w
      rw [e.injective.mem_set_image]
      change ‖g.eval (e z)‖ < 1 ↔ ‖p.eval z‖ < 1
      rw [hev,norm_mul,norm_pow,hunit,one_pow,one_mul]
    unfold numComponents at hc ⊢
    rw [him,component_image,hc]

end LemniscateMotion
end

private lemma DoubleInterval.gap_exists (G : Set ℂ) (r : ℝ) (hr : 4 ≤ r) (hG : IsCompact G)
    (h0 : (0:ℂ) ∈ G) (hrG : (r:ℂ) ∈ G) (hs : G ⊆ Complex.ofReal '' Icc 0 r)
    (hn : ¬ ∃ c u : ℂ, ‖u‖=1 ∧ ∀ t ∈ Icc (-2:ℝ) 2, c+u*(t:ℂ) ∈ G) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < r ∧
      G ⊆ (Complex.ofReal '' Icc 0 a) ∪ (Complex.ofReal '' Icc b r) := by
  have he : ∃ s : ℝ, s ∈ Icc 0 4 ∧ (s:ℂ) ∉ G := by
    by_contra! h
    apply hn
    refine ⟨2,1,by simp,fun t ht => ?_⟩
    simpa using h (2+t) ⟨by linarith [ht.1],by linarith [ht.2]⟩
  obtain ⟨s,hs',hout⟩ := he
  have hs0 : 0 < s := lt_of_le_of_ne hs'.1 (by rintro rfl; exact hout (by simpa using h0))
  have hsr : s < r := lt_of_le_of_ne (hs'.2.trans hr) (by rintro rfl; exact hout hrG)
  have ho : IsOpen {t : ℝ | (t:ℂ) ∉ G} := hG.isClosed.isOpen_compl.preimage Complex.continuous_ofReal
  obtain ⟨ε,hε,he⟩ := Metric.isOpen_iff.mp ho s hout
  let d := min (min (s/2) ((r-s)/2)) (ε/2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ s/2 := (min_le_left _ _).trans (min_le_left _ _)
  have hd2 : d ≤ (r-s)/2 := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : d ≤ ε/2 := min_le_right _ _
  refine ⟨s-d,s+d,by linarith,by linarith,by linarith,?_⟩
  intro z hz
  obtain ⟨x,hx,rfl⟩ := hs hz
  by_cases hL : x ≤ s-d
  · exact Or.inl ⟨x,⟨hx.1,hL⟩,rfl⟩
  by_cases hR : s+d ≤ x
  · exact Or.inr ⟨x,⟨hR,hx.2⟩,rfl⟩
  have hin : x ∈ Metric.ball s ε := by
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith
  exact (he hin hz).elim


noncomputable section
namespace OMA.R_Erdos1042_erdos_1042_variants_universal_R1_H1_R1
open Set Filter Polynomial Erdos1042

/-- The critical width, with a genuine open gap. -/
def H1 : Prop := ∀ G : Set ℂ, let r : ℝ := 4
    IsCompact G → transfiniteDiameter G = 1 → (0:ℂ) ∈ G → (r:ℂ) ∈ G →
    ∀ a b : ℝ, 0 < a → a < b → b < r →
    G ⊆ (Complex.ofReal '' Icc 0 a) ∪ (Complex.ofReal '' Icc b r) →
    (¬ ∃ c u : ℂ, ‖u‖=1 ∧ ∀ t ∈ Icc (-2:ℝ) 2, c+u*(t:ℂ) ∈ G) →
    (¬ ∃ (c u : ℂ) (t : ℝ), ‖u‖=1 ∧ 3 ≤ t ∧
      ∀ z : ℂ, z^2-(t:ℂ) ∈ Complex.ofReal '' Icc (-2:ℝ) 2 → c+u*z ∈ G) →
    ∃ᶠ n : ℕ in atTop, ∃ f : ℂ[X], MonicWithRootsIn G n f ∧ numComponents f=n

/-- Greater width, excluding sets containing an explicit pair of quadratic inverse intervals. -/
def H2 : Prop := ∀ (G : Set ℂ) (r : ℝ), 4 < r →
    IsCompact G → transfiniteDiameter G = 1 → (0:ℂ) ∈ G → (r:ℂ) ∈ G →
    ∀ a b : ℝ, 0 < a → a < b → b < r →
    G ⊆ (Complex.ofReal '' Icc 0 a) ∪ (Complex.ofReal '' Icc b r) →
    (¬ ∃ c u : ℂ, ‖u‖=1 ∧ ∀ t ∈ Icc (-2:ℝ) 2, c+u*(t:ℂ) ∈ G) →
    (¬ ∃ (c u : ℂ) (t : ℝ), ‖u‖=1 ∧ 3 ≤ t ∧
      ∀ z : ℂ, z^2-(t:ℂ) ∈ Complex.ofReal '' Icc (-2:ℝ) 2 → c+u*z ∈ G) →
    ∃ᶠ n : ℕ in atTop, ∃ f : ℂ[X], MonicWithRootsIn G n f ∧ numComponents f=n

theorem main : H1 → H2 → OMA.R_Erdos1042_erdos_1042_variants_universal_R1.H1 := by
  intro hcrit hwide G r h2 hG hcap hz hrG hsub hseg
  have hr := DoubleInterval.interval_width G r (by linarith) hsub hcap
  obtain ⟨a,b,ha,hab,hb,hgap⟩ := DoubleInterval.gap_exists G r hr hG hz hrG hsub hseg
  by_cases hex : ∃ (c u : ℂ) (t : ℝ), ‖u‖=1 ∧ 3 ≤ t ∧
      ∀ z : ℂ, z^2-(t:ℂ) ∈ Complex.ofReal '' Icc (-2:ℝ) 2 → c+u*z ∈ G
  · obtain ⟨c,u,t,hu,ht,hin⟩ := hex
    rw [frequently_atTop]
    intro k
    let m := k+1
    obtain ⟨f,hf,hcomp⟩ := DoubleInterval.quadratic_family t ht m (by dsimp [m]; omega)
    exact ⟨m*2,by dsimp [m]; omega,LemniscateMotion.transfer c u hu hin hf hcomp⟩
  · rcases eq_or_lt_of_le hr with he | he
    · subst r
      exact hcrit G hG hcap hz hrG a b ha hab hb hgap hseg hex
    · exact hwide G r he hG hcap hz hrG a b ha hab hb hgap hseg hex
end OMA.R_Erdos1042_erdos_1042_variants_universal_R1_H1_R1
end
