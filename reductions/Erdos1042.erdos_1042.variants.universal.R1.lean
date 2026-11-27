import FormalConjectures.ErdosProblems.«1042»
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Data.Nat.Choose.Cast

/-! Rigid motions preserve capacity, roots, monicity and lemniscate component
counts. Chebyshev polynomials resolve sets containing a straight segment of
length four; regular polygons of circumradius at least one yield another
explicit class. Only compact sets normalized at two points remain.
The regular-polygon proof adapts the power-label and root enumeration lemmas
from peilinliu66-dev/jsp865-erdos1042-formalization at
111c3348a9f535d788675e3f75a53cf7cd40c90b, JSP865/ComponentLabels.lean
and JSP865/ExplicitRootComponents.lean.
Copyright (c) 2026. Independently authored JSP865 source.
SPDX-License-Identifier: Apache-2.0.
The Chebyshev witness and the finite
Fekete-product compactness argument are adapted from @Genbox at
1aa4f45ad130335f4061714cc0c74c2b865116e8 and b86a4bdab6fdd064bb2d2cea7f4173586f0a518a. -/
-- Credit: @marcusbuffett


section
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

private theorem OMA.cheb_comp_count (n : ℕ) (hn : 1 ≤ n) :
    Erdos1042.numComponents (cheb n) = n := by
  classical
  let U := Erdos1047.strictSublevelSet (cheb n) 1
  let F (i : Fin n) := connectedComponentIn U (chebPoint n i)
  have hroot (i : Fin n) : chebPoint n i ∈ U := by
    change ‖(cheb n).eval (chebPoint n i)‖ < 1
    simp [cheb_point_eval_zero]
  have hbound : Bornology.IsBounded U := by
    refine Metric.isBounded_ball.subset (t := Metric.ball (0 : ℂ) 4) ?_
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    by_contra! hlarge
    have hge : 1 ≤ ‖(cheb n).eval z‖ := by
      rw [cheb_eval_prod, norm_prod]
      apply Finset.one_le_prod
      intro i _
      have ha : ‖chebPoint n i‖ ≤ 2 := by
        rw [chebPoint, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have hc := Real.abs_cos_le_one (chebAngle n i)
        linarith
      have hi := norm_add_le (z - chebPoint n i) (chebPoint n i)
      rw [sub_add_cancel] at hi
      linarith
    exact (not_lt_of_ge hge) hz
  have hcover : Erdos1047.componentsIn U = Set.range F := by
    ext C
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, hr, hz0⟩ := cheb_strict_component_root (cheb n)
        (by rw [(cheb_degree_monic n).1]; omega) (c := 1) zero_lt_one hbound hz
      have hmem : r ∈ (cheb n).roots := (mem_roots (cheb_degree_monic n).2.ne_zero).2 hz0
      rw [cheb_roots] at hmem
      change r ∈ Finset.univ.image (chebPoint n) at hmem
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      refine ⟨i, ?_⟩
      change connectedComponentIn U (chebPoint n i) = _
      rw [hi]
      exact (connectedComponentIn_eq hr).symm
    · rintro ⟨i, rfl⟩
      exact ⟨chebPoint n i, hroot i, rfl⟩
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
  unfold Erdos1042.numComponents
  change (Erdos1047.componentsIn U).ncard = n
  rw [hcover, Set.ncard_range_of_injective hinj]
  simp


private theorem OMA.segmentWitness (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : ℂ[X], Erdos1042.MonicWithRootsIn chebSegment n f ∧ Erdos1042.numComponents f = n := by
  refine ⟨cheb n, ⟨(cheb_degree_monic n).2, (cheb_degree_monic n).1, ?_⟩, cheb_comp_count n hn⟩
  intro z hz
  rw [cheb_roots] at hz
  change z ∈ Finset.univ.image (chebPoint n) at hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
  exact cheb_point_mem n i
end

noncomputable section
namespace RegularPolygon
open Set Polynomial
/-- The principal logarithm is continuous on the right-half-plane power locus. -/
private def positivePowerLocus (M : ℕ) : Set ℂ := {z | 0 < (z ^ M).re}

private def powerLabel (M : ℕ) (z : ℂ) : ℂ :=
  z / Complex.exp (Complex.log (z ^ M) / (M : ℂ))

private lemma continuousOn_powerLabel (M : ℕ) :
    ContinuousOn (powerLabel M) (positivePowerLocus M) := by
  have hlog : ContinuousOn (fun z : ℂ => Complex.log (z ^ M)) (positivePowerLocus M) :=
    (continuousOn_id.pow M).clog (fun _ hz => Or.inl hz)
  have hexp := Complex.continuous_exp.comp_continuousOn (hlog.div_const (M : ℂ))
  exact continuousOn_id.div hexp (fun _ _ => Complex.exp_ne_zero _)

private lemma powerLabel_pow {M : ℕ} (hM : M ≠ 0) {z : ℂ}
    (hz : z ∈ positivePowerLocus M) : powerLabel M z ^ M = 1 := by
  have hpow : z ^ M ≠ 0 := by
    intro h
    have hpos : 0 < (z ^ M).re := hz
    rw [h] at hpos
    simpa using hpos
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM
  have hcancel : (M : ℂ) * (Complex.log (z ^ M) / (M : ℂ)) =
      Complex.log (z ^ M) := by field_simp [hMc] <;> ring
  rw [powerLabel, div_pow, ← Complex.exp_nat_mul, hcancel,
    Complex.exp_log hpow, div_self hpow]

private lemma finite_unity_locus {M : ℕ} (hM : M ≠ 0) :
    Set.Finite {z : ℂ | z ^ M = 1} := by
  have hp : (Polynomial.X ^ M - Polynomial.C (1 : ℂ)) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C (1 : ℂ) hM).ne_zero
  simpa only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] using
      Polynomial.finite_setOfPred_isRoot hp

private lemma powerLabel_constant {M : ℕ} (hM : M ≠ 0) {S : Set ℂ}
    (hS : IsPreconnected S) (hpos : S ⊆ positivePowerLocus M)
    {z w : ℂ} (hz : z ∈ S) (hw : w ∈ S) : powerLabel M z = powerLabel M w := by
  exact hS.constant_of_mapsTo (finite_unity_locus hM).isDiscrete
    ((continuousOn_powerLabel M).mono hpos)
    (fun x hx => powerLabel_pow hM (hpos hx)) hz hw

private lemma powerLabel_injective_on_power_fibre (M : ℕ) {z w : ℂ}
    (hpow : z ^ M = w ^ M) (hlabel : powerLabel M z = powerLabel M w) : z = w := by
  unfold powerLabel at hlabel
  rw [hpow] at hlabel
  exact (div_left_inj' (Complex.exp_ne_zero _)).mp hlabel

private def circleRoot (d : ℝ) (M : ℕ) (i : Fin M) : ℂ :=
  (d : ℂ) * Complex.exp (2 * Real.pi * Complex.I / M) ^ i.val

private lemma circleRoot_pow (d : ℝ) {M : ℕ} (hM : M ≠ 0) (i : Fin M) :
    circleRoot d M i ^ M = (d : ℂ) ^ M := by
  have hζ := Complex.isPrimitiveRoot_exp M hM
  rw [circleRoot, mul_pow, ← pow_mul, Nat.mul_comm i.val M, pow_mul,
    hζ.pow_eq_one, one_pow, mul_one]

private lemma circleRoot_injective {d : ℝ} (hd : 0 < d) {M : ℕ} (hM : M ≠ 0) :
    Function.Injective (circleRoot d M) := by
  intro i j h
  have hdc : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
  apply Fin.ext
  apply (Complex.isPrimitiveRoot_exp M hM).pow_inj i.isLt j.isLt
  exact mul_left_cancel₀ hdc h

private lemma circle_case (n : ℕ) (hn : 0 < n) (s : ℝ) (hs : 1 ≤ s) :
    ∃ p : ℂ[X], Erdos1042.MonicWithRootsIn {z : ℂ | z^n=(s:ℂ)^n} n p ∧ Erdos1042.numComponents p = n := by
  classical
  let p := (X : ℂ[X])^n - C ((s:ℂ)^n)
  let v := circleRoot s n
  have hmon : p.Monic := monic_X_pow_sub_C _ hn.ne'
  have hdeg : p.natDegree = n := natDegree_X_pow_sub_C
  have hev (z : ℂ) : p.eval z = z^n - (s:ℂ)^n := by simp [p]
  have hr (i : Fin n) : (v i)^n = (s:ℂ)^n := circleRoot_pow _ hn.ne' i
  have hv : Function.Injective v := circleRoot_injective (by linarith) hn.ne'
  have hroots : p.roots = (Finset.univ.image v).val := by
    apply roots_eq_of_degree_eq_card
    · rintro z hz
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hz
      exact (hev _).trans (sub_eq_zero.mpr (hr i))
    · rw [Finset.card_image_of_injective _ hv,Finset.card_univ,Fintype.card_fin,degree_eq_natDegree hmon.ne_zero,hdeg]
  let U := Erdos1047.strictSublevelSet p 1
  let A (i : Fin n) := connectedComponentIn U (v i)
  have hin (i : Fin n) : v i ∈ U := by
    change ‖p.eval _‖ < 1
    rw [hev, hr,sub_self,norm_zero]; norm_num
  have hbound : Bornology.IsBounded U := by
    refine Metric.isBounded_ball.subset (t:=Metric.ball (0:ℂ) (s^n+2)) ?_
    intro z hz
    rw [Metric.mem_ball,dist_zero_right]
    have hsmall : ‖z^n-(s:ℂ)^n‖ < 1 := by simpa only [U,Erdos1047.strictSublevelSet,Set.mem_setOf_eq,hev] using hz
    have hb := norm_add_le (z^n-(s:ℂ)^n) ((s:ℂ)^n)
    rw [sub_add_cancel,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ s)] at hb
    by_cases he : 1 ≤ ‖z‖
    · linarith [le_self_pow₀ he hn.ne']
    · linarith [one_le_pow₀ hs (n:=n)]
  have hcover : Erdos1047.componentsIn U = Set.range A := by
    ext T
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨w,hw,hzero⟩ := OMA.cheb_strict_component_root p (hdeg ▸ hn) (c:=1) zero_lt_one hbound hz
      have hm := (mem_roots hmon.ne_zero).2 hzero
      rw [hroots] at hm
      change w ∈ Finset.univ.image v at hm
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hm
      exact ⟨i,(connectedComponentIn_eq hw).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨v i,hin i,rfl⟩
  have hpos : U ⊆ positivePowerLocus n := by
    intro z hz
    have hsmall : ‖z^n-(s:ℂ)^n‖ < 1 := by simpa only [U,Erdos1047.strictSublevelSet,Set.mem_setOf_eq,hev] using hz
    have hb := (Complex.abs_re_le_norm (z^n-(s:ℂ)^n)).trans_lt hsmall
    rw [Complex.sub_re,← Complex.ofReal_pow,Complex.ofReal_re,abs_lt] at hb
    change 0 < (z^n).re
    linarith [hb.1,one_le_pow₀ hs (n:=n)]
  have hinj : Function.Injective A := by
    intro i j h
    have hi : v i ∈ A i := mem_connectedComponentIn (hin i)
    have hj : v j ∈ A i := h ▸ mem_connectedComponentIn (hin j)
    apply hv
    exact powerLabel_injective_on_power_fibre n ((hr i).trans (hr j).symm)
      (powerLabel_constant hn.ne' isPreconnected_connectedComponentIn ((connectedComponentIn_subset _ _).trans hpos) hi hj)
  refine ⟨p,⟨hmon,hdeg,?_⟩,?_⟩
  · intro z hz
    have hb := (mem_roots hmon.ne_zero).1 hz
    change p.eval z = 0 at hb
    exact sub_eq_zero.mp ((hev z).symm.trans hb)
  · change (Erdos1047.componentsIn U).ncard = n
    rw [hcover,Set.ncard_range_of_injective hinj]
    simp
end RegularPolygon
end


section
open scoped BigOperators ENNReal
open Finset
namespace LemniscateSampling

private def indexPairs (N : ℕ) : Finset (Σ _ : Fin N, Fin N) :=
  Finset.univ.sigma fun i => Finset.Ioi i

private theorem mem_indexPairs {N : ℕ} (p : Σ _ : Fin N, Fin N) :
    p ∈ indexPairs N ↔ p.1 < p.2 := by
  simp [indexPairs]
private theorem bounded_of_product_bound {F : Set ℂ} {N : ℕ} (hN : 2 ≤ N)
    {Q : ℝ} (hQ : 0 < Q)
    (hprod : ∀ x : Fin N → ℂ, (∀ i, x i ∈ F) →
      (∏ p ∈ indexPairs N, dist (x p.1) (x p.2)) ≤ Q) :
    Bornology.IsBounded F := by
  classical
  by_contra hbounded
  have hinfinite : F.Infinite := fun h => hbounded h.isCompact.isBounded
  let e := Set.Infinite.natEmbedding F hinfinite
  let a (i : Fin N) : ℂ := (e i : F)
  have ha : Function.Injective a := fun i j hij =>
    Fin.ext (e.injective (Subtype.ext hij))
  let u : Fin N := ⟨0, by omega⟩
  let v : Fin N := ⟨1, by omega⟩
  let p : Σ _ : Fin N, Fin N := ⟨u, v⟩
  have hu : u ≠ v := by simp [u, v, Fin.ext_iff]
  have hp : p ∈ indexPairs N := (mem_indexPairs p).2 (by norm_num [p, u, v, Fin.lt_def])
  let P := ∏ j ∈ (indexPairs N).erase p, dist (a j.1) (a j.2)
  have hP : 0 < P := by
    apply Finset.prod_pos
    intro j hj
    exact dist_pos.mpr (ha.ne ((mem_indexPairs j).1 (Finset.mem_of_mem_erase hj)).ne)
  let D := ∑ i : Fin N, ‖a i‖
  have hD (i : Fin N) : ‖a i‖ ≤ D :=
    Finset.single_le_sum (fun j _ => norm_nonneg (a j)) (Finset.mem_univ i)
  have hDpos : 0 ≤ D := (norm_nonneg (a u)).trans (hD u)
  have hQp : 0 < Q / P := div_pos hQ hP
  apply hbounded
  refine (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).2 ⟨Q/P + 3*D, ?_⟩
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hzlarge
  let x (i : Fin N) : ℂ := if i = u then z else a i
  have hx (i : Fin N) : x i ∈ F := by
    by_cases hi : i = u
    · simpa only [x, if_pos hi] using hz
    · simpa only [x, if_neg hi] using (e i).property
  have hlong (i : Fin N) : Q/P + 2*D < dist z (a i) := by
    have ht : ‖z‖ ≤ dist z (a i) + ‖a i‖ := by
      rw [dist_eq_norm]
      simpa only [sub_add_cancel] using norm_add_le (z-a i) (a i)
    linarith only [hzlarge, ht, hD i]
  have hshort (i j : Fin N) : dist (a i) (a j) ≤ 2*D := by
    have ht := dist_triangle (a i) 0 (a j)
    rw [dist_zero_right, dist_zero_left] at ht
    linarith only [ht, hD i, hD j]
  have hremain : P ≤ ∏ j ∈ (indexPairs N).erase p, dist (x j.1) (x j.2) := by
    refine Finset.prod_le_prod (fun _ _ => dist_nonneg) ?_
    intro j hj
    have hne := ((mem_indexPairs j).1 (mem_of_mem_erase hj)).ne
    by_cases hi : j.1 = u
    · have hj' : j.2 ≠ u := fun h => hne (hi.trans h.symm)
      simp only [x, if_pos hi, if_neg hj']
      linarith only [hshort j.1 j.2, hlong j.2, hQp]
    · by_cases hj' : j.2 = u
      · simp only [x, if_neg hi, if_pos hj']
        rw [dist_comm (a j.1) z]
        linarith only [hshort j.1 j.2, hlong j.1, hQp]
      · simp only [x, if_neg hi, if_neg hj', le_refl]
  have hpdist : dist (x p.1) (x p.2) = dist z (a v) := by
    simp only [p, x, if_pos rfl, if_neg hu.symm]
  have hprod' := hprod x hx
  rw [← Finset.mul_prod_erase (indexPairs N) (fun j => dist (x j.1) (x j.2)) hp,
    hpdist] at hprod'
  have hqp : Q < dist z (a v) * P :=
    (div_lt_iff₀ hP).1 (by linarith only [hlong v, hDpos])
  exact (not_lt_of_ge hprod') (hqp.trans_le (mul_le_mul_of_nonneg_left hremain dist_nonneg))


private theorem finite_capacity_bounded (F : Set ℂ) (hf : Erdos1042.transfiniteDiameter F = 1) : Bornology.IsBounded F := by
  have hlt : Erdos1042.transfiniteDiameter F < 2 := by rw [hf]; norm_num
  have he : ∀ᶠ N : ℕ in Filter.atTop, Erdos1042.nthDiameter F N < 2 :=
    Filter.eventually_lt_of_limsup_lt hlt
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 (he.and (Filter.eventually_ge_atTop (2:ℕ)))
  have hn := (hN N le_rfl).2
  apply bounded_of_product_bound hn (Q := (2:ℝ)^(N.choose 2)) (by positivity)
  intro x hx
  have hm : 0 < N.choose 2 := Nat.choose_pos (hN N le_rfl).2
  have hmR : (N.choose 2 : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  let P := ∏ p ∈ indexPairs N, dist (x p.1) (x p.2)
  have hP : ENNReal.ofReal P =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, edist (x i) (x j) := by
    dsimp only [P, indexPairs]
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => dist_nonneg), Finset.prod_sigma]
    simp only [edist_dist]
  have hle : ENNReal.ofReal P ^ (1 / (N.choose 2 : ℝ)) ≤ (2:ℝ≥0∞) := by
    rw [hP]
    refine le_trans ?_ (hN N le_rfl).1.le
    exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  have hpow := pow_le_pow_left' hle (N.choose 2)
  rw [← ENNReal.rpow_mul_natCast, div_mul_cancel₀ _ hmR, ENNReal.rpow_one] at hpow
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  simpa [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)] using hpow

end LemniscateSampling
end
noncomputable section
namespace LemniscateMotion
open Set Filter Metric Polynomial Erdos1042 Erdos1047
open scoped ENNReal

private def motion (c u : ℂ) (hu : u ≠ 0) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ u hu).trans (Homeomorph.addLeft c)

private lemma motion_iso (c u : ℂ) (hu : ‖u‖ = 1) :
    Isometry (motion c u (norm_ne_zero_iff.mp (hu.trans_ne one_ne_zero))) := by
  apply Isometry.of_dist_eq
  intro z w
  change dist (c+u*z) (c+u*w) = _
  rw [dist_add_left,dist_eq_norm,←mul_sub,norm_mul,hu,one_mul,dist_eq_norm]

private lemma diameter_le_map {F G : Set ℂ} (e : ℂ → ℂ) (he : Isometry e)
    (hmap : MapsTo e F G) (n : ℕ) : nthDiameter F n ≤ nthDiameter G n := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  refine le_trans ?_ (le_iSup_of_le (fun i => e (z i)) (le_iSup_of_le (fun i => hmap (hz i)) le_rfl))
  simp_rw [he.edist_eq]
  rfl

private lemma capacity_motion {e : ℂ ≃ₜ ℂ} (he : Isometry e) (G : Set ℂ) :
    transfiniteDiameter (e '' G) = transfiniteDiameter G := by
  have hi : Isometry e.symm := by
    intro z w
    simpa using (he.edist_eq (e.symm z) (e.symm w)).symm
  have hn (n : ℕ) : nthDiameter (e '' G) n = nthDiameter G n := by
    apply le_antisymm
    · exact diameter_le_map e.symm hi (by rintro _ ⟨z,h,rfl⟩; simpa using h) n
    · exact diameter_le_map e he (fun z h => mem_image_of_mem _ h) n
  unfold transfiniteDiameter
  simp_rw [hn]

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

noncomputable section
namespace OMA.R_Erdos1042_erdos_1042_variants_universal_R1
open Erdos1042 Erdos1047 Polynomial Filter Set Metric LemniscateMotion

/-- A compact collinear set, placed on the real axis with diameter endpoints
0 and r. A full length-four segment has already been handled. -/
def H1 : Prop := ∀ (G : Set ℂ) (r : ℝ), 2 < r → IsCompact G → transfiniteDiameter G = 1 →
  (0:ℂ) ∈ G → (r:ℂ) ∈ G → G ⊆ Complex.ofReal '' Icc 0 r →
  (¬ ∃ c u : ℂ, ‖u‖=1 ∧ ∀ t ∈ Icc (-2:ℝ) 2, c+u*(t:ℂ) ∈ G) →
  ∃ᶠ n : ℕ in atTop, ∃ f : ℂ[X], MonicWithRootsIn G n f ∧ numComponents f=n

/-- The noncollinear case, with diameter endpoints fixed and the two explicit
families of root configurations excluded. -/
def H2 : Prop := ∀ (G : Set ℂ) (r : ℝ), 1 < r → IsCompact G → transfiniteDiameter G = 1 →
  (0:ℂ) ∈ G → (r:ℂ) ∈ G → (∀ z ∈ G, ∀ w ∈ G, dist z w ≤ r) →
  (∃ z ∈ G, z.im ≠ 0) → (∀ c : ℂ, ¬ G ⊆ closedBall c 1) →
  (¬ ∃ c u : ℂ, ‖u‖=1 ∧ ∀ t ∈ Icc (-2:ℝ) 2, c+u*(t:ℂ) ∈ G) →
  (¬ ∃ᶠ n : ℕ in atTop, ∃ (c u : ℂ) (s : ℝ), ‖u‖=1 ∧ 1 ≤ s ∧
    ∀ z : ℂ, z^n=(s:ℂ)^n → c+u*z ∈ G) →
  ∃ᶠ n : ℕ in atTop, ∃ f : ℂ[X], MonicWithRootsIn G n f ∧ numComponents f=n

section
private lemma seg_case {G : Set ℂ} (c u : ℂ) (hu : ‖u‖=1)
    (h : ∀ t ∈ Icc (-2:ℝ) 2, c+u*(t:ℂ) ∈ G) :
    ∃ᶠ n : ℕ in atTop, ∃ f : ℂ[X], MonicWithRootsIn G n f ∧ numComponents f=n := by
  apply Filter.Eventually.frequently
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  obtain ⟨p,hp,hc⟩ := OMA.segmentWitness n hn
  exact transfer c u hu (by rintro _ ⟨t,ht,rfl⟩; exact h t ht) hp hc

private lemma regular_case {G : Set ℂ} (h : ∃ᶠ n : ℕ in atTop, ∃ (c u : ℂ) (s : ℝ),
    ‖u‖=1 ∧ 1 ≤ s ∧ ∀ z : ℂ, z^n=(s:ℂ)^n → c+u*z ∈ G) :
    ∃ᶠ n : ℕ in atTop, ∃ f : ℂ[X], MonicWithRootsIn G n f ∧ numComponents f=n := by
  apply ((eventually_gt_atTop (0:ℕ)).and_frequently h).mono
  rintro n ⟨hn,c,u,s,hu,hs,hmem⟩
  obtain ⟨p,hp,hcc⟩ := RegularPolygon.circle_case n hn s hs
  exact transfer c u hu (fun z hz => hmem z hz) hp hcc

end

theorem main : H1 → H2 → type_of% @Erdos1042.erdos_1042.variants.universal := by
  intro realCase planeCase F hclosed hcap hdisc
  have hco := Metric.isCompact_of_isClosed_isBounded hclosed (LemniscateSampling.finite_capacity_bounded F hcap)
  obtain ⟨f,hf,_⟩ := Set.not_subset.mp (hdisc 0)
  have hne : F.Nonempty := ⟨f,hf⟩
  obtain ⟨⟨a,b⟩,⟨ha,hb⟩,hmax⟩ := (hco.prod hco).exists_isMaxOn (hne.prod hne)
    (continuous_dist.continuousOn : ContinuousOn (fun q : ℂ × ℂ => dist q.1 q.2) (F ×ˢ F))
  let r := ‖b-a‖
  have hab : dist a b = r := by rw [dist_comm,dist_eq_norm]
  have hbnd {z w : ℂ} (hz : z ∈ F) (hw : w ∈ F) : dist z w ≤ r :=
    (isMaxOn_iff.mp hmax (z,w) ⟨hz,hw⟩).trans_eq hab
  have hr : 1 < r := by
    by_contra! H
    exact hdisc a (fun z hz => (hbnd hz ha).trans H)
  have hr0 : r ≠ 0 := by linarith
  have hrC : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0
  let u := (b-a)/(r:ℂ)
  have hu : ‖u‖ = 1 := by
    rw [show ‖u‖ = ‖b-a‖ / ‖(r:ℂ)‖ by exact norm_div _ _, Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (show 0<r by linarith)]
    exact div_self hr0
  have hu0 := norm_ne_zero_iff.mp (hu.trans_ne one_ne_zero)
  let e := motion a u hu0
  let G := e ⁻¹' F
  have he : Isometry e := motion_iso a u hu
  have him : e '' G = F := e.image_preimage F
  have Gco : IsCompact G := e.isClosedEmbedding.isCompact_preimage hco
  have Gcap : transfiniteDiameter G = 1 := (capacity_motion he G).symm.trans (him ▸ hcap)
  have Gzero : (0:ℂ) ∈ G := by change a+u*0 ∈ F; simpa using ha
  have Gr : (r:ℂ) ∈ G := by change a+((b-a)/(r:ℂ))*r ∈ F; simpa [hrC] using hb
  have Gdist {z w : ℂ} (hz : z ∈ G) (hw : w ∈ G) : dist z w ≤ r :=
    (he.dist_eq z w).symm.trans_le (hbnd hz hw)
  have Gdisk (z : ℂ) : ¬ G ⊆ closedBall z 1 := by
    intro hs
    apply hdisc (e z)
    intro w hw
    obtain ⟨y,hy,rfl⟩ : w ∈ e '' G := him ▸ hw
    exact (he.dist_eq y z).trans_le (hs hy)
  suffices hh : ∃ᶠ n : ℕ in atTop, ∃ f : ℂ[X], MonicWithRootsIn G n f ∧ numComponents f=n by
    exact hh.mono fun n ⟨p,hp,hc⟩ => transfer a u hu (fun z hz => hz) hp hc
  by_cases hseg : ∃ c u : ℂ, ‖u‖=1 ∧ ∀ t ∈ Icc (-2:ℝ) 2, c+u*(t:ℂ) ∈ G
  · obtain ⟨c,v,hv,h⟩ := hseg
    exact seg_case c v hv h
  by_cases hreg : ∃ᶠ n : ℕ in atTop, ∃ (c u : ℂ) (s : ℝ), ‖u‖=1 ∧ 1 ≤ s ∧
      ∀ z : ℂ, z^n=(s:ℂ)^n → c+u*z ∈ G
  · exact regular_case hreg
  by_cases hplane : ∃ z ∈ G, z.im ≠ 0
  · exact planeCase G r hr Gco Gcap Gzero Gr (fun _ hz _ hw => Gdist hz hw) hplane Gdisk hseg hreg
  have Gline : G ⊆ Complex.ofReal '' Icc 0 r := by
    intro z hz
    have hi : z.im = 0 := by by_contra h; exact hplane ⟨z,hz,h⟩
    have hreal : (z.re:ℂ) = z := Complex.ext rfl (by simpa using hi.symm)
    have h₀ := Gdist hz Gzero
    have h₁ := Gdist hz Gr
    rw [←hreal,dist_zero_right,Complex.norm_real,Real.norm_eq_abs] at h₀
    rw [←hreal,Complex.dist_of_im_eq (by rfl),Real.dist_eq,Complex.ofReal_re,Complex.ofReal_re] at h₁
    exact ⟨z.re,⟨by linarith [(abs_le.mp h₁).1],(abs_le.mp h₀).2⟩,hreal⟩
  have hr2 : 2 < r := by
    by_contra! H
    apply Gdisk ((r/2 : ℝ) : ℂ)
    intro z hz
    obtain ⟨t,ht,rfl⟩ := Gline hz
    rw [mem_closedBall,Complex.dist_of_im_eq (by rfl),Real.dist_eq,Complex.ofReal_re,Complex.ofReal_re,abs_le]
    constructor <;> linarith [ht.1,ht.2]
  exact realCase G r hr2 Gco Gcap Gzero Gr Gline hseg
end OMA.R_Erdos1042_erdos_1042_variants_universal_R1
end

