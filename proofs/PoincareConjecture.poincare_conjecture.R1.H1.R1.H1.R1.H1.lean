import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.R1.H1.R1.H1.R1.H1: hypothesis H1 of reduction
-- PoincareConjecture.poincare_conjecture.R1.H1.R1.H1.R1
-- Credit: @ivillar
--
-- REUSE. The contractibility of a punctured sphere via stereographic projection follows
-- `punctured_simplyConnected` of the merged proof
-- proofs/PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R1.H3.lean (PR #3619,
-- same owner), which adapts proofs/PoincareConjecture.poincare_conjecture.variants.dimension_two.R1.H3.lean
-- by @dk8827 (PR #1958); `radial` and its lemmas are from the same file.

/-!
Cover `S³` by the complements `A`, `B` of the two poles `±N`. Each is homeomorphic to `ℝ³` by
stereographic projection, hence contractible. Let `pr : ℝ⁴ → ℝ³` be the orthogonal projection onto
`N^⊥` followed by an isometry `N^⊥ ≃ ℝ³`, and `inc` its isometric section. On `A ∩ B` the projection
`pr x` never vanishes, so `x ↦ pr x / ‖pr x‖` maps `A ∩ B` to `S²`, with homotopy inverse `inc`:
`pr ∘ inc = id`, and `inc (pr x / ‖pr x‖) ≃ x` by the normalized straight-line homotopy, whose
projection `((1 - t) / ‖pr x‖ + t) • pr x` never vanishes.
-/

open Metric

namespace OMA.PoincareCoverH1

abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev S3 := sphere (0 : E4) 1
abbrev S2 := sphere (0 : E3) 1

noncomputable def radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) : E :=
  ‖y‖⁻¹ • y

theorem radial_mem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E) (hy : y ≠ 0) :
    radial y ∈ sphere (0 : E) 1 := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  rw [mem_sphere_zero_iff_norm, radial, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), inv_mul_cancel₀ hn.ne']

theorem radial_of_norm_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (y : E)
    (h : ‖y‖ = 1) : radial y = y := by
  rw [radial, h, inv_one, one_smul]

theorem radial_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousOn (radial (E := E)) ({0}ᶜ : Set E) :=
  (continuous_norm.continuousOn.inv₀
    (fun _ hy => norm_ne_zero_iff.2 (by simpa using hy))).smul continuous_id.continuousOn

noncomputable def nv : E4 := EuclideanSpace.single 3 1

theorem nv_norm : ‖nv‖ = 1 := by simp [nv]

theorem nv_ne : nv ≠ 0 := fun h => by simpa [h] using nv_norm

noncomputable abbrev K : Submodule ℝ E4 := (ℝ ∙ nv)ᗮ

instance factE4 : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

noncomputable def Φ : K ≃ₗᵢ[ℝ] E3 := (OrthonormalBasis.fromOrthogonalSpanSingleton 3 nv_ne).repr

noncomputable def pr : E4 →L[ℝ] E3 :=
  (Φ.toContinuousLinearEquiv : K →L[ℝ] E3).comp K.orthogonalProjectionOnto

noncomputable def inc (v : E3) : E4 := ((Φ.symm v : K) : E4)

theorem inc_continuous : Continuous inc :=
  continuous_subtype_val.comp Φ.symm.continuous

theorem pr_inc (v : E3) : pr (inc v) = v := by
  simp [pr, inc]

theorem norm_inc (v : E3) : ‖inc v‖ = ‖v‖ :=
  Φ.symm.norm_map v

theorem pr_nv : pr nv = 0 := by
  have h : K.orthogonalProjectionOnto nv = 0 := by
    rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
    exact Submodule.le_orthogonal_orthogonal _ (Submodule.mem_span_singleton_self nv)
  simp [pr, h]

theorem eq_of_pr_eq_zero {x : E4} (hx : ‖x‖ = 1) (h : pr x = 0) : x = nv ∨ x = -nv := by
  have h1 : K.orthogonalProjectionOnto x = 0 := by
    have h2 := congrArg Φ.symm h
    simpa [pr] using h2
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff, Submodule.orthogonal_orthogonal] at h1
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h1
  rw [norm_smul, nv_norm, mul_one, Real.norm_eq_abs] at hx
  rcases (abs_eq zero_le_one).mp hx with hc | hc
  · left; rw [hc, one_smul]
  · right; rw [hc, neg_one_smul]

noncomputable def Np : S3 := ⟨nv, by simp [nv_norm]⟩
noncomputable def Sp : S3 := ⟨-nv, by simp [nv_norm]⟩

def A : Set S3 := {Np}ᶜ
def B : Set S3 := {Sp}ᶜ

theorem Np_ne_Sp : Np ≠ Sp := by
  intro h
  have h2 := congrArg (fun z : S3 => (z : E4) 3) h
  simp [Np, Sp, nv] at h2
  norm_num at h2

theorem pr_ne_of_mem {x : S3} (hx : x ∈ A ∩ B) : pr (x : E4) ≠ 0 := by
  intro h
  rcases eq_of_pr_eq_zero (norm_eq_of_mem_sphere x) h with h' | h'
  · exact hx.1 (Subtype.ext h')
  · exact hx.2 (Subtype.ext h')

theorem mem_of_pr_ne {x : S3} (h : pr (x : E4) ≠ 0) : x ∈ A ∩ B := by
  refine ⟨fun hx => h ?_, fun hx => h ?_⟩
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact pr_nv
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    show pr (-nv) = 0
    rw [map_neg, pr_nv, neg_zero]

noncomputable def fmap : C(↥(A ∩ B), S2) where
  toFun x := ⟨radial (pr x.1.1), radial_mem _ (pr_ne_of_mem x.2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact radial_continuousOn.comp_continuous
      (pr.continuous.comp (continuous_subtype_val.comp continuous_subtype_val))
      (fun x => pr_ne_of_mem x.2)

noncomputable def gmap : C(S2, ↥(A ∩ B)) where
  toFun v := ⟨⟨inc v.1, by rw [mem_sphere_zero_iff_norm, norm_inc]; exact norm_eq_of_mem_sphere v⟩,
    mem_of_pr_ne (by
      show pr (inc v.1) ≠ 0
      rw [pr_inc]
      exact ne_of_mem_sphere v.2 one_ne_zero)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact inc_continuous.comp continuous_subtype_val

theorem fg : fmap.comp gmap = ContinuousMap.id S2 := by
  refine ContinuousMap.ext fun v => Subtype.ext ?_
  show radial (pr (inc v.1)) = v.1
  rw [pr_inc, radial_of_norm_one _ (norm_eq_of_mem_sphere v)]

noncomputable def wv (t : ℝ) (x : ↥(A ∩ B)) : E4 := (1 - t) • inc (fmap x).1 + t • x.1.1

theorem pr_wv (t : ℝ) (x : ↥(A ∩ B)) :
    pr (wv t x) = ((1 - t) * ‖pr x.1.1‖⁻¹ + t) • pr x.1.1 := by
  have h : pr (inc (fmap x).1) = ‖pr x.1.1‖⁻¹ • pr x.1.1 := pr_inc _
  rw [wv, map_add, map_smul, map_smul, h, smul_smul, add_smul]

theorem pr_wv_ne (t : unitInterval) (x : ↥(A ∩ B)) : pr (wv t x) ≠ 0 := by
  rw [pr_wv]
  have hp := pr_ne_of_mem x.2
  have hn : 0 < ‖pr x.1.1‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hp)
  have ht0 := t.2.1
  have ht1 := t.2.2
  have hc : 0 < (1 - (t:ℝ)) * ‖pr x.1.1‖⁻¹ + t := by
    rcases eq_or_lt_of_le ht0 with h | h
    · rw [← h]; simpa using hn
    · nlinarith [mul_nonneg (sub_nonneg.2 ht1) hn.le]
  exact smul_ne_zero hc.ne' hp

theorem wv_ne (t : unitInterval) (x : ↥(A ∩ B)) : wv t x ≠ 0 :=
  fun h => pr_wv_ne t x (by rw [h, map_zero])

theorem wv_continuous : Continuous (fun p : unitInterval × ↥(A ∩ B) => wv p.1 p.2) := by
  have hf : Continuous (fun x : ↥(A ∩ B) => inc (fmap x).1) :=
    inc_continuous.comp (continuous_subtype_val.comp fmap.continuous)
  have hx : Continuous (fun x : ↥(A ∩ B) => x.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have ht : Continuous (fun p : unitInterval × ↥(A ∩ B) => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  unfold wv
  exact ((continuous_const.sub ht).smul (hf.comp continuous_snd)).add (ht.smul (hx.comp continuous_snd))

noncomputable def Hmap (p : unitInterval × ↥(A ∩ B)) : ↥(A ∩ B) :=
  ⟨⟨radial (wv p.1 p.2), radial_mem _ (wv_ne p.1 p.2)⟩, mem_of_pr_ne (by
      show pr (radial (wv p.1 p.2)) ≠ 0
      rw [radial, map_smul]
      exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.2 (wv_ne _ _))) (pr_wv_ne _ _))⟩

noncomputable def H : ContinuousMap.Homotopy (gmap.comp fmap) (ContinuousMap.id _) where
  toFun := Hmap
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact radial_continuousOn.comp_continuous wv_continuous (fun p => wv_ne p.1 p.2)
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    show radial (wv 0 x) = inc (fmap x).1
    have h1 : wv 0 x = inc (fmap x).1 := by simp [wv]
    rw [h1, radial_of_norm_one _ (by rw [norm_inc]; exact norm_eq_of_mem_sphere (fmap x))]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    show radial (wv 1 x) = x.1.1
    have h1 : wv 1 x = x.1.1 := by simp [wv]
    rw [h1, radial_of_norm_one _ (norm_eq_of_mem_sphere x.1)]

theorem contractible_compl (y : S3) : ContractibleSpace ↥(({y} : Set S3)ᶜ) := by
  let e := stereographic (norm_eq_of_mem_sphere y)
  have hs : e.source = ({y} : Set S3)ᶜ := stereographic_source (norm_eq_of_mem_sphere y)
  have ht : e.target = Set.univ := stereographic_target (norm_eq_of_mem_sphere y)
  let h := (Homeomorph.setCongr hs.symm).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)))
  exact h.contractibleSpace

noncomputable def hequiv : ContinuousMap.HomotopyEquiv ↥(A ∩ B) S2 where
  toFun := fmap
  invFun := gmap
  left_inv := ⟨H⟩
  right_inv := by
    rw [fg]

end OMA.PoincareCoverH1

open OMA.PoincareCoverH1 in
theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1.H1 := by
  unfold OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H1_R1.H1
  refine ⟨A, B, isOpen_compl_singleton, isOpen_compl_singleton, ?_, contractible_compl Np,
    contractible_compl Sp, ⟨hequiv⟩⟩
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases h : x = Np
  · right
    rw [h]
    exact Np_ne_Sp
  · left
    exact h
