import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R1
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.R1.H1.R1.H3.R1.H2: hypothesis H2 of reduction
-- PoincareConjecture.poincare_conjecture.R1.H1.R1.H3.R1
-- Credit: @ivillar

/-!
`Circle.exp : ℝ → Circle` is a quotient covering map by `2πℤ` (Mathlib), and `Circle` is
homeomorphic to the unit sphere of `EuclideanSpace ℝ (Fin 2)` through the isometry
`ℂ ≃ ℝ²`. Since `ℝ` is simply connected, Mathlib's `IsAddQuotientCoveringMap.fundamentalGroupEquiv`
identifies the fundamental group with `(Multiplicative (2πℤ))ᵐᵒᵖ`, a commutative group isomorphic
to `Multiplicative ℤ`; the abelianization of a commutative group is itself.
-/

open Metric

namespace OMA.CircleH2

abbrev S1 := sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

noncomputable def L : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr

noncomputable def ψ : Circle ≃ₜ S1 where
  toFun z := ⟨L (z : ℂ), by rw [mem_sphere_zero_iff_norm, L.norm_map]; exact Circle.norm_coe z⟩
  invFun v := ⟨L.symm (v : EuclideanSpace ℝ (Fin 2)), by
    show L.symm (v : EuclideanSpace ℝ (Fin 2)) ∈ sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm, L.symm.norm_map]
    exact norm_eq_of_mem_sphere v⟩
  left_inv z := by
    apply Subtype.ext
    show L.symm (L (z : ℂ)) = (z : ℂ)
    exact L.symm_apply_apply _
  right_inv v := by
    apply Subtype.ext
    show L (L.symm (v : EuclideanSpace ℝ (Fin 2))) = v
    exact L.apply_symm_apply _
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact L.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact L.symm.continuous.comp continuous_subtype_val

theorem hp : IsAddQuotientCoveringMap (ψ ∘ Circle.exp) (AddSubgroup.zmultiples (2 * Real.pi)) :=
  Circle.isAddQuotientCoveringMap_exp.homeomorph_comp ψ

noncomputable def gEquiv : ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi) :=
  AddEquiv.ofBijective
    (zmultiplesHom (AddSubgroup.zmultiples (2 * Real.pi))
      ⟨2 * Real.pi, AddSubgroup.mem_zmultiples _⟩)
    ⟨by
      intro m n h
      have h2 := congrArg Subtype.val h
      simp only [zmultiplesHom_apply, AddSubgroup.coe_zsmul, zsmul_eq_mul] at h2
      have hpi : (2 * Real.pi) ≠ 0 := by positivity
      exact_mod_cast mul_right_cancel₀ hpi h2,
    by
      rintro ⟨y, hy⟩
      obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
      refine ⟨k, Subtype.ext ?_⟩
      simp only [zmultiplesHom_apply, AddSubgroup.coe_zsmul]
      exact hk⟩

end OMA.CircleH2

open OMA.CircleH2 in
theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R1.H2 := by
  unfold OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R1.H2
  intro x
  let e : (ψ ∘ Circle.exp) ⁻¹' {x} := ⟨(hp.surjective x).choose, (hp.surjective x).choose_spec⟩
  let G := AddSubgroup.zmultiples (2 * Real.pi)
  let φ : FundamentalGroup S1 x ≃* (Multiplicative G)ᵐᵒᵖ := hp.fundamentalGroupEquiv e
  let φ2 : Abelianization (FundamentalGroup S1 x) ≃* Multiplicative ℤ :=
    φ.abelianizationCongr.trans ((Abelianization.equivOfComm).symm.trans
      ((MulOpposite.opMulEquiv).symm.trans (AddEquiv.toMultiplicative gEquiv.symm)))
  exact ⟨(MulEquiv.toAdditive φ2).toAddCommGrpIso⟩
