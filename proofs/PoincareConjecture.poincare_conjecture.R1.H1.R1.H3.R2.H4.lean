import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.R1.H1.R1.H3.R2.H4: hypothesis H4 of reduction
-- PoincareConjecture.poincare_conjecture.R1.H1.R1.H3.R2
-- Credit: @ivillar

/-!
`S⁰ = {±e₀}` has exactly two path components (a path from `e₀` to `-e₀` would make its
coordinate take the value `0`). Mathlib identifies `H₀(S⁰)` with `∐_{π₀ S⁰} ℤ` and the augmentation
with the codiagonal; via the biproduct this is the sum map `ℤ^{π₀ S⁰} → ℤ`, whose kernel is
`{(n, -n)} ≅ ℤ`.
-/

open CategoryTheory Limits AlgebraicTopology

namespace OMA.S0H0

abbrev S0 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1

noncomputable def pp : S0 := ⟨EuclideanSpace.single 0 1, by simp⟩
noncomputable def qq : S0 := ⟨-EuclideanSpace.single 0 1, by simp⟩

theorem coord_abs (x : S0) : |(x : EuclideanSpace ℝ (Fin 1)) 0| = 1 := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin 1))‖ = 1 := norm_eq_of_mem_sphere x
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
    Real.sqrt_sq_eq_abs] at hx
  exact hx

theorem eq_pp_or_qq (x : S0) : x = pp ∨ x = qq := by
  rcases (abs_eq zero_le_one).mp (coord_abs x) with h | h
  · left
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    simp [pp, h]
  · right
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i
    simp [qq, h]

theorem not_joined : ¬ Joined pp qq := by
  rintro ⟨γ⟩
  let f : unitInterval → ℝ := fun t => ((γ t : S0) : EuclideanSpace ℝ (Fin 1)) 0
  have hf : Continuous f :=
    (EuclideanSpace.proj (0 : Fin 1)).continuous.comp (continuous_subtype_val.comp γ.continuous)
  have h0 : f 0 = 1 := by
    show ((γ 0 : S0) : EuclideanSpace ℝ (Fin 1)) 0 = 1
    rw [γ.source]
    simp [pp]
  have h1 : f 1 = -1 := by
    show ((γ 1 : S0) : EuclideanSpace ℝ (Fin 1)) 0 = -1
    rw [γ.target]
    simp [qq]
  have hmem : (0 : ℝ) ∈ Set.Icc (f 1) (f 0) := by rw [h0, h1]; constructor <;> norm_num
  obtain ⟨t, ht⟩ := intermediate_value_univ 1 0 hf hmem
  have := coord_abs (γ t)
  simp only [f] at ht
  rw [ht, abs_zero] at this
  norm_num at this

theorem T_cases (j : ZerothHomotopy S0) :
    j = ZerothHomotopy.mk pp ∨ j = ZerothHomotopy.mk qq := by
  induction j using Quotient.inductionOn with
  | h x =>
    rcases eq_pp_or_qq x with rfl | rfl
    · left; rfl
    · right; rfl

theorem T_ne : (ZerothHomotopy.mk pp : ZerothHomotopy S0) ≠ ZerothHomotopy.mk qq :=
  fun h => not_joined (Quotient.exact h)

instance : Finite (ZerothHomotopy S0) :=
  Finite.of_surjective (fun b : Bool => if b then ZerothHomotopy.mk pp else ZerothHomotopy.mk qq)
    (by
      intro j
      rcases T_cases j with h | h
      · exact ⟨true, by simp [h]⟩
      · exact ⟨false, by simp [h]⟩)

end OMA.S0H0

open OMA.S0H0 in
theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2.H4 := by
  unfold OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2.H4
  classical
  let X : TopCat := TopCat.of S0
  let R : AddCommGrpCat := AddCommGrpCat.of ℤ
  let _ : Fintype (ZerothHomotopy X) := Fintype.ofFinite _
  let sumHom : (ZerothHomotopy X → ℤ) →+ ℤ :=
    { toFun := fun v => ∑ j, v j
      map_zero' := by simp
      map_add' := fun v w => by simp [Finset.sum_add_distrib] }
  let a : ZerothHomotopy X := ZerothHomotopy.mk pp
  let b : ZerothHomotopy X := ZerothHomotopy.mk qq
  have hab : a ≠ b := T_ne
  have huniv : (Finset.univ : Finset (ZerothHomotopy X)) = {a, b} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact T_cases j
  have hsum (v : ZerothHomotopy X → ℤ) : sumHom v = v a + v b := by
    show ∑ j, v j = _
    rw [huniv, Finset.sum_pair hab]
  let e : AddCommGrpCat.of (ZerothHomotopy X → ℤ) ≅ ∐ (fun _ : ZerothHomotopy X => R) :=
    (AddCommGrpCat.biproductIsoPi (fun _ : ZerothHomotopy X => R)).symm ≪≫
      biproduct.isoCoproduct (fun _ : ZerothHomotopy X => R)
  have hd : CategoryStruct.comp (biproduct.desc (Limits.Sigma.ι (fun _ : ZerothHomotopy X => R)))
      (Limits.Sigma.desc (fun _ => 𝟙 R)) = biproduct.desc (fun _ => 𝟙 R) := by
    apply biproduct.hom_ext'
    intro j
    simp
  have key : CategoryStruct.comp e.hom (Limits.Sigma.desc (fun _ => 𝟙 R)) =
      AddCommGrpCat.ofHom sumHom := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, biproduct.isoCoproduct_hom, Category.assoc, hd]
    rw [biproduct.desc_eq, Preadditive.comp_sum, huniv, Finset.sum_pair hab]
    simp only [Category.comp_id, AddCommGrpCat.biproductIsoPi_inv_comp_π]
    ext v
    simp only [AddMonoidHom.comp_apply, AddCommGrpCat.hom_add, AddCommGrpCat.hom_ofHom,
      AddMonoidHom.add_apply, Pi.evalAddMonoidHom_apply, hsum]
  let φ : sumHom.ker →+ ℤ := (Pi.evalAddMonoidHom (fun _ => ℤ) a).comp sumHom.ker.subtype
  have hφ : Function.Bijective φ := by
    constructor
    · intro v w hvw
      apply Subtype.ext
      funext j
      have hv := v.2
      have hw := w.2
      rw [AddMonoidHom.mem_ker, hsum] at hv hw
      have hva : (v : ZerothHomotopy X → ℤ) a = (w : ZerothHomotopy X → ℤ) a := hvw
      rcases T_cases j with rfl | rfl
      · exact hva
      · show (v : ZerothHomotopy X → ℤ) b = (w : ZerothHomotopy X → ℤ) b
        linarith
    · intro n
      refine ⟨⟨fun j => if j = a then n else -n, ?_⟩, ?_⟩
      · rw [AddMonoidHom.mem_ker, hsum]
        simp [Ne.symm hab]
      · simp [φ]
  let i1 := kernelIsoOfEq (TopCat.singularHomology₀Iso_sigma_desc_id X R).symm
  let i2 := kernelIsIsoComp (TopCat.singularHomology₀Iso X R).hom (Limits.Sigma.desc fun _ => 𝟙 R)
  let i3 := (kernelIsIsoComp e.hom (Limits.Sigma.desc fun _ => 𝟙 R)).symm
  let i4 := kernelIsoOfEq key
  let i5 := AddCommGrpCat.kernelIsoKer (AddCommGrpCat.ofHom sumHom)
  let i6 := AddEquiv.toAddCommGrpIso (X := AddCommGrpCat.of sumHom.ker) (Y := AddCommGrpCat.of ℤ)
    (AddEquiv.ofBijective φ hφ)
  exact ⟨i1 ≪≫ i2 ≪≫ i3 ≪≫ i4 ≪≫ i5 ≪≫ i6⟩
