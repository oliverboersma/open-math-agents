import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H2_R1
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.R1.H2.R1.H2.R1.H2: hypothesis H2 of reduction
-- PoincareConjecture.poincare_conjecture.R1.H2.R1.H2.R1
-- Credit: @ivillar

/-!
The inclusion `{x}ᶜ ⊆ M` is a monomorphism of spaces, hence its singular simplicial set map and,
degreewise, the induced map of free abelian groups `∐ ℤ ⟶ ∐ ℤ` are monomorphisms
(`sigmaConst` preserves monomorphisms). So if `i(c) = z` for a cycle `z`, then
`i(d c) = d(i c) = d z = 0` forces `d c = 0`; the cycle `b = c` maps to `z` on cycles
(`iCycles` is mono), hence `[b] ↦ [z]` in homology.
-/

open CategoryTheory Limits AlgebraicTopology

namespace OMA.PoincareLiftCycle

theorem lift_cycle (K L : ChainComplex AddCommGrpCat.{0} ℕ) (φ : K ⟶ L)
    (h2 : Function.Injective (φ.f 2)) (z : L.cycles 3) (c : K.X 3)
    (hc : φ.f 3 c = L.iCycles 3 z) :
    ∃ b : K.cycles 3, HomologicalComplex.homologyMap φ 3 (K.homologyπ 3 b) = L.homologyπ 3 z := by
  have h0 : φ.f 2 (K.d 3 2 c) = 0 := by
    calc φ.f 2 (K.d 3 2 c) = (K.d 3 2 ≫ φ.f 2) c := by rw [ConcreteCategory.comp_apply]
      _ = (φ.f 3 ≫ L.d 3 2) c := by rw [φ.comm]
      _ = L.d 3 2 (φ.f 3 c) := by rw [ConcreteCategory.comp_apply]
      _ = L.d 3 2 (L.iCycles 3 z) := by rw [hc]
      _ = (L.iCycles 3 ≫ L.d 3 2) z := by rw [ConcreteCategory.comp_apply]
      _ = 0 := by rw [HomologicalComplex.iCycles_d]; rfl
  have hdc : K.d 3 2 c = 0 := h2 (h0.trans (map_zero _).symm)
  let f : AddCommGrpCat.of ℤ ⟶ K.X 3 := AddCommGrpCat.ofHom (zmultiplesHom _ c)
  have hf : CategoryStruct.comp f (K.d 3 2) = 0 := by
    ext
    simp [f, hdc]
  let b : K.cycles 3 := K.liftCycles f 2 (by simp) hf (1 : ℤ)
  have hb : K.iCycles 3 b = c := by
    have h3 := congrArg (fun g => g (1 : ℤ)) (K.liftCycles_i f 2 (by simp) hf)
    simp only [ConcreteCategory.comp_apply] at h3
    rw [h3]
    simp [f]
  refine ⟨b, ?_⟩
  have hcyc : HomologicalComplex.cyclesMap φ 3 b = z := by
    apply (AddCommGrpCat.mono_iff_injective (L.iCycles 3)).mp inferInstance
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply, hb, hc]
  rw [← hcyc, ← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]

end OMA.PoincareLiftCycle

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H2_R1.H2 := by
  unfold OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H2_R1.H2
  intro M _ x z c hc
  have hmono : ∀ n, Mono ((((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of ↥({x}ᶜ : Set M) ⟶ TopCat.of M)).f n) := by
    intro n
    have h1 : Mono (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of ↥({x}ᶜ : Set M) ⟶ TopCat.of M) :=
      (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    have h2 : Mono (TopCat.toSSet.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of ↥({x}ᶜ : Set M) ⟶ TopCat.of M)) := inferInstance
    have h3 : Mono ((TopCat.toSSet.map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of ↥({x}ᶜ : Set M) ⟶ TopCat.of M)).app (Opposite.op (SimplexCategory.mk n))) :=
      inferInstance
    exact (sigmaConst.obj (AddCommGrpCat.of ℤ)).map_mono _
  exact OMA.PoincareLiftCycle.lift_cycle _ _ _
    ((AddCommGrpCat.mono_iff_injective _).mp (hmono 2)) z c hc
