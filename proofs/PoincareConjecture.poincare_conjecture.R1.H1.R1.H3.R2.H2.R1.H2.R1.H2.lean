import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2_H2_R1_H2_R1
import Mathlib

/-! A cokernel comparison for short exact sequences of chain complexes. -/

open CategoryTheory Limits HomologicalComplex

private theorem cokernel_map_homology_iso
    {K L A : ChainComplex AddCommGrpCat ℕ}
    (i : A ⟶ K) (j : A ⟶ L) (f : K ⟶ L)
    (w : CategoryStruct.comp i f = j) [Mono i] [Mono j]
    (hiso : ∀ n, IsIso (homologyMap f n)) (n : ℕ) :
    IsIso (homologyMap (cokernel.map i j (𝟙 A) f (by simp [w])) n) := by
  let S := ShortComplex.mk i (cokernel.π i) (by simp)
  let T := ShortComplex.mk j (cokernel.π j) (by simp)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance
  have hT : T.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel j) inferInstance inferInstance
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 A
      τ₂ := f
      τ₃ := cokernel.map i j (𝟙 A) f (by simp [w])
      comm₁₂ := by simpa [S, T] using w.symm
      comm₂₃ := by simp [S, T] }
  have hi : QuasiIso φ.τ₁ := by
    change QuasiIso (𝟙 A)
    infer_instance
  have hf : QuasiIso φ.τ₂ := by
    rw [quasiIso_iff]
    intro k
    exact (quasiIsoAt_iff_isIso_homologyMap f k).mpr (hiso k)
  have hφ := HomologySequence.quasiIso_τ₃ φ hS hT hi hf
  exact (quasiIsoAt_iff_isIso_homologyMap φ.τ₃ n).mp (hφ.quasiIsoAt n)

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H3_R2_H2_R1_H2_R1.H2 :=
  cokernel_map_homology_iso