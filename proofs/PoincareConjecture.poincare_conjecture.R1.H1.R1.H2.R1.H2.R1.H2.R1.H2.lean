import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1_H2_R1

open CategoryTheory Limits HomologicalComplex

/-! The two monomorphisms and their cokernels form short exact rows. Their
left comparison is the identity and their middle comparison is a quasi-isomorphism. -/

theorem OMA.solution :
    OMA.R_PoincareConjecture_poincare_conjecture_R1_H1_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro K L A i j f w hi hj hiso n
  let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  let T := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hS : S.ShortExact := { exact := ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel i) }
  have hT : T.ShortExact := { exact := ShortComplex.exact_of_g_is_cokernel T (cokernelIsCokernel j) }
  let g := cokernel.map i j (𝟙 A) f (by simp [w])
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 A
      τ₂ := f
      τ₃ := g
      comm₁₂ := by simpa [S, T] using w.symm
      comm₂₃ := by simp [S, T, g] }
  have hleft : QuasiIso φ.τ₁ := by
    change QuasiIso (𝟙 A)
    infer_instance
  have hmiddle : QuasiIso φ.τ₂ := by
    refine ⟨fun k => (quasiIsoAt_iff_isIso_homologyMap f k).mpr (hiso k)⟩
  have hright : QuasiIso φ.τ₃ := HomologySequence.quasiIso_τ₃ φ hS hT hleft hmiddle
  exact (quasiIsoAt_iff_isIso_homologyMap φ.τ₃ n).mp (hright.quasiIsoAt n)
