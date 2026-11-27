import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Endomorphism

/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under the Apache License, Version 2.0.
The algebraic argument adapts Homology/Algebra/LocallyNilpotent.lean and
Homology/Algebra/EventualImage.lean at 9f65eaf95b9ff5f1b39cfb2d2d24e51aed891568.
-/

/-! Reduce the open-cover chain comparison to subdivision on the quotient. -/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1_H1_R1

private theorem homologyMap_pow_eq_id {Q : ChainComplex AddCommGrpCat ℕ}
    {S : End Q} (hS : Homotopy S (𝟙 Q)) (k n : ℕ) :
    HomologicalComplex.homologyMap (S ^ k) n = 𝟙 _ := by
  have h : HomologicalComplex.homologyMap S n = 𝟙 _ :=
    (hS.homologyMap_eq n).trans (HomologicalComplex.homologyMap_id Q n)
  induction k with
  | zero => exact HomologicalComplex.homologyMap_id Q n
  | succ k ih =>
    rw [pow_succ, End.mul_def, HomologicalComplex.homologyMap_comp, ih, h,
      Category.id_comp]

private theorem isZero_homology_of_subdivision {Q : ChainComplex AddCommGrpCat ℕ}
    {S : End Q} (hS : Homotopy S (𝟙 Q))
    (hnil : ∀ n (z : Q.X n), ∃ k : ℕ, ((S ^ k).f n) z = 0) (n : ℕ) :
    IsZero (Q.homology n) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro a
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (Q.homologyπ n)).mp inferInstance a
  obtain ⟨k, hk⟩ := hnil n ((Q.iCycles n) z)
  have hz : HomologicalComplex.cyclesMap (S ^ k) n z = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (Q.iCycles n)).mp inferInstance
    have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i (S ^ k) n) z
    change (Q.iCycles n) (HomologicalComplex.cyclesMap (S ^ k) n z) =
      ((S ^ k).f n) ((Q.iCycles n) z) at h
    simpa only [map_zero] using h.trans hk
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (S ^ k) n) z
  rw [homologyMap_pow_eq_id hS k n] at h
  change (Q.homologyπ n) z = (Q.homologyπ n) (HomologicalComplex.cyclesMap (S ^ k) n z) at h
  simpa only [hz, map_zero] using h

private theorem quasiIso_of_acyclic_cokernel {P C : ChainComplex AddCommGrpCat ℕ}
    (q : P ⟶ C) (hm : Mono q)
    (hq : ∀ n, IsZero ((cokernel q).homology n)) : QuasiIso q := by
  let K := ShortComplex.mk q (cokernel.π q) (cokernel.condition q)
  have hK : K.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel q)
      mono_f := hm
      epi_g := inferInstanceAs (Epi (cokernel.π q)) }
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap q n) :=
    (hK.homology_exact₁ (n + 1) n rfl).mono_g ((hq (n + 1)).eq_zero_of_src _)
  have : Epi (HomologicalComplex.homologyMap q n) :=
    (hK.homology_exact₂ n).epi_f ((hq n).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- On the quotient by small chains, subdivision is homotopic to the identity
and repeated subdivision kills every chain. -/
def H1 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (U V : Set X), IsOpen U → IsOpen V →
    let C := (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
    let i : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=
      TopCat.ofHom ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩
    let j : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=
      TopCat.ofHom ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩
    let l : TopCat.of U ⟶ TopCat.of (U ∪ V : Set X) :=
      TopCat.ofHom ⟨Set.inclusion Set.subset_union_left, continuous_inclusion _⟩
    let r : TopCat.of V ⟶ TopCat.of (U ∪ V : Set X) :=
      TopCat.ofHom ⟨Set.inclusion Set.subset_union_right, continuous_inclusion _⟩
    let h : CategoryStruct.comp (C.map i) (C.map l) = CategoryStruct.comp (C.map j) (C.map r) := by
      rw [← C.map_comp, ← C.map_comp]
      rfl
    let Q := cokernel (pushout.desc (C.map l) (C.map r) h)
    ∃ S : End Q, Nonempty (Homotopy S (𝟙 Q)) ∧
      ∀ n (z : Q.X n), ∃ k : ℕ, ((S ^ k).f n) z = 0

/-- The chain pushout embeds into the union complex, since its simplices
are exactly those contained in one of the two subspaces. -/
def H2 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (U V : Set X),
    let C := (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
    let i : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of U :=
      TopCat.ofHom ⟨Set.inclusion Set.inter_subset_left, continuous_inclusion _⟩
    let j : TopCat.of (U ∩ V : Set X) ⟶ TopCat.of V :=
      TopCat.ofHom ⟨Set.inclusion Set.inter_subset_right, continuous_inclusion _⟩
    let l : TopCat.of U ⟶ TopCat.of (U ∪ V : Set X) :=
      TopCat.ofHom ⟨Set.inclusion Set.subset_union_left, continuous_inclusion _⟩
    let r : TopCat.of V ⟶ TopCat.of (U ∪ V : Set X) :=
      TopCat.ofHom ⟨Set.inclusion Set.subset_union_right, continuous_inclusion _⟩
    let h : CategoryStruct.comp (C.map i) (C.map l) = CategoryStruct.comp (C.map j) (C.map r) := by
      rw [← C.map_comp, ← C.map_comp]
      rfl
    Mono (pushout.desc (C.map l) (C.map r) h)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1.H1 := by
  intro hsub hmono X _ U V hU hV
  obtain ⟨S, ⟨hS⟩, hnil⟩ := hsub X U V hU hV
  exact quasiIso_of_acyclic_cokernel _ (hmono X U V) (isZero_homology_of_subdivision hS hnil)

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1_H1_R1
