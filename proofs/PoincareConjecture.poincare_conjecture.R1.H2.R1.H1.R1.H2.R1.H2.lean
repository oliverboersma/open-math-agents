import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1
import Mathlib

open CategoryTheory Limits AlgebraicTopology

private lemma exact_pushout {C : Type*} [Category C] [Abelian C] {A B D : C}
    (i : A ⟶ B) (j : A ⟶ D) [Mono i] :
    (IsPushout.of_isColimit (pushoutIsPushout i j)).shortComplex.ShortExact := by
  let h := IsPushout.of_isColimit (pushoutIsPushout i j)
  refine ShortComplex.ShortExact.mk' h.exact_shortComplex ?_ ?_
  · change Mono (biprod.lift i (-j))
    apply mono_of_mono_fac (biprod.lift_fst i (-j))
  · exact Cofork.IsColimit.epi h.isColimitCokernelCofork

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro X _ U V
  let f : TopCat.of ↥(U ∩ V) ⟶ TopCat.of U :=
    TopCat.ofHom ⟨Set.inclusion Set.inter_subset_left,continuous_inclusion _⟩
  let g : TopCat.of ↥(U ∩ V) ⟶ TopCat.of V :=
    TopCat.ofHom ⟨Set.inclusion Set.inter_subset_right,continuous_inclusion _⟩
  let F := (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
  haveI : Mono f := (TopCat.mono_iff_injective f).mpr (Set.inclusion_injective (Set.inter_subset_left (s := U) (t := V)))
  exact exact_pushout (F.map f) (F.map g)

