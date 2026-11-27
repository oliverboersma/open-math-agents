import FormalConjectures.Other.HyperbolicGroupsResiduallyFinite

/-!
The first hypothesis is the existing non-residual-finiteness result. The second isolates the
construction in Kapovich and Wise, J. Algebra 223 (2000), proof of Theorem 3.3. Their amalgam
contains copies of the original group. Generators of each factor are conjugate to products of
copies of the chosen element in the other factor, so the copies normally generate the amalgam.
The reduction expresses this geometric input separately from its consequence for finite quotients.
-/

namespace OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R1

/-- There is a word-hyperbolic group that is not residually finite. -/
def H1 : Prop := ¬ ∀ (A : Type) [Group A] [Group.IsHyperbolic A], Group.ResiduallyFinite A

/-- The normal-generation property of the Kapovich–Wise amalgam for an element `a ≠ 1`. -/
def H2 : Prop := ∀ (A : Type) [Group A] [Group.IsHyperbolic A] (a : A), a ≠ 1 →
  ∃ (K : Type) (_ : Group K) (_ : Group.IsHyperbolic K) (_ : Nontrivial K),
    Subgroup.normalClosure {x : K | ∃ f : A →* K, f a = x} = ⊤

lemma finiteIndex_eq_top_of_no_finite_maps {G : Type} [Group G]
    (h : ∀ (F : Type) [Group F] [Finite F], ∀ (φ : G →* F) (g : G), φ g = 1)
    (H : Subgroup G) [H.FiniteIndex] : H = ⊤ := by
  apply top_unique
  intro g _
  apply H.normalCore_le
  rw [Subgroup.normalCore_eq_ker]
  exact MonoidHom.mem_ker.mpr (h (Equiv.Perm (G ⧸ H)) (MulAction.toPermHom G (G ⧸ H)) g)

theorem main : H1 → H2 → type_of% @HyperbolicGroupsResiduallyFinite.hyperbolic_exists_finiteIndex_ne_top := by
  classical
  intro hNotRF hAmalgam hProper
  apply hNotRF
  intro A _ _
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro a ha
  by_contra hUnseparated
  have hVanishing (F : Type) [Group F] [Finite F] (f : A →* F) : f a = 1 := by
    by_contra hf
    exact hUnseparated ⟨F, inferInstance, inferInstance, f, hf⟩
  obtain ⟨K, _, _, _, hNormalGen⟩ := hAmalgam A a ha
  obtain ⟨H, hne, hFinite⟩ := hProper K
  haveI : H.FiniteIndex := hFinite
  have hTrivial (F : Type) [Group F] [Finite F] (f : K →* F) (x : K) : f x = 1 := by
    have hker : Subgroup.normalClosure {y : K | ∃ g : A →* K, g a = y} ≤ f.ker := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨g, rfl⟩
      exact MonoidHom.mem_ker.mpr (hVanishing F (f.comp g))
    rw [hNormalGen] at hker
    exact MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x))
  exact hne (finiteIndex_eq_top_of_no_finite_maps hTrivial H)

end OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_exists_finiteIndex_ne_top_R1
