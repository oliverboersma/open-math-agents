import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1

/-!
Each generating simplex vanishes in the local quotient outside its compact image. Compactly supported chains form a subgroup, and the coproduct property shows it is the entire chain group. Naturality passes this property to homology.
-/
open AlgebraicTopology CategoryTheory Limits
open scoped Simplicial
noncomputable section
namespace CompactChains

abbrev F := (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
abbrev C (M : Type) [TopologicalSpace M] := F.obj (TopCat.of M)
abbrev O (M : Type) [TopologicalSpace M] (x : M) := TopCat.of ↥({x}ᶜ : Set M)
abbrev inclu {M : Type} [TopologicalSpace M] (x : M) : O M x ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩
abbrev chainIncl {M : Type} [TopologicalSpace M] (x : M) := F.map (inclu x)
abbrev loc {M : Type} [TopologicalSpace M] (x : M) := cokernel.π (chainIncl x)

def carried (M : Type) [TopologicalSpace M] (n : ℕ) : AddSubgroup ((C M).X n) where
  carrier := {c | ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, (loc x).f n c = 0}
  zero_mem' := ⟨∅,isCompact_empty,fun x _ => map_zero _⟩
  add_mem' := by
    rintro u v ⟨K,hK,hu⟩ ⟨L,hL,hv⟩
    exact ⟨K∪L,hK.union hL,fun x hx => by
      rw [map_add, hu x (fun h => hx (Or.inl h)), hv x (fun h => hx (Or.inr h)), add_zero]⟩
  neg_mem' := by
    rintro u ⟨K,hK,hu⟩
    exact ⟨K,hK,fun x hx => by rw [map_neg,hu x hx,neg_zero]⟩

lemma kill {M : Type} [TopologicalSpace M] (x : M) (n : ℕ) (c : (F.obj (O M x)).X n) :
    (loc x).f n ((chainIncl x).f n c) = 0 := by
  have e := HomologicalComplex.congr_hom (cokernel.condition (chainIncl x)) n
  exact ConcreteCategory.congr_hom e c

lemma simplex_carried (M : Type) [TopologicalSpace M] (n : ℕ)
    (s : (TopCat.toSSet.obj (TopCat.of M)) _⦋n⦌) (v : ℤ) :
    ((TopCat.toSSet.obj (TopCat.of M)).ιChainComplex (R := AddCommGrpCat.of ℤ) s) v ∈
      carried M n := by
  let f : SimplexCategory.toTop.{0}.obj ⦋n⦌ ⟶ TopCat.of M := s.down
  letI : CompactSpace (SimplexCategory.toTop.{0}.obj ⦋n⦌) :=
    inferInstanceAs (CompactSpace (ULift.{0} (stdSimplex ℝ (Fin (n+1)))))
  refine ⟨Set.range (fun t => f t), isCompact_range (show Continuous (fun t => f t) from f.hom.continuous), ?_⟩
  intro x hx
  let l : SimplexCategory.toTop.obj ⦋n⦌ ⟶ O M x :=
    TopCat.ofHom ⟨fun t => ⟨f t, fun h => hx ⟨t,h⟩⟩, f.hom.continuous.subtype_mk _⟩
  let s' : (TopCat.toSSet.obj (O M x)) _⦋n⦌ := ⟨l⟩
  have eq : (TopCat.toSSet.map (inclu x)).app _ s' = s := by
    apply ULift.ext
    change CategoryStruct.comp l (inclu x) = f
    rfl
  have h := SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (O M x)) (Y := TopCat.toSSet.obj (TopCat.of M)) (R := AddCommGrpCat.of ℤ)
    (f := TopCat.toSSet.map (inclu x)) s'
  rw [eq] at h
  have e := congrArg (fun g => g v) h
  change (chainIncl x).f n (((TopCat.toSSet.obj (O M x)).ιChainComplex (R := AddCommGrpCat.of ℤ) s') v) =
    ((TopCat.toSSet.obj (TopCat.of M)).ιChainComplex (R := AddCommGrpCat.of ℤ) s) v at e
  rw [← e]
  exact kill _ _ _

theorem all_carried (M : Type) [TopologicalSpace M] (n : ℕ) (c : (C M).X n) :
    c ∈ carried M n := by
  let X := TopCat.toSSet.obj (TopCat.of M)
  let A := carried M n
  let inc : AddCommGrpCat.of A ⟶ (C M).X n := AddCommGrpCat.ofHom A.subtype
  let fac (s : X _⦋n⦌) : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of A :=
    AddCommGrpCat.ofHom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) s).hom.codRestrict A (simplex_carried M n s))
  let lift : (C M).X n ⟶ AddCommGrpCat.of A := Sigma.desc fac
  have h : CategoryStruct.comp lift inc = 𝟙 ((C M).X n) := by
    apply SSet.chainComplex_hom_ext
    intro s
    change CategoryStruct.comp (Sigma.ι (fun _ : X _⦋n⦌ => AddCommGrpCat.of ℤ) s) (CategoryStruct.comp (Sigma.desc fac) inc) = CategoryStruct.comp (Sigma.ι (fun _ : X _⦋n⦌ => AddCommGrpCat.of ℤ) s) (𝟙 _)
    rw [Sigma.ι_desc_assoc, Category.comp_id]
    rfl
  have e := congrArg (fun f => f c) h
  exact (show (lift c : (C M).X n) = c from e) ▸ (lift c).property

theorem support (M : Type) [TopologicalSpace M] (a : (C M).homology 3) :
    ∃ K : Set M, IsCompact K ∧ ∀ x ∉ K, HomologicalComplex.homologyMap (loc x) 3 a = 0 := by
  obtain ⟨z,rfl⟩ := (AddCommGrpCat.epi_iff_surjective ((C M).homologyπ 3)).mp inferInstance a
  obtain ⟨K,hK,hs⟩ := all_carried M 3 ((C M).iCycles 3 z)
  refine ⟨K,hK,fun x hx => ?_⟩
  have h := hs x hx
  let φ := loc x
  have hc := congrArg (fun f => f z) (HomologicalComplex.cyclesMap_i φ 3)
  have hz : HomologicalComplex.cyclesMap φ 3 z = 0 := by
    apply (AddCommGrpCat.mono_iff_injective ((cokernel (chainIncl x)).iCycles 3)).mp inferInstance
    rw [map_zero]
    exact hc.trans h
  have hn := congrArg (fun f => f z) (HomologicalComplex.homologyπ_naturality φ 3)
  exact hn.trans (by change (cokernel (chainIncl x)).homologyπ 3 (HomologicalComplex.cyclesMap φ 3 z) = _; rw [hz,map_zero])

end CompactChains


theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1.H2 := CompactChains.support
