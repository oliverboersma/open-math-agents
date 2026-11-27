import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1
import Mathlib

/-! Local detection of an absolute top cycle. The long exact sequence lifts a locally trivial class to each punctured manifold. Compact representatives there avoid whole neighborhoods. A finite subcover and Mayer–Vietoris then shrink a representative into the empty set. The degree-four dimension bound supplies injectivity for inclusions of opens. -/
namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1
open AlgebraicTopology CategoryTheory Limits
open scoped Simplicial
noncomputable section
/-- Vanishing above dimension three for the relative group of an open subspace. -/
def H1 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [ConnectedSpace M],
    ∀ U : Set M, IsOpen U → IsZero ((cokernel (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map
      ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M))).homology 4)

/-- Exactness at the middle term of the degree-three Mayer–Vietoris sequence of two opens. -/
def H2 : Prop := ∀ (M : Type) [TopologicalSpace M] (U V : Set M), IsOpen U → IsOpen V →
    let H := ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ))
    let j : TopCat.of U ⟶ TopCat.of ↥(U ∪ V) := (TopCat.ofHom ⟨Set.inclusion (Set.subset_union_left (s := U) (t := V)),continuous_inclusion (Set.subset_union_left (s := U) (t := V))⟩)
    let k : TopCat.of V ⟶ TopCat.of ↥(U ∪ V) := (TopCat.ofHom ⟨Set.inclusion (Set.subset_union_right (s := U) (t := V)),continuous_inclusion (Set.subset_union_right (s := U) (t := V))⟩)
    let i : TopCat.of ↥(U ∩ V) ⟶ TopCat.of U := (TopCat.ofHom ⟨Set.inclusion (Set.inter_subset_left (s := U) (t := V)),continuous_inclusion (Set.inter_subset_left (s := U) (t := V))⟩)
    ∀ u v, H.map j u = H.map k v → ∃ w, H.map i w = u


lemma chain_mono (M : Type) [TopologicalSpace M] (U : Set M) :
    Mono (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M)) := by
  classical
  let i : TopCat.of U ⟶ TopCat.of M := (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩)
  let X := TopCat.toSSet.obj (TopCat.of U)
  let Y := TopCat.toSSet.obj (TopCat.of M)
  let g : X ⟶ Y := TopCat.toSSet.map i
  apply HomologicalComplex.mono_of_mono_f
  intro n
  let j := g.app (Opposite.op ⦋n⦌)
  have hj : Function.Injective j := by
    intro s t h
    apply ULift.ext
    change (s.down : SimplexCategory.toTop.obj ⦋n⦌ ⟶ TopCat.of U) = t.down
    apply ConcreteCategory.hom_ext
    intro v
    let unpack (a : Y _⦋n⦌) : SimplexCategory.toTop.obj ⦋n⦌ ⟶ TopCat.of M := a.down
    exact Subtype.ext (congrArg (fun a => (unpack a).hom v) h)
  let back (t : Y _⦋n⦌) : AddCommGrpCat.of ℤ ⟶ (X.chainComplex (AddCommGrpCat.of ℤ)).X n :=
    if h : ∃ s, j s = t then X.ιChainComplex h.choose else 0
  let ret : (Y.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶ (X.chainComplex (AddCommGrpCat.of ℤ)).X n :=
    Sigma.desc back
  have hret : CategoryStruct.comp ((((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map i).f n) ret = 𝟙 _ := by
    apply SSet.chainComplex_hom_ext
    intro s
    change CategoryStruct.comp (X.ιChainComplex s) (CategoryStruct.comp ((SSet.chainComplexMap g (AddCommGrpCat.of ℤ)).f n) ret) = CategoryStruct.comp (X.ιChainComplex s) (𝟙 _)
    rw [SSet.ι_chainComplexMap_f_assoc, Category.comp_id]
    change CategoryStruct.comp (Sigma.ι _ (j s)) (Sigma.desc back) = _
    rw [Sigma.ι_desc]
    have he : ∃ t, j t = j s := ⟨s,rfl⟩
    simp only [back,dif_pos he,hj he.choose_spec]
  apply (AddCommGrpCat.mono_iff_injective _).mpr
  intro a b hab
  have ea := ConcreteCategory.congr_hom hret a
  have eb := ConcreteCategory.congr_hom hret b
  exact ea.symm.trans ((congrArg (fun z => ret z) hab).trans eb)

lemma point_lift (M : Type) [TopologicalSpace M] (x : M)
    (a : ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of M))
    (ha : HomologicalComplex.homologyMap (cokernel.π (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map
      ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of ↥({x}ᶜ : Set M) ⟶ TopCat.of M))) 3 a = 0) :
    ∃ b, ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of ↥({x}ᶜ : Set M) ⟶ TopCat.of M) b = a := by
  let i : TopCat.of ↥({x}ᶜ : Set M) ⟶ TopCat.of M := (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩)
  let f := ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map i
  letI : Mono f := chain_mono M _
  let seq := ShortComplex.mk _ _ (cokernel.condition f)
  have ex : seq.ShortExact := { exact := ShortComplex.exact_cokernel f }
  exact ((ShortComplex.ab_exact_iff _).mp (ex.homology_exact₂ 3)) a ha

lemma open_inj (dim : H1) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [ConnectedSpace M]
    (U : Set M) (hu : IsOpen U) :
    Function.Injective (((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M)) := by
  let f := ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M)
  letI : Mono f := chain_mono M _
  let seq := ShortComplex.mk _ _ (cokernel.condition f)
  have ex : seq.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have hz := AddCommGrpCat.isZero_iff_subsingleton.mp (dim M U hu)
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro b hb
  obtain ⟨z,hz'⟩ := (ShortComplex.ab_exact_iff _).mp (ex.homology_exact₁ 4 3 (by decide)) b hb
  have e : z = 0 := hz.elim _ _
  rw [e,map_zero] at hz'
  exact hz'.symm


lemma compact_chains (M : Type) [TopologicalSpace M] (n : ℕ)
    (c : (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of M)).X n) : ∃ K : Set M, IsCompact K ∧ ∃ b,
    (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of K ⟶ TopCat.of M)).f n b = c := by
  classical
  let X := TopCat.toSSet.obj (TopCat.of M)
  let C := ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of M)
  let f (K : Set M) := (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of K ⟶ TopCat.of M)).f n
  have up {K L : Set M} (h : K ⊆ L) : (f K).hom.range ≤ (f L).hom.range := by
    rintro v ⟨b,rfl⟩
    let i : TopCat.of K ⟶ TopCat.of L := (TopCat.ofHom ⟨Set.inclusion h,continuous_inclusion h⟩)
    let j : TopCat.of L ⟶ TopCat.of M := (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩)
    let e := HomologicalComplex.congr_hom (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map_comp i j) n
    exact ⟨_,(ConcreteCategory.congr_hom e b).symm⟩
  let A : AddSubgroup (C.X n) := {
    carrier := {v | ∃ K : Set M, IsCompact K ∧ v ∈ (f K).hom.range}
    zero_mem' := ⟨∅,isCompact_empty,(f ∅).hom.range.zero_mem⟩
    neg_mem' := by rintro v ⟨K,hK,hv⟩; exact ⟨K,hK,(f K).hom.range.neg_mem hv⟩
    add_mem' := by
      rintro u v ⟨K,hK,hu⟩ ⟨L,hL,hv⟩
      exact ⟨K ∪ L,hK.union hL,(f _).hom.range.add_mem (up Set.subset_union_left hu) (up Set.subset_union_right hv)⟩ }
  have generator (s : X _⦋n⦌) (v : ℤ) : (X.ιChainComplex (R := AddCommGrpCat.of ℤ) s) v ∈ A := by
    let t : SimplexCategory.toTop.obj ⦋n⦌ ⟶ TopCat.of M := s.down
    letI : CompactSpace (SimplexCategory.toTop.{0}.obj ⦋n⦌) :=
      inferInstanceAs (CompactSpace (ULift.{0} (stdSimplex ℝ (Fin (n+1)))))
    let K := Set.range (fun p => t p)
    let j : TopCat.of K ⟶ TopCat.of M := (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩)
    let l : SimplexCategory.toTop.obj ⦋n⦌ ⟶ TopCat.of K :=
      TopCat.ofHom ⟨fun p => ⟨t p,⟨p,rfl⟩⟩,t.hom.continuous.subtype_mk _⟩
    let s' : (TopCat.toSSet.obj (TopCat.of K)) _⦋n⦌ := ⟨l⟩
    have eq : (TopCat.toSSet.map j).app _ s' = s := by apply ULift.ext; rfl
    have e := SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj (TopCat.of K)) (Y := X)
      (R := AddCommGrpCat.of ℤ) (f := TopCat.toSSet.map j) s'
    rw [eq] at e
    exact ⟨K,isCompact_range t.hom.continuous,_,ConcreteCategory.congr_hom e v⟩
  let inc : AddCommGrpCat.of A ⟶ C.X n := AddCommGrpCat.ofHom A.subtype
  let fac (s : X _⦋n⦌) : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of A :=
    AddCommGrpCat.ofHom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) s).hom.codRestrict A (generator s))
  let lift : C.X n ⟶ AddCommGrpCat.of A := Sigma.desc fac
  have h : CategoryStruct.comp lift inc = 𝟙 (C.X n) := by
    apply SSet.chainComplex_hom_ext
    intro s
    change CategoryStruct.comp (Sigma.ι (fun _ : X _⦋n⦌ => AddCommGrpCat.of ℤ) s) (CategoryStruct.comp (Sigma.desc fac) inc) = CategoryStruct.comp (Sigma.ι (fun _ : X _⦋n⦌ => AddCommGrpCat.of ℤ) s) (𝟙 _)
    rw [Sigma.ι_desc_assoc, Category.comp_id]
    rfl
  have e : (lift c : C.X n) = c := ConcreteCategory.congr_hom h c
  exact e ▸ (lift c).property

lemma compact_representative (M : Type) [TopologicalSpace M] (a : ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of M)) :
    ∃ K : Set M, IsCompact K ∧ ∃ b, ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of K ⟶ TopCat.of M) b = a := by
  let C := ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of M)
  obtain ⟨z,rfl⟩ := (AddCommGrpCat.epi_iff_surjective (C.homologyπ 3)).mp inferInstance a
  obtain ⟨K,hK,b,hb⟩ := compact_chains M 3 (C.iCycles 3 z)
  let f := ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of K ⟶ TopCat.of M)
  let D := ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of K)
  haveI : Mono f := chain_mono M K
  let l := (ComplexShape.down ℕ).next 3
  haveI : Mono (f.f l) := inferInstance
  have hbd : D.d 3 l b = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (f.f l)).mp inferInstance
    rw [map_zero]
    have eq := ConcreteCategory.congr_hom (f.comm 3 l) b
    change C.d 3 l (f.f 3 b) = f.f l (D.d 3 l b) at eq
    change f.f 3 b = _ at hb
    rw [←eq,hb]
    exact ConcreteCategory.congr_hom (C.iCycles_d 3 l) z
  let y : D.cycles 3 := (D.sc 3).abCyclesIso.inv ⟨b,hbd⟩
  have hy : D.iCycles 3 y = b := (D.sc 3).abCyclesIso_inv_apply_iCycles ⟨b,hbd⟩
  have he : HomologicalComplex.cyclesMap f 3 y = z := by
    apply (AddCommGrpCat.mono_iff_injective (C.iCycles 3)).mp inferInstance
    have eq := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f 3) y
    change C.iCycles 3 (HomologicalComplex.cyclesMap f 3 y) = f.f 3 (D.iCycles 3 y) at eq
    rw [eq,hy]
    exact hb
  refine ⟨K,hK,D.homologyπ 3 y,?_⟩
  have hn := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f 3) y
  exact hn.trans (congrArg (fun t => C.homologyπ 3 t) he)

lemma compact_intersections {M : Type} [TopologicalSpace M] [T2Space M] [LocallyCompactSpace M]
    (P : Set M → Prop) (up : ∀ {A B}, A ⊆ B → P A → P B)
    (inter : ∀ {U V}, IsOpen U → IsOpen V → P U → P V → P (U ∩ V))
    (base : ∃ K, IsCompact K ∧ P K)
    (avoid : ∀ x : M, ∃ K, IsCompact K ∧ x ∉ K ∧ P K) : P ∅ := by
  classical
  obtain ⟨K,hK,hP⟩ := base
  obtain ⟨D,hD,hKD⟩ := exists_compact_superset hK
  have shrink (x : M) : ∃ L : Set M, IsCompact L ∧ x ∉ L ∧ P (interior L) := by
    obtain ⟨E,hE,hx,he⟩ := avoid x
    have hsub : E ⊆ ({x}ᶜ : Set M) := by
      intro y hy h
      exact hx ((Set.mem_singleton_iff.mp h) ▸ hy)
    obtain ⟨L,hL,hEL,hLx⟩ := exists_compact_between hE isOpen_compl_singleton hsub
    exact ⟨L,hL,fun h => hLx h rfl,up hEL he⟩
  choose L hc hx hp using shrink
  obtain ⟨s,hs⟩ := hD.elim_finite_subcover (fun x => (L x)ᶜ)
    (fun x => (hc x).isClosed.isOpen_compl) (fun x _ => Set.mem_iUnion.mpr ⟨x,hx x⟩)
  let W (t : Finset M) := interior D ∩ ⋂ x ∈ t, interior (L x)
  have good (t : Finset M) : IsOpen (W t) ∧ P (W t) := by
    induction t using Finset.induction_on with
    | empty => simpa [W] using And.intro (isOpen_interior (s := D)) (up hKD hP)
    | @insert x t hxt ih =>
      have eq : W (insert x t) = W t ∩ interior (L x) := by ext z; simp [W]; tauto
      rw [eq]
      exact ⟨ih.1.inter isOpen_interior,inter ih.1 isOpen_interior ih.2 (hp x)⟩
  apply up (A := W s) _ (good s).2
  intro z hz
  obtain ⟨x,hxs,hxout⟩ := Set.mem_iUnion₂.mp (hs (interior_subset hz.1))
  exact (hxout (interior_subset (Set.mem_iInter₂.mp hz.2 x hxs))).elim

lemma map_factor {X M : Type} [TopologicalSpace X] [TopologicalSpace M] {U : Set M}
    (f : TopCat.of X ⟶ TopCat.of M) (hf : ∀ x, f x ∈ U) (b : ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) :
    ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M)
      (((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom ⟨fun x => (⟨f x,hf x⟩ : U), f.hom.continuous.subtype_mk _⟩) b) =
    ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map f b := by
  let k : TopCat.of X ⟶ TopCat.of U := TopCat.ofHom
    ⟨fun x => (⟨f x,hf x⟩ : U),f.hom.continuous.subtype_mk _⟩
  have eq : CategoryStruct.comp k ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M) = f := rfl
  exact (ConcreteCategory.congr_hom (((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map_comp k ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M)) b).symm.trans
    (congrArg (fun g => ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map g b) eq)

lemma nested {M : Type} [TopologicalSpace M] {A B : Set M} (h : A ⊆ B)
    (b : ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of A)) :
    ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of B ⟶ TopCat.of M) (((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Set.inclusion h,continuous_inclusion h⟩)) b) =
    ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of A ⟶ TopCat.of M) b :=
  map_factor ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of A ⟶ TopCat.of M) (fun x => h x.property) b

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1.H1 := by
  intro dim mv M _ _ _ _
  dsimp only
  intro a ha
  classical
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M
  let P (U : Set M) := ∃ b, ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M) b = a
  have up {A B : Set M} (h : A ⊆ B) : P A → P B := by
    rintro ⟨b,hb⟩
    exact ⟨_,(nested h b).trans hb⟩
  have meet {U V : Set M} (hu : IsOpen U) (hv : IsOpen V) : P U → P V → P (U ∩ V) := by
    rintro ⟨u,eu⟩ ⟨v,ev⟩
    let j : U ⊆ U ∪ V := Set.subset_union_left
    let k : V ⊆ U ∪ V := Set.subset_union_right
    have eq : ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Set.inclusion j,continuous_inclusion j⟩)) u = ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Set.inclusion k,continuous_inclusion k⟩)) v := by
      apply open_inj dim M _ (hu.union hv)
      exact (nested j u).trans (eu.trans (ev.symm.trans (nested k v).symm))
    obtain ⟨w,hw⟩ := mv M U V hu hv u v eq
    let i : U ∩ V ⊆ U := Set.inter_subset_left
    have e : ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Set.inclusion i,continuous_inclusion i⟩)) w = u := hw
    exact ⟨w,(nested i w).symm.trans ((congrArg (fun b => ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M) b) e).trans eu)⟩
  have avoid (x : M) : ∃ K, IsCompact K ∧ x ∉ K ∧ P K := by
    let V : Set M := {x}ᶜ
    obtain ⟨b,hb⟩ := point_lift M x a (ha x)
    obtain ⟨K,hK,c,hc⟩ := compact_representative V b
    let t : Set M := Subtype.val '' K
    let i : TopCat.of K ⟶ TopCat.of V := (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩)
    let j : TopCat.of V ⟶ TopCat.of M := (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩)
    let f := CategoryStruct.comp i j
    have into (p : K) : f p ∈ t := ⟨p.val,p.property,rfl⟩
    have hcomp := ConcreteCategory.congr_hom (((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map_comp i j) c
    change ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map f c = ((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map j (((singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)).map i c) at hcomp
    refine ⟨t,hK.image continuous_subtype_val,?_,_,(map_factor f into c).trans ?_⟩
    · rintro ⟨z,hz,h⟩
      exact z.property h
    · rw [hcomp,hc]
      exact hb
  obtain ⟨z,hz⟩ := compact_intersections P (fun h => up h) (fun hu hv => meet hu hv) (compact_representative M a) avoid
  let E := TopCat.of ↥(∅ : Set M)
  have hempty := isZero_singularHomologyFunctor_of_totallyDisconnectedSpace AddCommGrpCat 3 (AddCommGrpCat.of ℤ) E (by decide)
  have ez : z = 0 := (AddCommGrpCat.isZero_iff_subsingleton.mp hempty).elim _ _
  rw [ez,map_zero] at hz
  exact hz.symm

end
end OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1_H1_R1

