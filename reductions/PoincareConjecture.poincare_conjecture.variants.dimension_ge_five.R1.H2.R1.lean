import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1
import Mathlib

/-! Top homology of a connected noncompact manifold. Every class comes from a compact subspace, so one point has a punctured representative. Tapered translations in charts transport this property throughout the manifold. Top-degree injectivity on opens and Mayer–Vietoris intersect the open supports, finitely many of which have empty intersection. -/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H2_R1

open AlgebraicTopology CategoryTheory Limits
open scoped Simplicial
noncomputable section


open Set Metric Filter

open scoped Topology

/-- Vanishing above the manifold dimension for the relative group of an open subspace. -/
def H1 : Prop := ∀ (n : ℕ), 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M],
    ∀ U : Set M, IsOpen U → IsZero ((cokernel (((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map
      ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M))).homology (n+1))

/-- Exactness at the middle term of the degree-n Mayer–Vietoris sequence of two opens. -/
def H2 : Prop := ∀ (n : ℕ), 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] (U V : Set M), IsOpen U → IsOpen V →
    let H := ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ))
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



lemma open_inj (dim : H1) (n : ℕ) (hn : 5 ≤ n) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [ConnectedSpace M]
    (U : Set M) (hu : IsOpen U) :
    Function.Injective (((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M)) := by
  let f := ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M)
  letI : Mono f := chain_mono M _
  let seq := ShortComplex.mk _ _ (cokernel.condition f)
  have ex : seq.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have hz := AddCommGrpCat.isZero_iff_subsingleton.mp (dim n hn M U hu)
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro b hb
  obtain ⟨z,hz'⟩ := (ShortComplex.ab_exact_iff _).mp (ex.homology_exact₁ (n+1) n (by rfl)) b hb
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

lemma compact_representative (n : ℕ) (M : Type) [TopologicalSpace M] (a : ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of M)) :
    ∃ K : Set M, IsCompact K ∧ ∃ b, ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of K ⟶ TopCat.of M) b = a := by
  let C := ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of M)
  obtain ⟨z,rfl⟩ := (AddCommGrpCat.epi_iff_surjective (C.homologyπ n)).mp inferInstance a
  obtain ⟨K,hK,b,hb⟩ := compact_chains M n (C.iCycles n z)
  let f := ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of K ⟶ TopCat.of M)
  let D := ((singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of K)
  haveI : Mono f := chain_mono M K
  let l := (ComplexShape.down ℕ).next n
  haveI : Mono (f.f l) := inferInstance
  have hbd : D.d n l b = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (f.f l)).mp inferInstance
    rw [map_zero]
    have eq := ConcreteCategory.congr_hom (f.comm n l) b
    change C.d n l (f.f n b) = f.f l (D.d n l b) at eq
    change f.f n b = _ at hb
    rw [←eq,hb]
    exact ConcreteCategory.congr_hom (C.iCycles_d n l) z
  let y : D.cycles n := (D.sc n).abCyclesIso.inv ⟨b,hbd⟩
  have hy : D.iCycles n y = b := (D.sc n).abCyclesIso_inv_apply_iCycles ⟨b,hbd⟩
  have he : HomologicalComplex.cyclesMap f n y = z := by
    apply (AddCommGrpCat.mono_iff_injective (C.iCycles n)).mp inferInstance
    have eq := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i f n) y
    change C.iCycles n (HomologicalComplex.cyclesMap f n y) = f.f n (D.iCycles n y) at eq
    rw [eq,hy]
    exact hb
  refine ⟨K,hK,D.homologyπ n y,?_⟩
  have hn := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality f n) y
  exact hn.trans (congrArg (fun t => C.homologyπ n t) he)


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


lemma map_factor {n : ℕ} {X M : Type} [TopologicalSpace X] [TopologicalSpace M] {U : Set M}
    (f : TopCat.of X ⟶ TopCat.of M) (hf : ∀ x, f x ∈ U) (b : ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) :
    ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M)
      (((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map (TopCat.ofHom ⟨fun x => (⟨f x,hf x⟩ : U), f.hom.continuous.subtype_mk _⟩) b) =
    ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map f b := by
  let k : TopCat.of X ⟶ TopCat.of U := TopCat.ofHom
    ⟨fun x => (⟨f x,hf x⟩ : U),f.hom.continuous.subtype_mk _⟩
  have eq : CategoryStruct.comp k ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M) = f := rfl
  exact (ConcreteCategory.congr_hom (((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map_comp k ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M)) b).symm.trans
    (congrArg (fun g => ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map g b) eq)

lemma nested {n : ℕ} {M : Type} [TopologicalSpace M] {A B : Set M} (h : A ⊆ B)
    (b : ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of A)) :
    ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of B ⟶ TopCat.of M) (((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Set.inclusion h,continuous_inclusion h⟩)) b) =
    ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of A ⟶ TopCat.of M) b :=
  map_factor ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of A ⟶ TopCat.of M) (fun x => h x.property) b



lemma chart_motion {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) (c : (EuclideanSpace ℝ (Fin n))) {r : ℝ} (hr : 0 < r)
    (hV : closedBall c (8*r) ⊆ e.target)
    {a b : M} (ha : a ∈ e.source) (hb : b ∈ e.source)
    (ha' : dist (e a) c < r) (hb' : dist (e b) c < r) :
    ∃ f : TopCat.of M ⟶ TopCat.of M, Nonempty (TopCat.Homotopy (𝟙 _) f) ∧
      ∀ z, f z = b → z = a := by
  classical
  let weight (c : (EuclideanSpace ℝ (Fin n))) (r : ℝ) (v : (EuclideanSpace ℝ (Fin n))) : ℝ := max 0 (min 1 ((5*r - dist v c)/r))
  have weight_bounds (c : (EuclideanSpace ℝ (Fin n))) (r : ℝ) (v : (EuclideanSpace ℝ (Fin n))) : 0 ≤ weight c r v ∧ weight c r v ≤ 1 :=
    ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have weight_one {c v : (EuclideanSpace ℝ (Fin n))} {r : ℝ} (hr : 0 < r) (hv : dist v c ≤ 4*r) :
      weight c r v = 1 := by
    have h : 1 ≤ (5*r-dist v c)/r := (le_div_iff₀ hr).mpr (by linarith)
    simp [weight,min_eq_left h]
  have weight_zero {c v : (EuclideanSpace ℝ (Fin n))} {r : ℝ} (hr : 0 < r) (hv : 5*r ≤ dist v c) :
      weight c r v = 0 := by
    have h : (5*r-dist v c)/r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
    exact max_eq_left ((min_le_right _ _).trans h)
  have weight_cont (c : (EuclideanSpace ℝ (Fin n))) (r : ℝ) : Continuous (weight c r) := by unfold weight; fun_prop

  let shift (c : (EuclideanSpace ℝ (Fin n))) (r : ℝ) (a b : (EuclideanSpace ℝ (Fin n))) (t : unitInterval) (v : (EuclideanSpace ℝ (Fin n))) : (EuclideanSpace ℝ (Fin n)) :=
    v + ((t.val * weight c r v) • (b-a))
  have shift_cont (c : (EuclideanSpace ℝ (Fin n))) (r : ℝ) (a b : (EuclideanSpace ℝ (Fin n))) : Continuous (fun p : unitInterval × (EuclideanSpace ℝ (Fin n)) => shift c r a b p.1 p.2) := by
    unfold shift
    have h := (weight_cont c r).comp (continuous_snd : Continuous (Prod.snd : unitInterval × (EuclideanSpace ℝ (Fin n)) → (EuclideanSpace ℝ (Fin n))))
    fun_prop
  have shift_dist {c a b : (EuclideanSpace ℝ (Fin n))} {r : ℝ} (ha : dist a c < r) (hb : dist b c < r)
      (t : unitInterval) (v : (EuclideanSpace ℝ (Fin n))) : dist (shift c r a b t v) v < 2*r := by
    have h := weight_bounds c r v
    have h0 : 0 ≤ t.val * weight c r v := mul_nonneg t.property.1 h.1
    have h1 : t.val * weight c r v ≤ 1 := mul_le_one₀ t.property.2 h.1 h.2
    have hd : dist b a < 2*r := by linarith [dist_triangle_right b a c]
    simpa [shift,dist_eq_norm, norm_smul,Real.norm_eq_abs,abs_of_nonneg h0,abs_of_nonneg t.property.1,abs_of_nonneg h.1] using
      (le_trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg (b-a))) (one_mul ‖b-a‖).le).trans_lt (by simpa [dist_eq_norm] using hd)
  have shift_target {c a b : (EuclideanSpace ℝ (Fin n))} {r : ℝ} (hr : 0 < r) (ha : dist a c < r) (hb : dist b c < r)
      {V : Set (EuclideanSpace ℝ (Fin n))} (hc : closedBall c (8*r) ⊆ V) {v : (EuclideanSpace ℝ (Fin n))} (hv : v ∈ V) (t : unitInterval) :
      shift c r a b t v ∈ V := by
    by_cases h : 5*r ≤ dist v c
    · simpa [shift,weight_zero hr h] using hv
    · apply hc
      rw [mem_closedBall]
      linarith [dist_triangle (shift c r a b t v) v c,shift_dist ha hb t v]
  have shift_hit {c a b : (EuclideanSpace ℝ (Fin n))} {r : ℝ} (hr : 0 < r) (ha : dist a c < r) (hb : dist b c < r)
      {v : (EuclideanSpace ℝ (Fin n))} (h : shift c r a b 1 v = b) : v = a := by
    have hd := shift_dist ha hb 1 v
    rw [h, dist_comm] at hd
    have hv : dist v c ≤ 4*r := by linarith [dist_triangle v b c]
    have eq : v + (b-a) = b := by simpa [shift,weight_one hr hv] using h
    calc v = (v + (b-a)) - (b-a) := by abel
         _ = b - (b-a) := by rw [eq]
         _ = a := by abel


  let g := shift c r (e a) (e b)
  let m (p : unitInterval × M) := if p.2 ∈ e.source then e.symm (g p.1 (e p.2)) else p.2
  let K := e.symm '' closedBall c (5*r)
  have inner : closedBall c (5*r) ⊆ e.target :=
    (closedBall_subset_closedBall (by linarith : 5*r ≤ 8*r)).trans hV
  have hK : IsCompact K := (isCompact_closedBall c (5*r)).image_of_continuousOn
    (e.continuousOn_symm.mono inner)
  have subK : K ⊆ e.source := by
    rintro _ ⟨w,hw,rfl⟩
    exact e.map_target (inner hw)
  have ht (t : unitInterval) {z : M} (hz : z ∈ e.source) : g t (e z) ∈ e.target :=
    shift_target hr ha' hb' hV (e.map_source hz) t
  have outside (p : unitInterval × M) (hp : p.2 ∉ K) : m p = p.2 := by
    by_cases hs : p.2 ∈ e.source
    · have hfar : 5*r ≤ dist (e p.2) c := by
        by_contra! hh
        exact hp ⟨e p.2,mem_closedBall.mpr hh.le,e.left_inv hs⟩
      simp [m,hs,g,shift,weight_zero hr hfar,e.left_inv hs]
    · simp [m,hs]
  have hm : Continuous m := continuous_iff_continuousAt.mpr fun p => by
    by_cases hs : p.2 ∈ e.source
    · have hpair : ContinuousAt (fun q : unitInterval × M => (q.1,e q.2)) p :=
        continuousAt_fst.prodMk ((e.continuousAt hs).comp continuousAt_snd)
      have hgs : ContinuousAt (fun q : unitInterval × M => g q.1 (e q.2)) p :=
        (shift_cont c r (e a) (e b)).continuousAt.comp hpair
      have hc : ContinuousAt (fun q : unitInterval × M => e.symm (g q.1 (e q.2))) p :=
        (e.continuousAt_symm (ht p.1 hs)).comp' (f := fun q : unitInterval × M => g q.1 (e q.2)) hgs
      apply hc.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hs)] with q hq
      exact if_pos hq
    · apply (continuous_snd.continuousAt : ContinuousAt (Prod.snd : unitInterval × M → M) p).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds (fun h => hs (subK h)))] with q hq
      exact outside q hq
  let f : TopCat.of M ⟶ TopCat.of M := TopCat.ofHom
    ⟨fun z => m (1,z), hm.comp (continuous_const.prodMk continuous_id)⟩
  refine ⟨f,?_,?_⟩
  · refine ⟨{ toFun := m
              continuous_toFun := hm
              map_one_left := fun _ => rfl
              map_zero_left := ?_ }⟩
    intro z
    change m (0,z) = z
    by_cases h : z ∈ e.source <;> simp [m,h,g,shift,e.left_inv]
  · intro z hz
    change m (1,z) = b at hz
    by_cases hs : z ∈ e.source
    · have h' : e.symm (g 1 (e z)) = b := by simpa [m,hs] using hz
      have eq : g 1 (e z) = e b := (e.right_inv (ht 1 hs)).symm.trans (congrArg e h')
      have h := shift_hit hr ha' hb' eq
      exact e.injOn hs ha h
    · have eq : z = b := by simpa [m,hs] using hz
      exact (hs (eq ▸ hb)).elim



lemma move_neighbors {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ a ∈ U, ∀ b ∈ U,
      ∃ f : TopCat.of M ⟶ TopCat.of M, Nonempty (TopCat.Homotopy (𝟙 _) f) ∧
        ∀ z, f z = b → z = a := by
  let e := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hx : x ∈ e.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) x
  obtain ⟨s,hs,hsT⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let r := s/10
  have hr : 0 < r := by dsimp [r]; positivity
  have hV : closedBall (e x) (8*r) ⊆ e.target :=
    (closedBall_subset_ball (by dsimp [r]; linarith : 8*r < s)).trans hsT
  refine ⟨e.source ∩ e ⁻¹' ball (e x) r,e.isOpen_inter_preimage isOpen_ball,⟨hx,mem_ball_self hr⟩,?_⟩
  intro a ha b hb
  exact chart_motion e _ hr hV ha.1 hb.1 ha.2 hb.2



theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1.H2 := by
  intro dim mv n hn M _ _ _ _ noncompact
  classical
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  suffices zero : ∀ a : ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of M), a = 0 from ⟨fun a b => (zero a).trans (zero b).symm⟩
  intro a
  let P (U : Set M) := ∃ b, ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M) b = a
  have up {A B : Set M} (h : A ⊆ B) : P A → P B := by
    rintro ⟨b,hb⟩
    exact ⟨_,(nested h b).trans hb⟩
  have meet {U V : Set M} (hu : IsOpen U) (hv : IsOpen V) : P U → P V → P (U ∩ V) := by
    rintro ⟨u,eu⟩ ⟨v,ev⟩
    let j : U ⊆ U ∪ V := Set.subset_union_left
    let k : V ⊆ U ∪ V := Set.subset_union_right
    have eq : ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Set.inclusion j,continuous_inclusion j⟩)) u = ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Set.inclusion k,continuous_inclusion k⟩)) v := by
      apply open_inj dim n hn M _ (hu.union hv)
      exact (nested j u).trans (eu.trans (ev.symm.trans (nested k v).symm))
    obtain ⟨w,hw⟩ := mv n hn M U V hu hv u v eq
    let i : U ∩ V ⊆ U := Set.inter_subset_left
    have e : ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Set.inclusion i,continuous_inclusion i⟩)) w = u := hw
    exact ⟨w,(nested i w).symm.trans ((congrArg (fun b => ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map ((TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩) : TopCat.of U ⟶ TopCat.of M) b) e).trans eu)⟩
  let S : Set M := fun x => P ({x}ᶜ)
  have transfer {x y : M} (f : TopCat.of M ⟶ TopCat.of M) (hf : TopCat.Homotopy (𝟙 _) f)
      (hit : ∀ z, f z = y → z = x) : x ∈ S → y ∈ S := by
    rintro ⟨b,hb⟩
    let i : TopCat.of ↥({x}ᶜ : Set M) ⟶ TopCat.of M := (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩)
    let g := CategoryStruct.comp i f
    have hg (p : ↥({x}ᶜ : Set M)) : g p ∈ ({y}ᶜ : Set M) := fun h => p.property (hit p h)
    have homEq : ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map f = 𝟙 _ := by
      have e := hf.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) n
      change ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map (𝟙 (TopCat.of M)) = ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map f at e
      exact e.symm.trans (((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map_id _)
    have hc := ConcreteCategory.congr_hom (((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map_comp i f) b
    change ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map g b = ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map f (((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map i b) at hc
    rw [homEq,hb] at hc
    exact ⟨_,(map_factor g hg b).trans hc⟩
  have near (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ u ∈ U, ∀ v ∈ U, u ∈ S → v ∈ S := by
    obtain ⟨U,hU,hx,hm⟩ := move_neighbors (n := n) x
    refine ⟨U,hU,hx,?_⟩
    intro u hu v hv
    obtain ⟨f,⟨hf⟩,hit⟩ := hm u hu v hv
    exact transfer f hf hit
  have ho : IsOpen S := isOpen_iff_forall_mem_open.mpr fun x hx => by
    obtain ⟨U,hU,hxU,hm⟩ := near x
    exact ⟨U,fun y hy => hm x hxU y hy hx,hU,hxU⟩
  have hc : IsOpen Sᶜ := isOpen_iff_forall_mem_open.mpr fun x hx => by
    obtain ⟨U,hU,hxU,hm⟩ := near x
    exact ⟨U,fun y hy h => hx (hm y hy x hxU h),hU,hxU⟩
  obtain ⟨K,hK,hrep⟩ := compact_representative n M a
  obtain ⟨x,hx⟩ : ∃ x, x ∉ K := by
    by_contra! h
    exact noncompact ⟨Set.eq_univ_of_forall h ▸ hK⟩
  have mem : x ∈ S := up (fun y hy h => hx ((Set.mem_singleton_iff.mp h) ▸ hy)) hrep
  have top : S = univ := (isClopen_iff.mp ⟨isOpen_compl_iff.mp hc,ho⟩).resolve_left (show S.Nonempty from ⟨x,mem⟩).ne_empty
  have avoid (y : M) : ∃ K, IsCompact K ∧ y ∉ K ∧ P K := by
    let V : Set M := {y}ᶜ
    obtain ⟨b,hb⟩ := (show y ∈ S from top ▸ mem_univ y)
    obtain ⟨K,hK,c,hc⟩ := compact_representative n V b
    let t : Set M := Subtype.val '' K
    let i : TopCat.of K ⟶ TopCat.of V := (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩)
    let j : TopCat.of V ⟶ TopCat.of M := (TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩)
    let f := CategoryStruct.comp i j
    have into (p : K) : f p ∈ t := ⟨p.val,p.property,rfl⟩
    have hcomp := ConcreteCategory.congr_hom (((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map_comp i j) c
    change ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map f c = ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map j (((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).map i c) at hcomp
    refine ⟨t,hK.image continuous_subtype_val,?_,_,(map_factor f into c).trans ?_⟩
    · rintro ⟨z,hz,h⟩
      exact z.property h
    · rw [hcomp,hc]
      exact hb
  obtain ⟨z,hz⟩ := compact_intersections P (fun h => up h) (fun hu hv => meet hu hv) (compact_representative n M a) avoid
  let E := TopCat.of ↥(∅ : Set M)
  have hempty := isZero_singularHomologyFunctor_of_totallyDisconnectedSpace AddCommGrpCat n (AddCommGrpCat.of ℤ) E (by omega)
  have ez : z = 0 := (AddCommGrpCat.isZero_iff_subsingleton.mp hempty).elim _ _
  rw [ez,map_zero] at hz
  exact hz.symm


end

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H2_R1
