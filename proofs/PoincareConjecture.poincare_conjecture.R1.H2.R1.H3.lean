import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H2_R1

/-!
Vanishing propagates under chart-supported maps homotopic to the identity. A tapered translation carries one nearby point to another with a singleton fiber. Homotopy invariance and the exact sequence of a puncture transport the relative vanishing in both directions. Connectedness then propagates it globally.
-/
open Set Metric Filter
open scoped Topology
noncomputable section
namespace LocalMove
abbrev E := EuclideanSpace ℝ (Fin 3)
def weight (c : E) (r : ℝ) (v : E) : ℝ := max 0 (min 1 ((5*r - dist v c)/r))
lemma weight_bounds (c : E) (r : ℝ) (v : E) : 0 ≤ weight c r v ∧ weight c r v ≤ 1 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
lemma weight_one {c v : E} {r : ℝ} (hr : 0 < r) (hv : dist v c ≤ 4*r) :
    weight c r v = 1 := by
  have h : 1 ≤ (5*r-dist v c)/r := (le_div_iff₀ hr).mpr (by linarith)
  simp [weight,min_eq_left h]
lemma weight_zero {c v : E} {r : ℝ} (hr : 0 < r) (hv : 5*r ≤ dist v c) :
    weight c r v = 0 := by
  have h : (5*r-dist v c)/r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
  exact max_eq_left ((min_le_right _ _).trans h)
lemma weight_cont (c : E) (r : ℝ) : Continuous (weight c r) := by unfold weight; fun_prop

def shift (c : E) (r : ℝ) (a b : E) (t : unitInterval) (v : E) : E :=
  v + ((t.val * weight c r v) • (b-a))
lemma shift_cont (c : E) (r : ℝ) (a b : E) : Continuous (fun p : unitInterval × E => shift c r a b p.1 p.2) := by
  unfold shift
  have h := (weight_cont c r).comp (continuous_snd : Continuous (Prod.snd : unitInterval × E → E))
  fun_prop
lemma shift_dist {c a b : E} {r : ℝ} (ha : dist a c < r) (hb : dist b c < r)
    (t : unitInterval) (v : E) : dist (shift c r a b t v) v < 2*r := by
  have h := weight_bounds c r v
  have h0 : 0 ≤ t.val * weight c r v := mul_nonneg t.property.1 h.1
  have h1 : t.val * weight c r v ≤ 1 := mul_le_one₀ t.property.2 h.1 h.2
  have hd : dist b a < 2*r := by linarith [dist_triangle_right b a c]
  simpa [shift,dist_eq_norm, norm_smul,Real.norm_eq_abs,abs_of_nonneg h0,abs_of_nonneg t.property.1,abs_of_nonneg h.1] using
    (le_trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg (b-a))) (one_mul ‖b-a‖).le).trans_lt (by simpa [dist_eq_norm] using hd)
lemma shift_target {c a b : E} {r : ℝ} (hr : 0 < r) (ha : dist a c < r) (hb : dist b c < r)
    {V : Set E} (hc : closedBall c (8*r) ⊆ V) {v : E} (hv : v ∈ V) (t : unitInterval) :
    shift c r a b t v ∈ V := by
  by_cases h : 5*r ≤ dist v c
  · simpa [shift,weight_zero hr h] using hv
  · apply hc
    rw [mem_closedBall]
    linarith [dist_triangle (shift c r a b t v) v c,shift_dist ha hb t v]
lemma shift_hit {c a b : E} {r : ℝ} (hr : 0 < r) (ha : dist a c < r) (hb : dist b c < r)
    {v : E} (h : shift c r a b 1 v = b) : v = a := by
  have hd := shift_dist ha hb 1 v
  rw [h, dist_comm] at hd
  have hv : dist v c ≤ 4*r := by linarith [dist_triangle v b c]
  have eq : v + (b-a) = b := by simpa [shift,weight_one hr hv] using h
  calc v = (v + (b-a)) - (b-a) := by abel
       _ = b - (b-a) := by rw [eq]
       _ = a := by abel

end LocalMove


open Set Metric Filter CategoryTheory
open scoped Topology
noncomputable section
namespace LocalMove

lemma chart_motion {M : Type} [TopologicalSpace M] [T2Space M]
    (e : OpenPartialHomeomorph M E) (c : E) {r : ℝ} (hr : 0 < r)
    (hV : closedBall c (8*r) ⊆ e.target)
    {a b : M} (ha : a ∈ e.source) (hb : b ∈ e.source)
    (ha' : dist (e a) c < r) (hb' : dist (e b) c < r) :
    ∃ f : TopCat.of M ⟶ TopCat.of M, Nonempty (TopCat.Homotopy (𝟙 _) f) ∧
      ∀ z, f z = b → z = a := by
  classical
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

lemma move_neighbors {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] (x : M) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ a ∈ U, ∀ b ∈ U,
      ∃ f : TopCat.of M ⟶ TopCat.of M, Nonempty (TopCat.Homotopy (𝟙 _) f) ∧
        ∀ z, f z = b → z = a := by
  let e := chartAt E x
  have hx : x ∈ e.source := mem_chart_source E x
  obtain ⟨s,hs,hsT⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let r := s/10
  have hr : 0 < r := by dsimp [r]; positivity
  have hV : closedBall (e x) (8*r) ⊆ e.target :=
    (closedBall_subset_ball (by dsimp [r]; linarith : 8*r < s)).trans hsT
  refine ⟨e.source ∩ e ⁻¹' ball (e x) r,e.isOpen_inter_preimage isOpen_ball,⟨hx,mem_ball_self hr⟩,?_⟩
  intro a ha b hb
  exact chart_motion e _ hr hV ha.1 hb.1 ha.2 hb.2

end LocalMove


open CategoryTheory Limits AlgebraicTopology Set
open scoped Simplicial Topology
noncomputable section
namespace LocalMove

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


abbrev HomF := (singularHomologyFunctor AddCommGrpCat.{0} 3).obj (AddCommGrpCat.of ℤ)
abbrev CF := (singularChainComplexFunctor AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℤ)
abbrev incX {M : Type} [TopologicalSpace M] (x : M) : TopCat.of ↥({x}ᶜ : Set M) ⟶ TopCat.of M :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

def rep {M : Type} [TopologicalSpace M] (a : HomF.obj (TopCat.of M)) (x : M) : Prop :=
  ∃ b, HomF.map (incX x) b = a

lemma transport {M : Type} [TopologicalSpace M] (a : HomF.obj (TopCat.of M)) {x y : M}
    (f : TopCat.of M ⟶ TopCat.of M) (hf : TopCat.Homotopy (𝟙 _) f)
    (hit : ∀ z, f z = y → z = x) : rep a x → rep a y := by
  rintro ⟨b,hb⟩
  let g := CategoryStruct.comp (incX x) f
  have hg (p : ↥({x}ᶜ : Set M)) : g p ∈ ({y}ᶜ : Set M) := fun h => p.property (hit p h)
  have homEq : HomF.map f = 𝟙 _ := by
    have e := hf.congr_homologyMap_singularChainComplexFunctor (AddCommGrpCat.of ℤ) 3
    change HomF.map (𝟙 (TopCat.of M)) = HomF.map f at e
    exact e.symm.trans (HomF.map_id _)
  have hc := ConcreteCategory.congr_hom (HomF.map_comp (incX x) f) b
  change HomF.map g b = HomF.map f (HomF.map (incX x) b) at hc
  rw [homEq,hb] at hc
  exact ⟨_,(map_factor g hg b).trans hc⟩

lemma vanish_of_rep {M : Type} [TopologicalSpace M] (a : HomF.obj (TopCat.of M)) (x : M)
    (h : rep a x) : HomologicalComplex.homologyMap (cokernel.π (CF.map (incX x))) 3 a = 0 := by
  obtain ⟨b,rfl⟩ := h
  let i := CF.map (incX x)
  let π := cokernel.π i
  have eq := HomologicalComplex.homologyMap_comp i π 3
  rw [show CategoryStruct.comp i π = 0 from cokernel.condition i,HomologicalComplex.homologyMap_zero] at eq
  exact ConcreteCategory.congr_hom eq.symm b

theorem propagate (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [ConnectedSpace M]
    (a : HomF.obj (TopCat.of M)) (h : ∃ x, HomologicalComplex.homologyMap (cokernel.π (CF.map (incX x))) 3 a = 0) :
    ∀ y, HomologicalComplex.homologyMap (cokernel.π (CF.map (incX y))) 3 a = 0 := by
  let S : Set M := fun x => rep a x
  have near (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∀ u ∈ U, ∀ v ∈ U, rep a u → rep a v := by
    obtain ⟨U,hU,hx,hm⟩ := move_neighbors x
    refine ⟨U,hU,hx,?_⟩
    intro u hu v hv
    obtain ⟨f,⟨hf⟩,hit⟩ := hm u hu v hv
    exact transport a f hf hit
  have ho : IsOpen S := isOpen_iff_forall_mem_open.mpr fun x hx => by
    obtain ⟨U,hU,hxU,hm⟩ := near x
    exact ⟨U,fun y hy => hm x hxU y hy hx,hU,hxU⟩
  have hc : IsOpen Sᶜ := isOpen_iff_forall_mem_open.mpr fun x hx => by
    obtain ⟨U,hU,hxU,hm⟩ := near x
    exact ⟨U,fun y hy h => hx (hm y hy x hxU h),hU,hxU⟩
  obtain ⟨x,hx⟩ := h
  have hn : S.Nonempty := ⟨x,point_lift M x a hx⟩
  have top : S = univ := (isClopen_iff.mp ⟨isOpen_compl_iff.mp hc,ho⟩).resolve_left hn.ne_empty
  intro y
  exact vanish_of_rep a y (show y ∈ S from top ▸ mem_univ y)

end LocalMove


theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_R1_H2_R1.H3 := LocalMove.propagate
