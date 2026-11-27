import OMAReductions.R_erdos_634_R1_H2_R1

/-!
# Erdos 634, step R1.H2.R1.H3: the RightRow case

Flattened from the Lean port of Beeson-Rosu / Bonfioli (formalizations of the triangle tiling
papers), restricted to the declarations this step uses.
-/

section
namespace Erdos634.SupportFace
open Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem mem_convexHull_max (f : E →ₗ[ℝ] ℝ) (c : ℝ) (s : Finset E)
    (hle : ∀ v ∈ s, f v ≤ c) {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) (hfx : f x = c) :
    x ∈ convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) := by
  classical
  rw [Finset.convexHull_eq] at hx
  obtain ⟨w, hw0, hw1, hcm⟩ := hx
  have hcomb : ∑ v ∈ s, w v • v = x := by
    rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hw1]; rfl
  have hdef : ∑ v ∈ s, w v * (c - f v) = 0 := by
    have hfsum : ∑ v ∈ s, w v * f v = c := by
      have : f (∑ v ∈ s, w v • v) = ∑ v ∈ s, w v * f v := by
        rw [map_sum]; simp [map_smul, smul_eq_mul]
      rw [hcomb] at this; rw [← this, hfx]
    calc ∑ v ∈ s, w v * (c - f v)
        = (∑ v ∈ s, w v) * c - ∑ v ∈ s, w v * f v := by
          rw [Finset.sum_mul]; rw [← Finset.sum_sub_distrib]; ring_nf
          exact Finset.sum_congr rfl (fun v _ => by ring)
      _ = 0 := by rw [hw1, hfsum]; ring
  have hterm : ∀ v ∈ s, w v * (c - f v) = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).mp hdef
    intro v hv
    exact mul_nonneg (hw0 v hv) (by linarith [hle v hv])
  have hsupp : ∀ v ∈ s, w v ≠ 0 → f v = c := by
    intro v hv hne
    rcases mul_eq_zero.mp (hterm v hv) with h | h
    · exact absurd h hne
    · linarith
  have hzero : ∀ v ∈ s, v ∉ s.filter (fun v => f v = c) → w v = 0 := by
    intro v hv hnot
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hv, hsupp v hv hne⟩)
  have hsub : s.filter (fun v => f v = c) ⊆ s := Finset.filter_subset _ _
  have hsum1 : ∑ v ∈ s.filter (fun v => f v = c), w v = 1 := by
    rw [Finset.sum_subset hsub hzero]; exact hw1
  rw [Finset.convexHull_eq]
  refine ⟨w, ?_, hsum1, ?_⟩
  · intro v hv; exact hw0 v (Finset.mem_filter.mp hv).1
  · rw [Finset.centerMass_eq_of_sum_1 _ _ hsum1]
    have : ∑ v ∈ s.filter (fun v => f v = c), w v • id v = ∑ v ∈ s, w v • v := by
      refine Finset.sum_subset hsub ?_
      intro v hv hnot; simp [hzero v hv hnot]
    rw [this]; exact hcomb
theorem contact_eq_face (f : E →ₗ[ℝ] ℝ) (c : ℝ) (s : Finset E)
    (hle : ∀ v ∈ s, f v ≤ c) :
    {x ∈ convexHull ℝ (s : Set E) | f x = c}
      = convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) := by
  classical
  ext x
  constructor
  · rintro ⟨hx, hfx⟩
    exact mem_convexHull_max f c s hle hx hfx
  · intro hx
    have hsub : ((s.filter (fun v => f v = c) : Finset E) : Set E) ⊆ (s : Set E) := by
      intro v hv; exact (Finset.mem_filter.mp hv).1
    refine ⟨convexHull_mono hsub hx, ?_⟩
    have : convexHull ℝ ((s.filter (fun v => f v = c) : Finset E) : Set E) ⊆ {y | f y = c} := by
      refine convexHull_min ?_ ?_
      · intro v hv; exact (Finset.mem_filter.mp hv).2
      · intro a ha b hb ta tb hta htb htab
        simp only [Set.mem_setOf_eq] at *
        rw [map_add, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul]
        linear_combination c * htab
    exact this hx
end Erdos634.SupportFace
end

section
namespace Erdos634.SegmentDense
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
private noncomputable def par (x b : E) (t : ℝ) : E := (1 - t) • x + t • b
private theorem par_mem_segment {x b : E} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    par x b t ∈ segment ℝ x b := by
  rw [segment_eq_image]
  exact ⟨t, ht, rfl⟩
private theorem par_dist {x b : E} (t : ℝ) : ‖par x b t - x‖ = |t| * ‖b - x‖ := by
  have : par x b t - x = t • (b - x) := by
    simp only [par, smul_sub, sub_smul, one_smul]; abel
  rw [this, norm_smul, Real.norm_eq_abs]
private theorem par_injOn {x b : E} (hxb : x ≠ b) : Function.Injective (par x b) := by
  intro s t hst
  have h : (s - t) • (b - x) = 0 := by
    have : par x b s - par x b t = (s - t) • (b - x) := by
      simp only [par, smul_sub, sub_smul, one_smul]; abel
    rw [← this, hst, sub_self]
  rcases smul_eq_zero.mp h with h1 | h2
  · linarith [sub_eq_zero.mp (by linarith [h1] : s - t = 0)]
  · exact absurd (sub_eq_zero.mp h2).symm hxb
theorem subset_closure_diff_finite {a b : E} (hab : a ≠ b) {F : Set E} (hF : F.Finite) :
    segment ℝ a b ⊆ closure (segment ℝ a b \ F) := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp, hxp⟩ : ∃ p, p ∈ ({a, b} : Set E) ∧ x ≠ p := by
    by_cases h : x = a
    · exact ⟨b, by simp, by rw [h]; exact hab⟩
    · exact ⟨a, by simp, h⟩
  have hpmem : p ∈ segment ℝ a b := by
    rcases hp with h | h
    · rw [h]; exact left_mem_segment ℝ a b
    · rw [h]; exact right_mem_segment ℝ a b
  have hseg : segment ℝ x p ⊆ segment ℝ a b :=
    (convex_segment a b).segment_subset hx hpmem
  have hnorm : 0 < ‖p - x‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (Ne.symm hxp)
  set δ : ℝ := min 1 (ε / (2 * ‖p - x‖)) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hinf : (Set.Ioo (0:ℝ) δ).Infinite := Set.Ioo_infinite hδ
  have himg : ((par x p) '' Set.Ioo (0:ℝ) δ).Infinite :=
    hinf.image ((par_injOn hxp).injOn)
  obtain ⟨y, hy, hyF⟩ := (himg.diff hF).nonempty
  obtain ⟨t, ht, rfl⟩ := hy
  refine ⟨par x p t, ⟨hseg (par_mem_segment ⟨le_of_lt ht.1, le_trans (le_of_lt ht.2) (min_le_left _ _)⟩), hyF⟩, ?_⟩
  rw [dist_comm, dist_eq_norm, par_dist, abs_of_pos ht.1]
  have h1 : t < ε / (2 * ‖p - x‖) := lt_of_lt_of_le ht.2 (min_le_right _ _)
  calc t * ‖p - x‖ < (ε / (2 * ‖p - x‖)) * ‖p - x‖ := by
        exact mul_lt_mul_of_pos_right h1 hnorm
    _ = ε / 2 := by field_simp
    _ < ε := by linarith
end Erdos634.SegmentDense
end

section
open scoped ENNReal
namespace Erdos634.Geometry
open MeasureTheory Set
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)
structure Tri where
  pts : Fin 3 → Plane
  indep : AffineIndependent ℝ pts
namespace Tri
def carrier (T : Tri) : Set Plane := convexHull ℝ (Set.range T.pts)
theorem convex (T : Tri) : Convex ℝ T.carrier := convex_convexHull ℝ _
theorem isCompact (T : Tri) : IsCompact T.carrier :=
  (Set.finite_range _).isCompact_convexHull ℝ
theorem measurableSet (T : Tri) : MeasurableSet T.carrier := T.isCompact.measurableSet
theorem nullMeasurableSet (T : Tri) : NullMeasurableSet T.carrier volume :=
  T.measurableSet.nullMeasurableSet
theorem volume_frontier (T : Tri) : volume (frontier T.carrier) = 0 :=
  T.convex.addHaar_frontier volume
theorem affineSpan_eq_top (T : Tri) : affineSpan ℝ T.carrier = ⊤ := by
  have h : affineSpan ℝ T.carrier = affineSpan ℝ (Set.range T.pts) :=
    affineSpan_convexHull _
  rw [h]
  exact T.indep.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)
theorem interior_nonempty (T : Tri) : (interior T.carrier).Nonempty :=
  T.convex.interior_nonempty_iff_affineSpan_eq_top.mpr T.affineSpan_eq_top
theorem volume_pos (T : Tri) : 0 < volume T.carrier :=
  (isOpen_interior.measure_pos volume T.interior_nonempty).trans_le
    (measure_mono interior_subset)
end Tri
structure Dissection (N : ℕ) where
  target : Tri
  tile : Fin N → Tri
  covers : (⋃ i, (tile i).carrier) = target.carrier
  interiors_disjoint :
    Pairwise fun i j => Disjoint (interior (tile i).carrier) (interior (tile j).carrier)
namespace Dissection
variable {N : ℕ}
theorem aedisjoint (D : Dissection N) {i j : Fin N} (hij : i ≠ j) :
    AEDisjoint volume (D.tile i).carrier (D.tile j).carrier := by
  have hsub : (D.tile i).carrier ∩ (D.tile j).carrier ⊆
      frontier (D.tile i).carrier ∪ frontier (D.tile j).carrier := by
    rintro x ⟨hxi, hxj⟩
    by_cases h1 : x ∈ interior (D.tile i).carrier
    · by_cases h2 : x ∈ interior (D.tile j).carrier
      · exfalso
        have hd : Disjoint (interior (D.tile i).carrier) (interior (D.tile j).carrier) :=
          D.interiors_disjoint hij
        exact Set.disjoint_left.mp hd h1 h2
      · exact Or.inr ⟨subset_closure hxj, h2⟩
    · exact Or.inl ⟨subset_closure hxi, h1⟩
  refine measure_mono_null hsub ?_
  exact measure_union_null (D.tile i).volume_frontier (D.tile j).volume_frontier
theorem volume_target (D : Dissection N) :
    volume D.target.carrier = ∑ i, volume (D.tile i).carrier := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N))) (f := fun i => (D.tile i).carrier)
    (fun _ _ _ _ hij => D.aedisjoint hij)
    (fun i _ => (D.tile i).nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), (D.tile i).carrier) = D.target.carrier := by
    rw [← D.covers]; simp
  rw [hU] at h
  exact h
theorem volume_target_of_congruent (D : Dissection N) (v : ℝ≥0∞)
    (hv : ∀ i, volume (D.tile i).carrier = v) :
    volume D.target.carrier = (N : ℝ≥0∞) * v := by
  rw [D.volume_target]
  simp [hv]
theorem pos (D : Dissection N) : 0 < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    have hz := D.volume_target
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hz
    exact absurd hz D.target.volume_pos.ne'
  · exact h
end Dissection
noncomputable def cornerAngle (p q r : Plane) : ℝ :=
  EuclideanGeometry.angle (V := Plane) p q r
theorem cornerAngle_sum (T : Tri) :
    cornerAngle (T.pts 1) (T.pts 0) (T.pts 2)
      + cornerAngle (T.pts 2) (T.pts 1) (T.pts 0)
      + cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi := by
  have h10 : T.pts 1 ≠ T.pts 0 := by
    intro h
    have : (1 : Fin 3) = 0 := T.indep.injective h
    exact absurd this (by decide)
  have key := EuclideanGeometry.angle_add_angle_add_angle_eq_pi
    (V := Plane) (p₁ := T.pts 0) (p₂ := T.pts 1) (T.pts 2) h10
  unfold cornerAngle
  rw [EuclideanGeometry.angle_comm (V := Plane) (T.pts 1) (T.pts 0) (T.pts 2),
      EuclideanGeometry.angle_comm (V := Plane) (T.pts 2) (T.pts 1) (T.pts 0),
      EuclideanGeometry.angle_comm (V := Plane) (T.pts 0) (T.pts 2) (T.pts 1)]
  linarith [key]
theorem angle_indep {α : ℝ} (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (A B : ℤ)
    (h : (A : ℝ) * α + (B : ℝ) * Real.pi = 0) : A = 0 ∧ B = 0 := by
  have hA : A = 0 := by
    by_contra hA0
    apply hirr
    have hAR : (A : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hA0
    refine ⟨((-B : ℤ) : ℚ) / ((A : ℤ) : ℚ), ?_⟩
    push_cast
    field_simp
    linarith
  refine ⟨hA, ?_⟩
  have h' : (B : ℝ) * Real.pi = 0 := by
    rw [hA] at h
    push_cast at h
    linarith
  rcases mul_eq_zero.mp h' with hb | hpi
  · exact_mod_cast hb
  · exact absurd hpi Real.pi_ne_zero
def HasAngleSums {N : ℕ} (D : Dissection N) (angleAt : Plane → Fin N → ℝ) : Prop :=
  (∀ v ∈ interior D.target.carrier, ∑ i, angleAt v i = 2 * Real.pi) ∧
  (∀ v ∈ frontier D.target.carrier, v ∉ Set.range D.target.pts →
    ∑ i, angleAt v i = Real.pi) ∧
  (∀ k : Fin 3, ∑ i, angleAt (D.target.pts k) i
    = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)))
def HasEdgeChains {N : ℕ} (D : Dissection N) (edgeOf : Fin N → Fin 3 → Set Plane) : Prop :=
  ∀ i : Fin 3, ∃ (part : Finset (Fin N × Fin 3)),
    (⋃ e ∈ part, edgeOf e.1 e.2) = segment ℝ (D.target.pts i) (D.target.pts (i + 1))
def Tri.edge (T : Tri) (i : Fin 3) : Set Plane := segment ℝ (T.pts i) (T.pts (i + 1))
theorem tile_contact_face (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hle : ∀ x ∈ T.carrier, f x ≤ c) :
    {x ∈ T.carrier | f x = c}
      = convexHull ℝ (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) :
          Set Plane) := by
  classical
  have hmem : ∀ v ∈ (Finset.univ.image T.pts), f v ≤ c := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hle _ (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hcar : T.carrier = convexHull ℝ ((Finset.univ.image T.pts : Finset Plane) : Set Plane) := by
    rw [Tri.carrier]; congr 1
    ext x; constructor
    · rintro ⟨i, rfl⟩; exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    · intro hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact ⟨i, rfl⟩
  rw [hcar]
  exact Erdos634.SupportFace.contact_eq_face f c _ hmem
theorem two_vertices_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hall : ∀ i, f (T.pts i) = c) : False := by
  have hsub : T.carrier ⊆ {x | f x = c} := by
    rw [Tri.carrier]
    refine convexHull_min ?_ ?_
    · rintro x ⟨i, rfl⟩; exact hall i
    · intro a ha b hb ta tb hta htb htab
      simp only [Set.mem_setOf_eq] at *
      rw [map_add, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul]
      linear_combination c * htab
  obtain ⟨x, hx⟩ := T.interior_nonempty
  have hxc : f x = c := hsub (interior_subset hx)
  obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (LinearMap.ext fun z => by simp [h z])
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  set t : ℝ := ε / (2 * ‖y‖) with ht
  have hynorm : 0 < ‖y‖ := by
    rcases eq_or_ne y 0 with rfl | hy0
    · simp at hy
    · exact norm_pos_iff.mpr hy0
  have htpos : 0 < t := by positivity
  have hdist : dist (x + t • y) x = t * ‖y‖ := by
    rw [dist_eq_norm]
    have hxy : x + t • y - x = t • y := by abel
    rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  have hmemball : x + t • y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, hdist]
    have hhalf : t * ‖y‖ = ε / 2 := by rw [ht]; field_simp
    rw [hhalf]; linarith
  have : f (x + t • y) = c := hsub (interior_subset (hball hmemball))
  rw [map_add, map_smul, hxc, smul_eq_mul] at this
  have : t * f y = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (ne_of_gt htpos)
  · exact hy h
theorem tile_subset_target (D : Dissection N) (j : Fin N) :
    (D.tile j).carrier ⊆ D.target.carrier := by
  rw [← D.covers]; exact Set.subset_iUnion (fun i => (D.tile i).carrier) j
theorem Tri.isClosed_edge (T : Tri) (k : Fin 3) : IsClosed (T.edge k) := by
  have hc : IsCompact (T.edge k) := by
    rw [Tri.edge, segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  exact hc.isClosed
theorem Tri.pair_eq_edge (T : Tri) {p q : Fin 3} (hpq : p ≠ q) :
    ∃ k, segment ℝ (T.pts p) (T.pts q) = T.edge k := by
  simp only [Tri.edge]
  fin_cases p <;> fin_cases q <;> simp_all <;>
    [ exact ⟨0, rfl⟩;
      exact ⟨2, segment_symm ℝ _ _⟩;
      exact ⟨0, segment_symm ℝ _ _⟩;
      exact ⟨1, rfl⟩;
      exact ⟨2, rfl⟩;
      exact ⟨1, segment_symm ℝ _ _⟩ ]
noncomputable def Tri.basis (T : Tri) : AffineBasis (Fin 3) ℝ Plane :=
  AffineBasis.mk T.pts T.indep (by
    have := T.affineSpan_eq_top
    rwa [Tri.carrier, affineSpan_convexHull] at this)
theorem exists_supporting (T : Tri) (i : Fin 3) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ x ∈ T.carrier, f x ≤ c) ∧
      f (T.pts i) = c ∧ f (T.pts (i + 1)) = c ∧ f (T.pts (i + 2)) < c := by
  classical
  set g : Plane →ᵃ[ℝ] ℝ := T.basis.coord (i + 2) with hg
  have hdecomp : ∀ x, g x = g.linear x + g 0 := by
    intro x; simpa using congrFun (AffineMap.decomp g) x
  have hb : ∀ j, g (T.pts j) = if i + 2 = j then 1 else 0 := by
    intro j; exact AffineBasis.coord_apply T.basis (i + 2) j
  have hne1 : i + 2 ≠ i := by fin_cases i <;> decide
  have hne2 : i + 2 ≠ i + 1 := by fin_cases i <;> decide
  have h0 : g (T.pts i) = 0 := by rw [hb]; simp [hne1]
  have h1 : g (T.pts (i + 1)) = 0 := by rw [hb]; simp [hne2]
  have h2 : g (T.pts (i + 2)) = 1 := by rw [hb]; simp
  have hnonneg : ∀ j, (0:ℝ) ≤ g (T.pts j) := by
    intro j; rw [hb]; split <;> norm_num
  refine ⟨-g.linear, g 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have hlin0 : g.linear = 0 := by
      have := congrArg Neg.neg hzero; simpa using this
    have ha := hdecomp (T.pts i)
    have hc := hdecomp (T.pts (i + 2))
    rw [hlin0] at ha hc
    simp only [LinearMap.zero_apply, zero_add] at ha hc
    rw [h0] at ha; rw [h2] at hc
    linarith
  · intro x hx
    rw [Tri.carrier] at hx
    show x ∈ {y : Plane | (-g.linear) y ≤ g 0}
    refine convexHull_min ?_ ?_ hx
    · rintro y ⟨j, rfl⟩
      simp only [Set.mem_setOf_eq, LinearMap.neg_apply]
      linarith [hdecomp (T.pts j), hnonneg j]
    · intro a ha b hb ta tb hta htb htab
      simp only [Set.mem_setOf_eq, LinearMap.neg_apply] at ha hb ⊢
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have key : -(ta * g.linear a + tb * g.linear b)
               = ta * (-g.linear a) + tb * (-g.linear b) := by ring
      rw [key]
      calc ta * (-g.linear a) + tb * (-g.linear b)
          ≤ ta * g 0 + tb * g 0 :=
            add_le_add (mul_le_mul_of_nonneg_left ha hta) (mul_le_mul_of_nonneg_left hb htb)
        _ = g 0 := by rw [← add_mul, htab, one_mul]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts i), h0]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts (i + 1)), h1]
  · simp only [LinearMap.neg_apply]; linarith [hdecomp (T.pts (i + 2)), h2]
theorem contact_is_edge (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ x ∈ T.carrier, f x ≤ c) {x : Plane} (hx : x ∈ T.carrier) (hfx : f x = c)
    (hxv : ∀ k, x ≠ T.pts k) :
    ∃ k, {y ∈ T.carrier | f y = c} = T.edge k := by
  classical
  set V : Finset (Fin 3) := Finset.univ.filter (fun k => f (T.pts k) = c) with hV
  have himg : (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) : Set Plane)
            = T.pts '' (V : Set (Fin 3)) := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hv
      obtain ⟨⟨k, _, hk⟩, hfv⟩ := hv
      refine ⟨k, ?_, hk⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter]
      exact ⟨Finset.mem_univ k, by rw [hk]; exact hfv⟩
    · rintro ⟨k, hkV, rfl⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter] at hkV
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨k, Finset.mem_univ k, rfl⟩, hkV.2⟩
  have hcontact : {y ∈ T.carrier | f y = c} = convexHull ℝ (T.pts '' (V : Set (Fin 3))) := by
    rw [tile_contact_face T f c hle, himg]
  have hxc : x ∈ convexHull ℝ (T.pts '' (V : Set (Fin 3))) := by
    rw [← hcontact]; exact ⟨hx, hfx⟩
  have hcard3 : V.card ≤ 3 := by
    have := Finset.card_le_card (Finset.subset_univ V)
    simpa using this
  interval_cases h : V.card
  · 
    rw [Finset.card_eq_zero] at h
    rw [h] at hxc; simp at hxc
  · 
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
    rw [hk] at hxc
    simp only [Finset.coe_singleton, Set.image_singleton, convexHull_singleton,
      Set.mem_singleton_iff] at hxc
    exact absurd hxc (hxv k)
  · 
    obtain ⟨p, q, hpq, hV2⟩ := Finset.card_eq_two.mp h
    obtain ⟨k, hk⟩ := T.pair_eq_edge hpq
    refine ⟨k, ?_⟩
    rw [hcontact, hV2]
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
    rw [convexHull_pair, hk]
  · 
    exfalso
    have hall : ∀ k, f (T.pts k) = c := by
      intro k
      have hmem : k ∈ V := by
        have : V = Finset.univ := Finset.eq_univ_of_card V (by simpa using h)
        rw [this]; exact Finset.mem_univ k
      simpa [hV, Finset.mem_filter] using hmem
    exact two_vertices_on_line T f c hf hall
theorem target_contact_side (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) {i : Fin 3}
    (hle : ∀ x ∈ T.carrier, f x ≤ c) (hi : f (T.pts i) = c) (hi1 : f (T.pts (i + 1)) = c)
    (hi2 : f (T.pts (i + 2)) < c) :
    {x ∈ T.carrier | f x = c} = segment ℝ (T.pts i) (T.pts (i + 1)) := by
  classical
  set V : Finset (Fin 3) := Finset.univ.filter (fun k => f (T.pts k) = c) with hV
  have hexh : ∀ k : Fin 3, k = i ∨ k = i + 1 ∨ k = i + 2 := by
    intro k; fin_cases i <;> fin_cases k <;> decide
  have hVeq : V = {i, i + 1} := by
    apply Finset.Subset.antisymm
    · intro k hk
      rw [hV, Finset.mem_filter] at hk
      rcases hexh k with rfl | rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · exact absurd hk.2 (by linarith)
    · intro k hk
      rw [hV, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_insert.mp hk with rfl | hk'
      · exact hi
      · rw [Finset.mem_singleton.mp hk']; exact hi1
  have himg : (((Finset.univ.image T.pts).filter (fun v => f v = c) : Finset Plane) : Set Plane)
            = T.pts '' (V : Set (Fin 3)) := by
    ext v
    constructor
    · intro hv
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image] at hv
      obtain ⟨⟨k, _, hk⟩, hfv⟩ := hv
      refine ⟨k, ?_, hk⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter]
      exact ⟨Finset.mem_univ k, by rw [hk]; exact hfv⟩
    · rintro ⟨k, hkV, rfl⟩
      rw [Finset.mem_coe, hV, Finset.mem_filter] at hkV
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨k, Finset.mem_univ k, rfl⟩, hkV.2⟩
  rw [tile_contact_face T f c hle, himg, hVeq]
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  rw [convexHull_pair]
theorem hasEdgeChains_edge (D : Dissection N) :
    HasEdgeChains D (fun j k => (D.tile j).edge k) := by
  classical
  intro i
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  set S : Set Plane := segment ℝ (D.target.pts i) (D.target.pts (i + 1)) with hSdef
  have hS : {x ∈ D.target.carrier | f x = c} = S :=
    target_contact_side D.target f c hle hi hi1 hi2
  set part : Finset (Fin N × Fin 3) :=
    Finset.univ.filter (fun e : Fin N × Fin 3 => (D.tile e.1).edge e.2 ⊆ S) with hpart
  refine ⟨part, ?_⟩
  apply Set.Subset.antisymm
  · 
    intro x hx
    obtain ⟨e, he, hxe⟩ := Set.mem_iUnion₂.mp hx
    have : (D.tile e.1).edge e.2 ⊆ S := by
      rw [hpart, Finset.mem_filter] at he; exact he.2
    exact this hxe
  · 
    have hFfin : (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2).Finite :=
      Set.finite_range _
    have hUclosed : IsClosed (⋃ e ∈ part, (D.tile e.1).edge e.2) :=
      Set.Finite.isClosed_biUnion (Finset.finite_toSet part)
        (fun e _ => (D.tile e.1).isClosed_edge e.2)
    have hnd : D.target.pts i ≠ D.target.pts (i + 1) := by
      intro h
      have hij : i = i + 1 := D.target.indep.injective h
      fin_cases i <;> exact absurd hij (by decide)
    have hkey : S \ (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2)
              ⊆ ⋃ e ∈ part, (D.tile e.1).edge e.2 := by
      rintro x ⟨hxS, hxF⟩
      have hxt : x ∈ D.target.carrier ∧ f x = c := by rw [← hS] at hxS; exact hxS
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp (by rw [D.covers]; exact hxt.1)
      have hlej : ∀ y ∈ (D.tile j).carrier, f y ≤ c :=
        fun y hy => hle y (tile_subset_target D j hy)
      have hxv : ∀ k, x ≠ (D.tile j).pts k := by
        intro k hk; exact hxF ⟨(j, k), hk.symm⟩
      obtain ⟨k, hk⟩ := contact_is_edge (D.tile j) f c hf hlej hxj hxt.2 hxv
      have hsub : (D.tile j).edge k ⊆ S := by
        rw [← hk, ← hS]
        rintro y ⟨hy1, hy2⟩
        exact ⟨tile_subset_target D j hy1, hy2⟩
      refine Set.mem_iUnion₂.mpr ⟨(j, k), ?_, ?_⟩
      · rw [hpart, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hsub⟩
      · rw [← hk]; exact ⟨hxj, hxt.2⟩
    calc S ⊆ closure (S \ (Set.range fun (jk : Fin N × Fin 3) => (D.tile jk.1).pts jk.2)) :=
          Erdos634.SegmentDense.subset_closure_diff_finite hnd hFfin
      _ ⊆ closure (⋃ e ∈ part, (D.tile e.1).edge e.2) := closure_mono hkey
      _ = _ := hUclosed.closure_eq
theorem Tri.hausdorff_edge (T : Tri) (k : Fin 3) :
    (MeasureTheory.Measure.hausdorffMeasure 1) (T.edge k) = edist (T.pts k) (T.pts (k + 1)) := by
  rw [Tri.edge]
  exact MeasureTheory.hausdorffMeasure_segment _ _
theorem Tri.carrier_eq_nonneg_coord (T : Tri) :
    T.carrier = {y | ∀ i, 0 ≤ T.basis.coord i y} := by
  have h : Set.range T.pts = Set.range (T.basis : Fin 3 → Plane) := rfl
  rw [Tri.carrier, h]
  exact T.basis.convexHull_eq_nonneg_coord
theorem Tri.inter_ball_eq_halfplane (T : Tri) (k : Fin 3) {x : Plane}
    (h1 : 0 < T.basis.coord (k + 1) x) (h2 : 0 < T.basis.coord (k + 2) x) :
    ∃ r > 0, T.carrier ∩ Metric.ball x r
           = {y | 0 ≤ T.basis.coord k y} ∩ Metric.ball x r := by
  have hfin : ∀ j i : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := by decide
  have hc1 : Continuous (T.basis.coord (k + 1)) := AffineMap.continuous_of_finiteDimensional _
  have hc2 : Continuous (T.basis.coord (k + 2)) := AffineMap.continuous_of_finiteDimensional _
  have hopen : IsOpen {y | 0 < T.basis.coord (k + 1) y ∧ 0 < T.basis.coord (k + 2) y} :=
    (isOpen_lt continuous_const hc1).inter (isOpen_lt continuous_const hc2)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x ⟨h1, h2⟩
  refine ⟨r, hr, ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, T.carrier_eq_nonneg_coord]
  constructor
  · rintro ⟨hy, hyb⟩; exact ⟨hy k, hyb⟩
  · rintro ⟨hyk, hyb⟩
    refine ⟨fun i => ?_, hyb⟩
    obtain ⟨hp1, hp2⟩ := hball hyb
    rcases hfin k i with rfl | rfl | rfl
    · exact hyk
    · exact hp1.le
    · exact hp2.le
theorem Tri.ball_subset_of_pos (T : Tri) {x : Plane}
    (hpos : ∀ i, 0 < T.basis.coord i x) :
    ∃ r > 0, Metric.ball x r ⊆ T.carrier := by
  have hopen : IsOpen {y : Plane | ∀ i, 0 < T.basis.coord i y} := by
    have : {y : Plane | ∀ i, 0 < T.basis.coord i y} = ⋂ i, {y | 0 < T.basis.coord i y} := by
      ext y; simp [Set.mem_iInter]
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt continuous_const (AffineMap.continuous_of_finiteDimensional _)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hpos
  refine ⟨r, hr, fun y hy => ?_⟩
  rw [T.carrier_eq_nonneg_coord]
  exact fun i => (hball hy i).le
theorem Tri.ball_disjoint_of_neg (T : Tri) {x : Plane} {k : Fin 3}
    (hneg : T.basis.coord k x < 0) :
    ∃ r > 0, Metric.ball x r ∩ T.carrier = ∅ := by
  have hopen : IsOpen {y : Plane | T.basis.coord k y < 0} :=
    isOpen_lt (AffineMap.continuous_of_finiteDimensional _) continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hneg
  refine ⟨r, hr, Set.eq_empty_iff_forall_notMem.mpr ?_⟩
  rintro y ⟨hy1, hy2⟩
  rw [T.carrier_eq_nonneg_coord] at hy2
  exact absurd (hy2 k) (not_le.mpr (hball hy1))
theorem volume_halfspace_inter_ball (L : Plane →ₗ[ℝ] ℝ) (hL : L ≠ 0) (r : ℝ) :
    2 * volume ({v : Plane | 0 ≤ L v} ∩ Metric.ball 0 r) = volume (Metric.ball (0 : Plane) r) := by
  classical
  have hcont : Continuous L := L.continuous_of_finiteDimensional
  set A : Set Plane := {v | 0 ≤ L v} ∩ Metric.ball 0 r with hAdef
  set B : Set Plane := {v | L v ≤ 0} ∩ Metric.ball 0 r with hBdef
  have hBmeas : MeasurableSet B :=
    ((isClosed_le hcont continuous_const).measurableSet).inter Metric.isOpen_ball.measurableSet
  have hBA : B = (fun v : Plane => (-1 : ℝ) • v) ⁻¹' A := by
    ext v
    simp only [hAdef, hBdef, Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq,
      Metric.mem_ball, dist_zero_right, neg_one_smul, map_neg, norm_neg, neg_nonneg]
  have hvolB : volume B = volume A := by
    rw [hBA, Measure.addHaar_preimage_smul volume (by norm_num : (-1 : ℝ) ≠ 0)]
    simp
  have hunion : A ∪ B = Metric.ball (0 : Plane) r := by
    ext v
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro hv
      rcases le_total (0 : ℝ) (L v) with h | h
      · exact Or.inl ⟨h, hv⟩
      · exact Or.inr ⟨h, hv⟩
  have hker : LinearMap.ker L ≠ ⊤ := fun h => hL (LinearMap.ker_eq_top.mp h)
  have hinter : volume (A ∩ B) = 0 := by
    refine measure_mono_null (fun v hv => ?_) (Measure.addHaar_submodule volume _ hker)
    exact le_antisymm hv.2.1 hv.1.1
  have hie := measure_union_add_inter (μ := volume) A hBmeas
  rw [hunion, hinter, hvolB, add_zero] at hie
  rw [hie, two_mul]
theorem volume_halfplane_inter_ball_at (g : Plane →ᵃ[ℝ] ℝ) (hL : g.linear ≠ 0)
    {x : Plane} (hx : g x = 0) (r : ℝ) :
    2 * volume ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r) = volume (Metric.ball x r) := by
  have hg : ∀ v : Plane, g (x + v) = g.linear v := by
    intro v
    have h := g.map_vadd x v
    simpa [add_comm, hx] using h
  have hballpre : (fun v : Plane => x + v) ⁻¹' Metric.ball x r = Metric.ball 0 r := by
    ext v; simp [Metric.mem_ball, dist_eq_norm, dist_zero_right]
  have hpre : (fun v : Plane => x + v) ⁻¹' ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)
            = {v : Plane | 0 ≤ g.linear v} ∩ Metric.ball 0 r := by
    rw [Set.preimage_inter, hballpre]
    congr 1
    ext v; simp only [Set.mem_preimage, Set.mem_setOf_eq, hg]
  calc 2 * volume ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)
      = 2 * volume ((fun v : Plane => x + v) ⁻¹' ({y : Plane | 0 ≤ g y} ∩ Metric.ball x r)) := by
        rw [measure_preimage_add]
    _ = 2 * volume ({v : Plane | 0 ≤ g.linear v} ∩ Metric.ball 0 r) := by rw [hpre]
    _ = volume (Metric.ball (0 : Plane) r) := volume_halfspace_inter_ball _ hL r
    _ = volume (Metric.ball x r) := by rw [← hballpre, measure_preimage_add]
theorem Tri.coord_linear_ne_zero (T : Tri) (k : Fin 3) : (T.basis.coord k).linear ≠ 0 := by
  intro h
  have hne : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have e1 : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq k
  have e2 : T.basis.coord k (T.pts (k + 1)) = 0 := T.basis.coord_apply_ne (hne k)
  have hdiff : T.basis.coord k (T.pts k) - T.basis.coord k (T.pts (k + 1)) = 0 := by
    have hv := (T.basis.coord k).linearMap_vsub (T.pts k) (T.pts (k + 1))
    rw [h] at hv
    simpa using hv.symm
  rw [e1, e2] at hdiff
  norm_num at hdiff
theorem inter_ball_mono {A B : Set Plane} {x : Plane} {r : ℝ}
    (h : A ∩ Metric.ball x r = B ∩ Metric.ball x r) {r' : ℝ} (hr' : r' ≤ r) :
    A ∩ Metric.ball x r' = B ∩ Metric.ball x r' := by
  have hsub : Metric.ball x r' ⊆ Metric.ball x r := Metric.ball_subset_ball hr'
  ext y
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨hy, hb⟩; exact ⟨((Set.ext_iff.mp h y).mp ⟨hy, hsub hb⟩).1, hb⟩
  · rintro ⟨hy, hb⟩; exact ⟨((Set.ext_iff.mp h y).mpr ⟨hy, hsub hb⟩).1, hb⟩
theorem Tri.volume_inter_ball_edge (T : Tri) (k : Fin 3) {x : Plane}
    (h0 : T.basis.coord k x = 0)
    (h1 : 0 < T.basis.coord (k + 1) x) (h2 : 0 < T.basis.coord (k + 2) x) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      2 * volume (T.carrier ∩ Metric.ball x r') = volume (Metric.ball x r') := by
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_halfplane k h1 h2
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  rw [inter_ball_mono hEq hle]
  exact volume_halfplane_inter_ball_at (T.basis.coord k) (T.coord_linear_ne_zero k) h0 r'
theorem Tri.volume_inter_ball_interior (T : Tri) {x : Plane}
    (hpos : ∀ i, 0 < T.basis.coord i x) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball x r') = volume (Metric.ball x r') := by
  obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  congr 1
  exact Set.inter_eq_self_of_subset_right
    (fun y hy => hsub (Metric.ball_subset_ball hle hy))
theorem Tri.volume_inter_ball_exterior (T : Tri) {x : Plane} {k : Fin 3}
    (hneg : T.basis.coord k x < 0) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball x r') = 0 := by
  obtain ⟨r, hr, hemp⟩ := T.ball_disjoint_of_neg hneg
  refine ⟨r, hr, fun r' _ hle => ?_⟩
  have : T.carrier ∩ Metric.ball x r' = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy1, hy2⟩
    have : y ∈ Metric.ball x r ∩ T.carrier := ⟨Metric.ball_subset_ball hle hy2, hy1⟩
    rw [hemp] at this
    exact this
  rw [this, measure_empty]
theorem Dissection.volume_ball_eq_sum {N : ℕ} (D : Dissection N) {x : Plane} {r : ℝ}
    (hball : Metric.ball x r ⊆ D.target.carrier) :
    volume (Metric.ball x r) = ∑ i, volume ((D.tile i).carrier ∩ Metric.ball x r) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ Metric.ball x r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ Metric.ball x r))
          = Metric.ball x r := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
    exact Set.inter_eq_self_of_subset_right hball
  rw [hU] at h
  exact h
theorem local_degree_eq {V : ℝ≥0∞} (hV0 : V ≠ 0) (hVt : V ≠ ⊤) {k m : ℕ}
    (h : (k : ℝ≥0∞) * V + (m : ℝ≥0∞) * (2 * V) = 2 * V) :
    k + 2 * m = 2 := by
  have hcast : ((k + 2 * m : ℕ) : ℝ≥0∞) * V = ((2 : ℕ) : ℝ≥0∞) * V := by
    push_cast
    rw [← h]; ring
  exact_mod_cast (ENNReal.mul_left_inj hV0 hVt).mp hcast
theorem local_degree_two {k m : ℕ} (hk : 1 ≤ k) (h : k + 2 * m = 2) : k = 2 ∧ m = 0 := by
  omega
theorem Tri.eq_vertex_of_two_coords_zero (T : Tri) {x : Plane} {j k : Fin 3} (hjk : j ≠ k)
    (hj : T.basis.coord j x = 0) (hk : T.basis.coord k x = 0) :
    ∃ m, x = T.pts m := by
  classical
  have key : ∀ u v : Fin 3, u ≠ v →
      ∃ m : Fin 3, m ≠ u ∧ m ≠ v ∧ ∀ b : Fin 3, b ≠ m → b = u ∨ b = v := by decide
  obtain ⟨m, hmj, hmk, hall⟩ := key j k hjk
  have hzero : ∀ b : Fin 3, b ≠ m → T.basis.coord b x = 0 := by
    intro b hb; rcases hall b hb with rfl | rfl
    · exact hj
    · exact hk
  have hm : T.basis.coord m x = 1 := by
    rw [← T.basis.sum_coord_apply_eq_one x]
    exact (Finset.sum_eq_single_of_mem m (Finset.mem_univ m)
      (fun b _ hb => hzero b hb)).symm
  refine ⟨m, T.basis.ext_elem (fun i => ?_)⟩
  by_cases hi : i = m
  · rw [hi, hm]; exact (T.basis.coord_apply_eq m).symm
  · rw [hzero i hi]; exact (T.basis.coord_apply_ne hi).symm
theorem Tri.classify (T : Tri) {x : Plane} (hx : ∀ k, x ≠ T.pts k) :
    (∀ i, 0 < T.basis.coord i x)
  ∨ (∃ k, T.basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j x)
  ∨ (∃ k, T.basis.coord k x < 0) := by
  classical
  by_cases hneg : ∃ k, T.basis.coord k x < 0
  · exact Or.inr (Or.inr hneg)
  push_neg at hneg
  by_cases hpos : ∀ i, 0 < T.basis.coord i x
  · exact Or.inl hpos
  push_neg at hpos
  obtain ⟨k, hk⟩ := hpos
  have hk0 : T.basis.coord k x = 0 := le_antisymm hk (hneg k)
  refine Or.inr (Or.inl ⟨k, hk0, fun j hj => ?_⟩)
  rcases (hneg j).lt_or_eq with h | h
  · exact h
  · 
    exact absurd (T.eq_vertex_of_two_coords_zero hj h.symm hk0) (by
      rintro ⟨m, rfl⟩; exact hx m rfl)
theorem exists_common_radius {N : ℕ} (hN : 0 < N) (f : Fin N → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ r > 0, ∀ i, r ≤ f i := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne f, ?_, fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  rw [gt_iff_lt, Finset.lt_inf'_iff]
  exact fun i _ => hf i
theorem Dissection.local_balance {N : ℕ} (D : Dissection N) {x : Plane} {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball x r ⊆ D.target.carrier)
    (E I : Finset (Fin N)) (hdisj : Disjoint E I)
    (hE : ∀ i ∈ E, 2 * volume ((D.tile i).carrier ∩ Metric.ball x r) = volume (Metric.ball x r))
    (hI : ∀ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = volume (Metric.ball x r))
    (hrest : ∀ i ∈ (Finset.univ : Finset (Fin N)), i ∉ E ∪ I →
      volume ((D.tile i).carrier ∩ Metric.ball x r) = 0)
    (hEne : E.Nonempty) :
    E.card = 2 ∧ I.card = 0 := by
  classical
  set V : ℝ≥0∞ := volume (Metric.ball x r) with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume x hr).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  have hsum : ∑ i ∈ E ∪ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = V := by
    rw [Finset.sum_subset (Finset.subset_univ (E ∪ I)) hrest]
    exact (D.volume_ball_eq_sum hball).symm
  have hsplit : ∑ i ∈ E ∪ I, volume ((D.tile i).carrier ∩ Metric.ball x r)
      = (∑ i ∈ E, volume ((D.tile i).carrier ∩ Metric.ball x r))
        + ∑ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) :=
    Finset.sum_union hdisj
  have hEsum : 2 * ∑ i ∈ E, volume ((D.tile i).carrier ∩ Metric.ball x r) = (E.card : ℝ≥0∞) * V := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hE, Finset.sum_const, nsmul_eq_mul]
  have hIsum : ∑ i ∈ I, volume ((D.tile i).carrier ∩ Metric.ball x r) = (I.card : ℝ≥0∞) * V := by
    rw [Finset.sum_congr rfl hI, Finset.sum_const, nsmul_eq_mul]
  rw [hsplit] at hsum
  have hkey : (E.card : ℝ≥0∞) * V + (I.card : ℝ≥0∞) * (2 * V) = 2 * V := by
    have h1 : (I.card : ℝ≥0∞) * (2 * V) = 2 * ((I.card : ℝ≥0∞) * V) := by ring
    rw [h1, ← hEsum, ← hIsum, ← mul_add, hsum]
  have hcount : E.card + 2 * I.card = 2 := local_degree_eq hV0 hVt hkey
  exact local_degree_two (Finset.card_pos.mpr hEne) hcount
def OnEdge {N : ℕ} (D : Dissection N) (x : Plane) (i : Fin N) : Prop :=
  ∃ k, (D.tile i).basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < (D.tile i).basis.coord j x
def Inside {N : ℕ} (D : Dissection N) (x : Plane) (i : Fin N) : Prop :=
  ∀ j, 0 < (D.tile i).basis.coord j x
theorem Dissection.local_contribution {N : ℕ} (D : Dissection N) {x : Plane} (i : Fin N)
    (hxv : ∀ k, x ≠ (D.tile i).pts k) :
    ∃ ri > 0, ∀ r', 0 < r' → r' ≤ ri →
      (OnEdge D x i →
        2 * volume ((D.tile i).carrier ∩ Metric.ball x r') = volume (Metric.ball x r'))
    ∧ (Inside D x i →
        volume ((D.tile i).carrier ∩ Metric.ball x r') = volume (Metric.ball x r'))
    ∧ (¬ OnEdge D x i → ¬ Inside D x i →
        volume ((D.tile i).carrier ∩ Metric.ball x r') = 0) := by
  classical
  rcases (D.tile i).classify hxv with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hkneg⟩
  · 
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_interior hpos
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun hE => ?_, fun _ => h r' h1 h2, fun _ hI => absurd hpos hI⟩⟩
    obtain ⟨m, hm, -⟩ := hE
    exact absurd hm (ne_of_gt (hpos m))
  · 
    have hne : ∀ j : Fin 3, j + 1 ≠ j ∧ j + 2 ≠ j := by decide
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_edge k hk0
      (hkpos _ (hne k).1) (hkpos _ (hne k).2)
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun _ => h r' h1 h2, fun hI => ?_, fun hE _ => ?_⟩⟩
    · exact absurd hk0 (ne_of_gt (hI k))
    · exact absurd ⟨k, hk0, hkpos⟩ hE
  · 
    obtain ⟨r, hr, h⟩ := (D.tile i).volume_inter_ball_exterior hkneg
    refine ⟨r, hr, fun r' h1 h2 => ⟨fun hE => ?_, fun hI => ?_, fun _ _ => h r' h1 h2⟩⟩
    · obtain ⟨m, hm, hrest⟩ := hE
      by_cases hmk : k = m
      · rw [hmk] at hkneg; exact absurd hm (ne_of_lt hkneg)
      · exact absurd (hrest k hmk) (not_lt.mpr hkneg.le)
    · exact absurd (hI k) (not_lt.mpr hkneg.le)
open scoped Classical in
theorem Dissection.two_tiles_at_edge_point {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    (hEne : (Finset.univ.filter (fun i => OnEdge D x i)).Nonempty) :
    (Finset.univ.filter (fun i => OnEdge D x i)).card = 2
      ∧ (Finset.univ.filter (fun i => Inside D x i)).card = 0 := by
  classical
  choose ri hri hcontrib using fun i => D.local_contribution i (hxv i)
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius hN ri hri
  refine D.local_balance (x := x) (r := min R r0) (lt_min hR hr0) ?_ _ _ ?_ ?_ ?_ ?_ hEne
  · exact (Metric.ball_subset_ball (min_le_left _ _)).trans hRt
  · 
    rw [Finset.disjoint_left]
    intro i hiE hiI
    obtain ⟨m, hm, -⟩ := (Finset.mem_filter.mp hiE).2
    exact absurd hm (ne_of_gt ((Finset.mem_filter.mp hiI).2 m))
  · exact fun i hi => (hcontrib i _ (lt_min hR hr0)
      ((min_le_right R r0).trans (hr0le i))).1 (Finset.mem_filter.mp hi).2
  · exact fun i hi => (hcontrib i _ (lt_min hR hr0)
      ((min_le_right R r0).trans (hr0le i))).2.1 (Finset.mem_filter.mp hi).2
  · intro i _ hi
    rw [Finset.mem_union, not_or] at hi
    exact (hcontrib i _ (lt_min hR hr0) ((min_le_right R r0).trans (hr0le i))).2.2
      (fun h => hi.1 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))
      (fun h => hi.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩))
noncomputable def Tri.det (T : Tri) : ℝ :=
  (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1 - (T.pts 1 - T.pts 0) 1 * (T.pts 2 - T.pts 0) 0
noncomputable def Tri.leftDir (T : Tri) (k : Fin 3) : Plane :=
  if 0 < T.det then T.pts (k + 1) - T.pts k else T.pts k - T.pts (k + 1)
theorem Tri.leftDir_ne_zero (T : Tri) (k : Fin 3) : T.leftDir k ≠ 0 := by
  have hsucc : ∀ j : Fin 3, j ≠ j + 1 := by decide
  have hne : T.pts k ≠ T.pts (k + 1) := fun h => hsucc k (T.indep.injective h)
  unfold Tri.leftDir
  split
  · exact sub_ne_zero.mpr (Ne.symm hne)
  · exact sub_ne_zero.mpr hne
def cross (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0
@[simp] theorem cross_neg_left (u v : Plane) : cross (-u) v = - cross u v := by
  simp only [cross]; simp; ring
@[simp] theorem cross_self (u : Plane) : cross u u = 0 := by simp only [cross]; ring
@[simp] theorem cross_zero_right (u : Plane) : cross u 0 = 0 := by simp only [cross]; simp
theorem cross_add_right (u v w : Plane) : cross u (v + w) = cross u v + cross u w := by
  simp only [cross]; simp; ring
theorem cross_smul_right (t : ℝ) (u v : Plane) : cross u (t • v) = t * cross u v := by
  simp only [cross]; simp; ring
theorem cross_sum_right {n : ℕ} (u : Plane) (g : Fin n → Plane) :
    cross u (∑ i, g i) = ∑ i, cross u (g i) := by
  classical
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Fin.sum_univ_castSucc, cross_add_right, ih, Fin.sum_univ_castSucc]
theorem Tri.det_cyclic (T : Tri) (k : Fin 3) :
    cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts k) = T.det := by
  fin_cases k <;> simp [cross, Tri.det] <;> ring
theorem Tri.coord_mul_det (T : Tri) (k : Fin 3) (y : Plane) :
    T.basis.coord (k + 2) y * T.det = cross (T.pts (k + 1) - T.pts k) (y - T.pts k) := by
  have hsum : ∑ i, T.basis.coord i y = 1 := T.basis.sum_coord_apply_eq_one y
  have hy : ∑ i, T.basis.coord i y • T.pts i = y := T.basis.linear_combination_coord_eq_self y
  have hdec : y - T.pts k = ∑ i, T.basis.coord i y • (T.pts i - T.pts k) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hy, ← Finset.sum_smul, hsum, one_smul]
  rw [hdec, cross_sum_right]
  have hk   : cross (T.pts (k + 1) - T.pts k) (T.pts k - T.pts k) = 0 := by simp
  have hk1  : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1) - T.pts k) = 0 := cross_self _
  have hk2  := T.det_cyclic k
  have hfin : ∀ j : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by
    have : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
    exact fun j => this k j
  rw [Finset.sum_eq_single (k + 2)]
  · rw [cross_smul_right, hk2]
  · intro j _ hj
    rcases hfin j with rfl | rfl | rfl
    · rw [cross_smul_right, hk, mul_zero]
    · rw [cross_smul_right, hk1, mul_zero]
    · exact absurd rfl hj
  · intro h; exact absurd (Finset.mem_univ _) h
theorem Tri.leftDir_eq_or (T : Tri) (k : Fin 3) :
    T.leftDir k = T.pts (k + 1) - T.pts k ∨ T.leftDir k = -(T.pts (k + 1) - T.pts k) := by
  unfold Tri.leftDir; split
  · exact Or.inl rfl
  · right; abel
theorem Tri.det_ne_zero (T : Tri) : T.det ≠ 0 := by
  intro h
  have hall : ∀ w : Plane, cross (T.pts 1 - T.pts 0) w = 0 := by
    intro w
    have hid := T.coord_mul_det 0 (T.pts 0 + w)
    simp only [h, mul_zero, add_sub_cancel_left] at hid
    exact hid.symm
  have h0 : (T.pts 1 - T.pts 0) 0 = 0 := by
    have hw := hall (EuclideanSpace.single 1 (1 : ℝ))
    simpa [cross] using hw
  have h1 : (T.pts 1 - T.pts 0) 1 = 0 := by
    have hw := hall (EuclideanSpace.single 0 (1 : ℝ))
    simp [cross] at hw
    simp only [PiLp.sub_apply]
    linarith
  have hzero : T.pts 1 - T.pts 0 = 0 := by
    ext i; fin_cases i
    · simpa using h0
    · simpa using h1
  have hne : (0 : Fin 3) ≠ 1 := by decide
  exact hne (T.indep.injective (sub_eq_zero.mp hzero).symm)
theorem Tri.interior_left_of_leftDir (T : Tri) (k : Fin 3) {y : Plane}
    (hy : ∀ i, 0 < T.basis.coord i y) :
    0 < cross (T.leftDir k) (y - T.pts k) := by
  have hdet : T.det ≠ 0 := T.det_ne_zero
  have hid := T.coord_mul_det k y
  have hc : 0 < T.basis.coord (k + 2) y := hy _
  unfold Tri.leftDir
  split
  · rename_i hpos
    rw [← hid]; exact mul_pos hc hpos
  · rename_i hnpos
    have hneg : T.det < 0 := lt_of_le_of_ne (not_lt.mp hnpos) hdet
    have hflip : T.pts k - T.pts (k + 1) = -(T.pts (k + 1) - T.pts k) := (neg_sub _ _).symm
    rw [hflip, cross_neg_left, ← hid]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hc hneg)
theorem proportional_of_ker_le (f g : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0)
    (h : ∀ v, f v = 0 → g v = 0) : ∃ c : ℝ, ∀ w, g w = c * f w := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hf (LinearMap.ext fun w => by simpa using hcon w)
  refine ⟨g v / f v, fun w => ?_⟩
  have hker : f (w - (f w / f v) • v) = 0 := by
    simp [map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  have := h _ hker
  simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
  rw [this]
  field_simp
theorem proportional_of_disjoint_pos (L₁ L₂ : Plane →ₗ[ℝ] ℝ) (h₁ : L₁ ≠ 0) (h₂ : L₂ ≠ 0)
    (hdisj : ∀ v, ¬(0 < L₁ v ∧ 0 < L₂ v)) :
    ∃ c : ℝ, c < 0 ∧ ∀ v, L₂ v = c * L₁ v := by
  obtain ⟨u, hu⟩ : ∃ u, 0 < L₁ u := by
    obtain ⟨w, hw⟩ : ∃ w, L₁ w ≠ 0 := by
      by_contra hc; push_neg at hc
      exact h₁ (LinearMap.ext fun w => by simpa using hc w)
    rcases lt_or_gt_of_ne hw with hneg | hpos
    · exact ⟨-w, by simpa using hneg⟩
    · exact ⟨w, hpos⟩
  have hker : ∀ v, L₁ v = 0 → L₂ v = 0 := by
    intro v hv
    by_contra hne
    obtain ⟨v', hv1, hv2⟩ : ∃ v', L₁ v' = 0 ∧ 0 < L₂ v' := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨-v, by simpa using hv, by simpa using hlt⟩
      · exact ⟨v, hv, hgt⟩
    by_cases hpos : 0 ≤ L₂ u
    · refine hdisj (u + v') ⟨?_, ?_⟩
      · rw [map_add, hv1, add_zero]; exact hu
      · rw [map_add]; linarith
    · have hnegu : L₂ u < 0 := not_le.mp hpos
      have hepos : 0 < L₂ v' / (-2 * L₂ u) := div_pos hv2 (by linarith)
      refine hdisj ((L₂ v' / (-2 * L₂ u)) • u + v') ⟨?_, ?_⟩
      · rw [map_add, map_smul, hv1, smul_eq_mul, add_zero]
        exact mul_pos hepos hu
      · rw [map_add, map_smul, smul_eq_mul]
        have hune : L₂ u ≠ 0 := ne_of_lt hnegu
        have hcalc : L₂ v' / (-2 * L₂ u) * L₂ u = -(L₂ v') / 2 := by
          field_simp
        rw [hcalc]; linarith
  obtain ⟨c, hc⟩ := proportional_of_ker_le L₁ L₂ h₁ hker
  have hcne : c ≠ 0 := by
    intro h; subst h
    exact h₂ (LinearMap.ext fun v => by simpa using hc v)
  refine ⟨c, ?_, hc⟩
  rcases lt_or_gt_of_ne hcne with hlt | hgt
  · exact hlt
  · exact absurd ⟨hu, by rw [hc u]; exact mul_pos hgt hu⟩ (hdisj u)
theorem Tri.mem_interior_of_cross_pos (T : Tri) {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (hother : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    {v : Plane} (hv : 0 < cross (T.leftDir (m + 1)) v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → x + ε • v ∈ interior T.carrier := by
  have hidx : (m + 1) + 2 = m := by fin_cases m <;> rfl
  set w : Plane := T.pts ((m + 1) + 1) - T.pts (m + 1) with hw
  have hcoord : ∀ ε : ℝ, T.basis.coord m (x + ε • v) * T.det = ε * cross w v := by
    intro ε
    have h1 := T.coord_mul_det (m + 1) (x + ε • v)
    have h2 := T.coord_mul_det (m + 1) x
    rw [hidx] at h1 h2
    rw [hm, zero_mul] at h2
    have hsplit : x + ε • v - T.pts (m + 1) = (x - T.pts (m + 1)) + ε • v := by abel
    rw [hsplit, cross_add_right, cross_smul_right, ← hw, ← h2, zero_add] at h1
    exact h1
  have hvne : v ≠ 0 := by rintro rfl; simp at hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have hmpos : ∀ ε : ℝ, 0 < ε → 0 < T.basis.coord m (x + ε • v) := by
    intro ε hε
    have hdet := T.det_ne_zero
    rcases lt_or_gt_of_ne hdet with hneg | hpos
    · have hlv : T.leftDir (m + 1) = -w := by
        unfold Tri.leftDir; rw [if_neg (not_lt.mpr hneg.le), hw]; abel
      rw [hlv, cross_neg_left] at hv
      have hcw : cross w v < 0 := by linarith
      have := hcoord ε
      nlinarith [mul_pos hε (neg_pos.mpr hcw)]
    · have hlv : T.leftDir (m + 1) = w := by
        unfold Tri.leftDir; rw [if_pos hpos, hw]
      rw [hlv] at hv
      have := hcoord ε
      nlinarith [mul_pos hε hv]
  have hopen : IsOpen {y : Plane | ∀ j, j ≠ m → 0 < T.basis.coord j y} := by
    have heq : {y : Plane | ∀ j, j ≠ m → 0 < T.basis.coord j y}
        = ⋂ j : Fin 3, {y : Plane | j ≠ m → 0 < T.basis.coord j y} := by
      ext y; simp [Set.mem_iInter]
    rw [heq]
    refine isOpen_iInter_of_finite fun j => ?_
    by_cases hj : j = m
    · have : {y : Plane | j ≠ m → 0 < T.basis.coord j y} = Set.univ := by ext y; simp [hj]
      rw [this]; exact isOpen_univ
    · have : {y : Plane | j ≠ m → 0 < T.basis.coord j y} = {y | 0 < T.basis.coord j y} := by
        ext y; simp [hj]
      rw [this]
      exact isOpen_lt continuous_const (AffineMap.continuous_of_finiteDimensional _)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hother
  refine ⟨r / ‖v‖, div_pos hr hvpos, fun ε hε hlt => ?_⟩
  have hin : x + ε • v ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : x + ε • v - x = ε • v := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    calc ε * ‖v‖ < (r / ‖v‖) * ‖v‖ := by
          exact mul_lt_mul_of_pos_right hlt hvpos
      _ = r := div_mul_cancel₀ r (ne_of_gt hvpos)
  have hallpos : ∀ j, 0 < T.basis.coord j (x + ε • v) := by
    intro j
    by_cases hj : j = m
    · rw [hj]; exact hmpos ε hε
    · exact hball hin j hj
  obtain ⟨ρ, hρ, hρsub⟩ := T.ball_subset_of_pos hallpos
  exact mem_interior.mpr ⟨Metric.ball (x + ε • v) ρ, hρsub, Metric.isOpen_ball,
    Metric.mem_ball_self hρ⟩
theorem Dissection.cross_disjoint_of_onEdge {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {x : Plane} {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x)
    (v : Plane) :
    ¬(0 < cross ((D.tile i₁).leftDir (m₁ + 1)) v
      ∧ 0 < cross ((D.tile i₂).leftDir (m₂ + 1)) v) := by
  rintro ⟨hv₁, hv₂⟩
  obtain ⟨ε₁, hε₁, h₁⟩ := (D.tile i₁).mem_interior_of_cross_pos hm₁ ho₁ hv₁
  obtain ⟨ε₂, hε₂, h₂⟩ := (D.tile i₂).mem_interior_of_cross_pos hm₂ ho₂ hv₂
  set ε := min ε₁ ε₂ / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact half_pos (lt_min hε₁ hε₂)
  have hlt₁ : ε < ε₁ := by
    rw [hεdef]; have := min_le_left ε₁ ε₂; linarith
  have hlt₂ : ε < ε₂ := by
    rw [hεdef]; have := min_le_right ε₁ ε₂; linarith
  exact Set.disjoint_left.mp (D.interiors_disjoint hne)
    (h₁ ε hεpos hlt₁) (h₂ ε hεpos hlt₂)
noncomputable def crossL (u : Plane) : Plane →ₗ[ℝ] ℝ where
  toFun := cross u
  map_add' := cross_add_right u
  map_smul' := fun t v => cross_smul_right t u v
@[simp] theorem crossL_apply (u v : Plane) : crossL u v = cross u v := rfl
theorem eq_zero_of_cross_eq_zero {u : Plane} (h : ∀ v, cross u v = 0) : u = 0 := by
  have h0 : u 0 = 0 := by
    have := h (EuclideanSpace.single 1 (1 : ℝ)); simpa [cross] using this
  have h1 : u 1 = 0 := by
    have := h (EuclideanSpace.single 0 (1 : ℝ))
    simp [cross] at this
    linarith
  ext i; fin_cases i
  · simpa using h0
  · simpa using h1
theorem crossL_ne_zero {u : Plane} (hu : u ≠ 0) : crossL u ≠ 0 := by
  intro h
  exact hu (eq_zero_of_cross_eq_zero fun v => by
    have := LinearMap.congr_fun h v; simpa using this)
theorem Dissection.leftDir_antiparallel {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {x : Plane} {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x) :
    ∃ c : ℝ, c < 0 ∧ (D.tile i₂).leftDir (m₂ + 1) = c • (D.tile i₁).leftDir (m₁ + 1) := by
  obtain ⟨c, hcneg, hc⟩ := proportional_of_disjoint_pos
    (crossL ((D.tile i₁).leftDir (m₁ + 1))) (crossL ((D.tile i₂).leftDir (m₂ + 1)))
    (crossL_ne_zero ((D.tile i₁).leftDir_ne_zero _))
    (crossL_ne_zero ((D.tile i₂).leftDir_ne_zero _))
    (fun v => by
      simpa using D.cross_disjoint_of_onEdge hne hm₁ ho₁ hm₂ ho₂ v)
  refine ⟨c, hcneg, ?_⟩
  have hzero : ∀ v, cross ((D.tile i₂).leftDir (m₂ + 1) - c • (D.tile i₁).leftDir (m₁ + 1)) v = 0 := by
    intro v
    have h1 : cross ((D.tile i₂).leftDir (m₂ + 1)) v = c * cross ((D.tile i₁).leftDir (m₁ + 1)) v := by
      simpa using hc v
    simp only [cross, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    simp only [cross] at h1
    linarith [h1]
  exact sub_eq_zero.mp (eq_zero_of_cross_eq_zero hzero)
theorem exists_second_of_card_two {α : Type*} {s : Finset α} (h : s.card = 2) (a : α) :
    ∃ b ∈ s, b ≠ a :=
  Finset.exists_mem_ne (by omega) a
theorem Dissection.second_tile_at_edge_point {N : ℕ} (D : Dissection N) (hN : 0 < N) {x : Plane}
    (hxv : ∀ i k, x ≠ (D.tile i).pts k)
    {R : ℝ} (hR : 0 < R) (hRt : Metric.ball x R ⊆ D.target.carrier)
    {i₀ : Fin N} (hi₀ : OnEdge D x i₀) :
    ∃ i₁, i₁ ≠ i₀ ∧ OnEdge D x i₁ := by
  classical
  have hmem : i₀ ∈ Finset.univ.filter (fun i => OnEdge D x i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩
  have hcard := (D.two_tiles_at_edge_point hN hxv hR hRt ⟨i₀, hmem⟩).1
  obtain ⟨i₁, hi₁mem, hne⟩ := exists_second_of_card_two hcard i₀
  exact ⟨i₁, hne, (Finset.mem_filter.mp hi₁mem).2⟩
theorem Tri.edge_subset_carrier (T : Tri) (k : Fin 3) : T.edge k ⊆ T.carrier := by
  refine (convex_convexHull ℝ _).segment_subset ?_ ?_ <;>
    exact subset_convexHull ℝ _ ⟨_, rfl⟩
theorem Tri.coord_eq_zero_of_mem_edge (T : Tri) (k : Fin 3) {x : Plane} (hx : x ∈ T.edge k) :
    T.basis.coord (k + 2) x = 0 := by
  have hne1 : (k + 2) ≠ k := by fin_cases k <;> decide
  have hne2 : (k + 2) ≠ (k + 1) := by fin_cases k <;> decide
  have hconv : Convex ℝ ((T.basis.coord (k + 2)) ⁻¹' {(0 : ℝ)}) :=
    (convex_singleton (0 : ℝ)).affine_preimage _
  have hb : ∀ i : Fin 3, T.pts i = (T.basis : Fin 3 → Plane) i := fun _ => rfl
  refine hconv.segment_subset ?_ ?_ hx
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, hb, AffineBasis.coord_apply]
    simp [hne1]
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, hb, AffineBasis.coord_apply]
    simp [hne2]
theorem Tri.mem_edge_of_coord_zero (T : Tri) {m : Fin 3} {x : Plane}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x) :
    x ∈ T.edge (m + 1) := by
  have hsum := T.basis.sum_coord_apply_eq_one x
  have hcomb := T.basis.linear_combination_coord_eq_self x
  have h1 : (m + 1) ≠ m := by fin_cases m <;> decide
  have h2 : (m + 2) ≠ m := by fin_cases m <;> decide
  refine ⟨T.basis.coord (m + 1) x, T.basis.coord (m + 1 + 1) x,
    (ho _ h1).le, ?_, ?_, ?_⟩
  · have : (m + 1 + 1) = m + 2 := by fin_cases m <;> rfl
    rw [this]; exact (ho _ h2).le
  · have hthree : ∀ c : Fin 3 → ℝ, ∑ i, c i = c m + c (m + 1) + c (m + 1 + 1) := by
      intro c; fin_cases m <;> simp [Fin.sum_univ_three] <;> ring
    rw [hthree] at hsum; rw [hm, zero_add] at hsum; exact hsum
  · have hthree : ∀ c : Fin 3 → Plane, ∑ i, c i = c m + c (m + 1) + c (m + 1 + 1) := by
      intro c; fin_cases m <;> simp [Fin.sum_univ_three] <;> abel
    rw [hthree] at hcomb
    have hb : ∀ i, T.basis i = T.pts i := fun _ => rfl
    simpa [hm, zero_smul, hb] using hcomb
def Dissection.vertexSet {N : ℕ} (D : Dissection N) : Set Plane :=
  ⋃ i : Fin N, ⋃ k : Fin 3, {(D.tile i).pts k}
theorem Dissection.vertexSet_finite {N : ℕ} (D : Dissection N) : D.vertexSet.Finite :=
  Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _
theorem Dissection.notMem_vertexSet {N : ℕ} (D : Dissection N) {x : Plane}
    (hx : x ∉ D.vertexSet) : ∀ i k, x ≠ (D.tile i).pts k := by
  intro i k h
  exact hx (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨k, by simp [h]⟩⟩)
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open MeasureTheory Set
theorem cross_sub_right (u a b : Plane) : cross u (a - b) = cross u a - cross u b := by
  simp only [cross, PiLp.sub_apply]; ring
theorem cross_smul_left (t : ℝ) (u v : Plane) : cross (t • u) v = t * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring
theorem cross_eq_zero_of_common_ker {n u v : Plane} (hn : n ≠ 0)
    (hu : cross n u = 0) (hv : cross n v = 0) : cross u v = 0 := by
  have hcomp : n 0 ≠ 0 ∨ n 1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hn (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  simp only [cross] at hu hv ⊢
  rcases hcomp with h | h
  · have key : n 0 * (u 0 * v 1 - u 1 * v 0) = 0 := by
      linear_combination u 0 * hv - v 0 * hu
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' h
    · exact h'
  · have key : n 1 * (u 0 * v 1 - u 1 * v 0) = 0 := by
      linear_combination u 1 * hv - v 1 * hu
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' h
    · exact h'
theorem parallel_of_cross_eq_zero {a b : Plane} (ha : a ≠ 0) (h : cross a b = 0) :
    ∃ τ : ℝ, b = τ • a := by
  have hcomp : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact ha (by ext i; fin_cases i <;> simp [hc.1, hc.2])
  simp only [cross] at h
  rcases hcomp with h0 | h1
  · refine ⟨b 0 / a 0, ?_⟩
    have key0 : b 0 = b 0 / a 0 * a 0 := by field_simp
    have key1 : b 1 = b 0 / a 0 * a 1 := by field_simp; linear_combination h
    ext i
    fin_cases i
    · simpa [smul_eq_mul] using key0
    · simpa [smul_eq_mul] using key1
  · refine ⟨b 1 / a 1, ?_⟩
    have key0 : b 0 = b 1 / a 1 * a 0 := by field_simp; linear_combination -h
    have key1 : b 1 = b 1 / a 1 * a 1 := by field_simp
    ext i
    fin_cases i
    · simpa [smul_eq_mul] using key0
    · simpa [smul_eq_mul] using key1
theorem plane_decomp (y : Plane) :
    y = EuclideanSpace.single (0 : Fin 2) (y 0) + EuclideanSpace.single (1 : Fin 2) (y 1) := by
  ext i
  fin_cases i <;> simp
theorem single_eq_smul (i : Fin 2) (a : ℝ) :
    EuclideanSpace.single i a = a • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i <;> simp [h]
noncomputable def rotVec (f : Plane →ₗ[ℝ] ℝ) : Plane :=
  EuclideanSpace.single (0 : Fin 2) (f (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)))
    + EuclideanSpace.single (1 : Fin 2) (-(f (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))))
theorem rotVec_spec (f : Plane →ₗ[ℝ] ℝ) (y : Plane) : f y = cross (rotVec f) y := by
  have h0 : EuclideanSpace.single (0 : Fin 2) (y 0)
      = y 0 • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := single_eq_smul 0 (y 0)
  have h1 : EuclideanSpace.single (1 : Fin 2) (y 1)
      = y 1 • EuclideanSpace.single (1 : Fin 2) (1 : ℝ) := single_eq_smul 1 (y 1)
  have hf : f y = y 0 * f (EuclideanSpace.single (0 : Fin 2) (1 : ℝ))
      + y 1 * f (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
    conv_lhs => rw [plane_decomp y, h0, h1]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hcross : cross (rotVec f) y
      = f (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) * y 1
        + f (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) * y 0 := by
    simp only [cross, rotVec, PiLp.add_apply]
    simp
  rw [hf, hcross]; ring
theorem rotVec_ne_zero {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) : rotVec f ≠ 0 := by
  intro h
  apply hf
  apply LinearMap.ext
  intro y
  rw [rotVec_spec f y, h]
  simp [cross]
theorem move_in_ball {x v : Plane} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) :
    x + (r / (2 * ‖v‖)) • v ∈ Metric.ball x r ∧ 0 < r / (2 * ‖v‖) := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have htpos : 0 < r / (2 * ‖v‖) := by positivity
  refine ⟨?_, htpos⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hxy : x + (r / (2 * ‖v‖)) • v - x = (r / (2 * ‖v‖)) • v := by abel
  rw [hxy, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
  have hval : r / (2 * ‖v‖) * ‖v‖ = r / 2 := by field_simp
  rw [hval]; linarith
theorem Tri.interior_coord_pos (T : Tri) {y : Plane} (hy : y ∈ interior T.carrier) :
    ∀ j, 0 < T.basis.coord j y := by
  intro j
  have hnn : 0 ≤ T.basis.coord j y := by
    have hmem := interior_subset hy
    rw [T.carrier_eq_nonneg_coord] at hmem
    exact hmem j
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
    obtain ⟨w, hw⟩ : ∃ w, (T.basis.coord j).linear w ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact T.coord_linear_ne_zero j (LinearMap.ext fun w => by simpa using hc w)
    obtain ⟨v, hv⟩ : ∃ v, (T.basis.coord j).linear v < 0 := by
      rcases lt_or_gt_of_ne hw with h' | h'
      · exact ⟨w, h'⟩
      · exact ⟨-w, by rw [map_neg]; linarith⟩
    have hvne : v ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact absurd hv (lt_irrefl 0)
    obtain ⟨hmem, htpos⟩ := move_in_ball (x := y) hvne hr
    have hin : y + (r / (2 * ‖v‖)) • v ∈ T.carrier := interior_subset (hball hmem)
    rw [T.carrier_eq_nonneg_coord] at hin
    have hcoord : T.basis.coord j (y + (r / (2 * ‖v‖)) • v)
        = (T.basis.coord j).linear ((r / (2 * ‖v‖)) • v) + T.basis.coord j y := by
      have h1 := (T.basis.coord j).map_vadd y ((r / (2 * ‖v‖)) • v)
      simp only [vadd_eq_add] at h1
      rw [add_comm ((r / (2 * ‖v‖)) • v) y] at h1
      exact h1
    have hneg : T.basis.coord j (y + (r / (2 * ‖v‖)) • v) < 0 := by
      rw [hcoord, map_smul, smul_eq_mul, h.symm, add_zero]
      exact mul_neg_of_pos_of_neg htpos hv
    exact absurd (hin j) (not_le.mpr hneg)
theorem Tri.interior_lt_of_le (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ y ∈ T.carrier, f y ≤ c) {y : Plane} (hy : y ∈ interior T.carrier) : f y < c := by
  rcases (hle y (interior_subset hy)).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior y hy
    obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hf (LinearMap.ext fun z => by simpa using hc z)
    obtain ⟨v, hv⟩ : ∃ v, 0 < f v := by
      rcases lt_or_gt_of_ne hw with h' | h'
      · exact ⟨-w, by rw [map_neg]; linarith⟩
      · exact ⟨w, h'⟩
    have hvne : v ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact absurd hv (lt_irrefl 0)
    obtain ⟨hmem, htpos⟩ := move_in_ball (x := y) hvne hr
    have hin : f (y + (r / (2 * ‖v‖)) • v) ≤ c := hle _ (interior_subset (hball hmem))
    rw [map_add, map_smul, smul_eq_mul, h] at hin
    nlinarith [mul_pos htpos hv]
theorem Tri.onEdge_param (T : Tri) {k : Fin 3} {x : Plane} (hx : x ∈ T.edge k)
    (h1 : x ≠ T.pts k) (h2 : x ≠ T.pts (k + 1)) :
    T.basis.coord (k + 2) x = 0 ∧ ∀ j, j ≠ k + 2 → 0 < T.basis.coord j x := by
  have hz := T.coord_eq_zero_of_mem_edge k hx
  rw [Tri.edge] at hx
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hx
  have hca : T.basis.coord k x = a := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord k (T.pts k) = 1 := T.basis.coord_apply_eq k
    have e2 : T.basis.coord k (T.pts (k + 1)) = 0 :=
      T.basis.coord_apply_ne (by fin_cases k <;> decide)
    rw [e1, e2]; ring
  have hcb : T.basis.coord (k + 1) x = b := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord (k + 1) (T.pts k) = 0 :=
      T.basis.coord_apply_ne (by fin_cases k <;> decide)
    have e2 : T.basis.coord (k + 1) (T.pts (k + 1)) = 1 := T.basis.coord_apply_eq (k + 1)
    rw [e1, e2]; ring
  have hapos : 0 < a := by
    rcases ha.lt_or_eq with h | h
    · exact h
    · exfalso
      apply h2
      have hb1 : b = 1 := by linarith
      rw [← hcomb, ← h, hb1]
      simp
  have hbpos : 0 < b := by
    rcases hb.lt_or_eq with h | h
    · exact h
    · exfalso
      apply h1
      have ha1 : a = 1 := by linarith
      rw [← hcomb, ← h, ha1]
      simp
  refine ⟨hz, fun j hj => ?_⟩
  have hcases : j = k ∨ j = k + 1 := by
    have hall : ∀ j k : Fin 3, j ≠ k + 2 → j = k ∨ j = k + 1 := by decide
    exact hall j k hj
  rcases hcases with rfl | rfl
  · rw [hca]; exact hapos
  · rw [hcb]; exact hbpos
theorem mem_ne_ends_of_avg {A B p q : Plane} (hpq : p ≠ q)
    (hp : p ∈ segment ℝ A B) (hq : q ∈ segment ℝ A B) :
    ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ∈ segment ℝ A B
      ∧ ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ≠ A ∧ ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ≠ B := by
  have hmem : ((1:ℝ)/2) • p + ((1:ℝ)/2) • q ∈ segment ℝ A B :=
    (convex_segment A B) hp hq (by norm_num) (by norm_num) (by norm_num)
  have hAB : A ≠ B := by
    rintro rfl
    rw [segment_same] at hp hq
    rw [Set.mem_singleton_iff] at hp hq
    exact hpq (hp.trans hq.symm)
  rw [segment_eq_image' ℝ A B] at hp hq
  obtain ⟨s, hs, rfl⟩ := hp
  obtain ⟨t, ht, rfl⟩ := hq
  have hmid : ((1:ℝ)/2) • (A + s • (B - A)) + ((1:ℝ)/2) • (A + t • (B - A))
      = A + ((s + t)/2) • (B - A) := by module
  refine ⟨hmem, ?_, ?_⟩
  · intro hcon
    rw [hmid] at hcon
    have hkey : ((s + t)/2) • (B - A) = 0 := by
      have h1 := congrArg (fun y => y - A) hcon
      simpa using h1
    rcases smul_eq_zero.mp hkey with h | h
    · have hs0 : s = 0 := by
        have := hs.1; have := ht.1
        have h2 : s + t = 0 := by linarith
        linarith
      have ht0 : t = 0 := by
        have := hs.1
        have h2 : s + t = 0 := by linarith
        linarith
      exact hpq (by rw [hs0, ht0])
    · exact hAB (sub_eq_zero.mp h).symm
  · intro hcon
    rw [hmid] at hcon
    have hB : A + (1:ℝ) • (B - A) = B := by module
    rw [← hB] at hcon
    have h2 : ((s + t)/2) • (B - A) = (1:ℝ) • (B - A) := by
      have h1 := congrArg (fun y => y - A) hcon
      simpa using h1
    have h3 : ((s + t)/2 - 1) • (B - A) = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · have hs1 : s = 1 := by
        have := hs.2; have := ht.2
        have h4 : s + t = 2 := by linarith
        linarith
      have ht1 : t = 1 := by
        have := hs.2
        have h4 : s + t = 2 := by linarith
        linarith
      exact hpq (by rw [hs1, ht1])
    · exact hAB (sub_eq_zero.mp h).symm
theorem Tri.edge_endpoints_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    (hfx : f x = c) (hle1 : f (T.pts (m + 1)) ≤ c) (hle2 : f (T.pts (m + 2)) ≤ c) :
    f (T.pts (m + 1)) = c ∧ f (T.pts (m + 2)) = c := by
  have hxe := T.mem_edge_of_coord_zero hm ho
  have hidx : (m + 1) + 1 = m + 2 := by fin_cases m <;> rfl
  rw [Tri.edge, hidx] at hxe
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hxe
  have hfxc : a * f (T.pts (m + 1)) + b * f (T.pts (m + 2)) = c := by
    rw [← hfx, ← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hca : T.basis.coord (m + 1) x = a := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord (m + 1) (T.pts (m + 1)) = 1 := T.basis.coord_apply_eq (m + 1)
    have e2 : T.basis.coord (m + 1) (T.pts (m + 2)) = 0 :=
      T.basis.coord_apply_ne (by fin_cases m <;> decide)
    rw [e1, e2]; ring
  have hcb : T.basis.coord (m + 2) x = b := by
    rw [← hcomb, Convex.combo_affine_apply hab, smul_eq_mul, smul_eq_mul]
    have e1 : T.basis.coord (m + 2) (T.pts (m + 1)) = 0 :=
      T.basis.coord_apply_ne (by fin_cases m <;> decide)
    have e2 : T.basis.coord (m + 2) (T.pts (m + 2)) = 1 := T.basis.coord_apply_eq (m + 2)
    rw [e1, e2]; ring
  have hapos : 0 < a := by
    rw [← hca]; exact ho _ (by fin_cases m <;> decide)
  have hbpos : 0 < b := by
    rw [← hcb]; exact ho _ (by fin_cases m <;> decide)
  have habc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  constructor
  · by_contra hne
    have hlt : f (T.pts (m + 1)) < c := lt_of_le_of_ne hle1 hne
    have h1 : a * f (T.pts (m + 1)) < a * c := mul_lt_mul_of_pos_left hlt hapos
    have h2 : b * f (T.pts (m + 2)) ≤ b * c := mul_le_mul_of_nonneg_left hle2 hb
    linarith
  · by_contra hne
    have hlt : f (T.pts (m + 2)) < c := lt_of_le_of_ne hle2 hne
    have h1 : a * f (T.pts (m + 1)) ≤ a * c := mul_le_mul_of_nonneg_left hle1 ha
    have h2 : b * f (T.pts (m + 2)) < b * c := mul_lt_mul_of_pos_left hlt hbpos
    linarith
theorem Tri.edge_inward (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle : ∀ y ∈ T.carrier, f y ≤ c) {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    (hfx : f x = c) {v : Plane} (hv : f v < 0) :
    0 < cross (T.leftDir (m + 1)) v := by
  have hmem : ∀ i, T.pts i ∈ T.carrier := fun i => subset_convexHull ℝ _ ⟨i, rfl⟩
  obtain ⟨hP, hQ⟩ := T.edge_endpoints_on_line f c hm ho hfx
    (hle _ (hmem _)) (hle _ (hmem _))
  have hidx : (m + 1) + 1 = m + 2 := by fin_cases m <;> rfl
  have hfdir : f (T.leftDir (m + 1)) = 0 := by
    rcases T.leftDir_eq_or (m + 1) with h | h
    · rw [h, hidx, map_sub, hP, hQ, sub_self]
    · rw [h, hidx, map_neg, map_sub, hP, hQ, sub_self, neg_zero]
  have hker : ∀ w, f w = 0 → crossL (T.leftDir (m + 1)) w = 0 := by
    intro w hw
    have hn := rotVec_ne_zero hf
    have h1 : cross (rotVec f) (T.leftDir (m + 1)) = 0 := by
      rw [← rotVec_spec]; exact hfdir
    have h2 : cross (rotVec f) w = 0 := by rw [← rotVec_spec]; exact hw
    rw [crossL_apply]
    exact cross_eq_zero_of_common_ker hn h1 h2
  obtain ⟨c₀, hc₀⟩ := proportional_of_ker_le f (crossL (T.leftDir (m + 1))) hf hker
  obtain ⟨y₀, hy₀⟩ := T.interior_nonempty
  have hy₀pos := T.interior_coord_pos hy₀
  have hcpos : 0 < cross (T.leftDir (m + 1)) (y₀ - T.pts (m + 1)) :=
    T.interior_left_of_leftDir (m + 1) hy₀pos
  have hylt : f y₀ < c := T.interior_lt_of_le f c hf hle hy₀
  have hval : cross (T.leftDir (m + 1)) (y₀ - T.pts (m + 1)) = c₀ * (f y₀ - c) := by
    have h1 := hc₀ (y₀ - T.pts (m + 1))
    rw [crossL_apply] at h1
    rw [h1, map_sub, hP]
  have hc₀neg : c₀ < 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 : 0 < c₀ * (f y₀ - c) := hval ▸ hcpos
    nlinarith
  have h2 := hc₀ v
  rw [crossL_apply] at h2
  rw [h2]
  exact mul_pos_of_neg_of_neg hc₀neg hv
theorem Dissection.no_second_tile_same_side {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hle₁ : ∀ y ∈ (D.tile i₁).carrier, f y ≤ c) (hle₂ : ∀ y ∈ (D.tile i₂).carrier, f y ≤ c)
    {x : Plane} (hfx : f x = c) {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x) : False := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hf (LinearMap.ext fun z => by simpa using hc z)
  obtain ⟨v, hv⟩ : ∃ v, f v < 0 := by
    rcases lt_or_gt_of_ne hw with h' | h'
    · exact ⟨w, h'⟩
    · exact ⟨-w, by rw [map_neg]; linarith⟩
  exact D.cross_disjoint_of_onEdge hne hm₁ ho₁ hm₂ ho₂ v
    ⟨(D.tile i₁).edge_inward f c hf hle₁ hm₁ ho₁ hfx hv,
     (D.tile i₂).edge_inward f c hf hle₂ hm₂ ho₂ hfx hv⟩
theorem Dissection.two_edge_data_clash {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {j₁ j₂ : Fin N} {k₁ k₂ : Fin 3}
    (hne : (j₁, k₁) ≠ (j₂, k₂))
    (hle₁ : ∀ y ∈ (D.tile j₁).carrier, f y ≤ c) (hle₂ : ∀ y ∈ (D.tile j₂).carrier, f y ≤ c)
    {x : Plane} (hfx : f x = c)
    (hz₁ : (D.tile j₁).basis.coord (k₁ + 2) x = 0)
    (hp₁ : ∀ j, j ≠ k₁ + 2 → 0 < (D.tile j₁).basis.coord j x)
    (hz₂ : (D.tile j₂).basis.coord (k₂ + 2) x = 0)
    (hp₂ : ∀ j, j ≠ k₂ + 2 → 0 < (D.tile j₂).basis.coord j x) : False := by
  by_cases hsame : j₁ = j₂
  · subst hsame
    have hk : k₁ ≠ k₂ := fun h => hne (by rw [h])
    have hk2 : k₁ + 2 ≠ k₂ + 2 := fun h => hk (add_right_cancel h)
    exact absurd hz₁ (ne_of_gt (hp₂ _ hk2))
  · exact D.no_second_tile_same_side hsame f c hf hle₁ hle₂ hfx hz₁ hp₁ hz₂ hp₂
theorem Dissection.sameside_edges_subsingleton {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    {e₁ e₂ : Fin N × Fin 3} (hne : e₁ ≠ e₂)
    (hle₁ : ∀ y ∈ (D.tile e₁.1).carrier, f y ≤ c)
    (hle₂ : ∀ y ∈ (D.tile e₂.1).carrier, f y ≤ c)
    (hE₁ : ∀ y ∈ (D.tile e₁.1).edge e₁.2, f y = c)
    (hE₂ : ∀ y ∈ (D.tile e₂.1).edge e₂.2, f y = c) :
    ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨hm1, hn1A, hn1B⟩ := mem_ne_ends_of_avg hpq hp.1 hq.1
  obtain ⟨hm2, hn2A, hn2B⟩ := mem_ne_ends_of_avg hpq hp.2 hq.2
  obtain ⟨hz₁, hp₁⟩ := (D.tile e₁.1).onEdge_param hm1 hn1A hn1B
  obtain ⟨hz₂, hp₂⟩ := (D.tile e₂.1).onEdge_param hm2 hn2A hn2B
  have hne' : (e₁.1, e₁.2) ≠ (e₂.1, e₂.2) := by simpa using hne
  exact D.two_edge_data_clash f c hf hne' hle₁ hle₂ (hE₁ _ hm1) hz₁ hp₁ hz₂ hp₂
theorem sum_hausdorff_of_partition {ι : Type*} (part : Finset ι)
    (E : ι → Set Plane) (S : Set Plane) (F : Set Plane) (hF : F.Finite)
    (hmeas : ∀ e ∈ part, MeasurableSet (E e))
    (hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ → (E e₁ ∩ E e₂).Subsingleton)
    (hsub : ∀ e ∈ part, E e ⊆ S)
    (hcov : S \ F ⊆ ⋃ e ∈ part, E e) :
    ∑ e ∈ part, (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) (E e)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) S := by
  classical
  haveI : MeasureTheory.NullSingletonClass
      (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) :=
    MeasureTheory.Measure.nullSingletonClass_hausdorff Plane (by norm_num)
  set μ := (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) with hμ
  have hadd := MeasureTheory.measure_biUnion_finset₀ (μ := μ) (s := part) (f := E)
    (fun e₁ h₁ e₂ h₂ hne => ((hdisj e₁ h₁ e₂ h₂ hne).finite.measure_zero μ))
    (fun e he => (hmeas e he).nullMeasurableSet)
  have hle1 : μ (⋃ e ∈ part, E e) ≤ μ S := measure_mono (Set.iUnion₂_subset hsub)
  have hFnull : μ F = 0 := hF.measure_zero μ
  have hle2 : μ S ≤ μ (⋃ e ∈ part, E e) := by
    calc μ S ≤ μ ((⋃ e ∈ part, E e) ∪ F) := by
          refine measure_mono fun x hx => ?_
          by_cases hxF : x ∈ F
          · exact Or.inr hxF
          · exact Or.inl (hcov ⟨hx, hxF⟩)
      _ ≤ μ (⋃ e ∈ part, E e) + μ F := measure_union_le _ _
      _ = μ (⋃ e ∈ part, E e) := by rw [hFnull, add_zero]
  rw [← hadd]
  exact le_antisymm hle1 hle2
theorem Dissection.side_partition {N : ℕ} (D : Dissection N) (i : Fin 3) :
    ∃ part : Finset (Fin N × Fin 3),
      ((⋃ e ∈ part, (D.tile e.1).edge e.2)
          = segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
      ∧ (∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
          ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
      ∧ ∑ e ∈ part, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
          = edist (D.target.pts i) (D.target.pts (i + 1)) := by
  classical
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  obtain ⟨part, hpart⟩ := hasEdgeChains_edge D i
  have hS : {x ∈ D.target.carrier | f x = c}
      = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) :=
    target_contact_side D.target f c hle hi hi1 hi2
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2
      ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
    intro e he y hy
    rw [← hpart]
    exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  have hlineE : ∀ e ∈ part, ∀ y ∈ (D.tile e.1).edge e.2, f y = c := by
    intro e he y hy
    have h1 : y ∈ {x ∈ D.target.carrier | f x = c} := by
      rw [hS]; exact hsub e he hy
    exact h1.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, f y ≤ c :=
    fun e y hy => hle y (tile_subset_target D e.1 hy)
  have hdisj : ∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
      ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton :=
    fun e₁ h₁ e₂ h₂ hne => D.sameside_edges_subsingleton f c hf hne
      (hleT e₁) (hleT e₂) (hlineE e₁ h₁) (hlineE e₂ h₂)
  refine ⟨part, hpart, hdisj, ?_⟩
  have hsum := sum_hausdorff_of_partition part (fun e => (D.tile e.1).edge e.2)
    (segment ℝ (D.target.pts i) (D.target.pts (i + 1))) ∅ Set.finite_empty
    (fun e _ => ((D.tile e.1).isClosed_edge e.2).measurableSet)
    hdisj hsub
    (by
      intro x hx
      rw [← hpart] at hx
      exact hx.1)
  calc ∑ e ∈ part, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = ∑ e ∈ part,
          (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
            ((D.tile e.1).edge e.2) := by
        refine Finset.sum_congr rfl fun e _ => ?_
        exact ((D.tile e.1).hausdorff_edge e.2).symm
    _ = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
          (segment ℝ (D.target.pts i) (D.target.pts (i + 1))) := hsum
    _ = edist (D.target.pts i) (D.target.pts (i + 1)) :=
        MeasureTheory.hausdorffMeasure_segment _ _
theorem Dissection.side_walk {N : ℕ} (D : Dissection N) (i : Fin 3) :
    ∃ part : Finset (Fin N × Fin 3),
      ((⋃ e ∈ part, (D.tile e.1).edge e.2)
          = segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
      ∧ (∀ e₁ ∈ part, ∀ e₂ ∈ part, e₁ ≠ e₂ →
          ((D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2).Subsingleton)
      ∧ ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
          = dist (D.target.pts i) (D.target.pts (i + 1)) := by
  obtain ⟨part, hcov, hdisj, hsum⟩ := D.side_partition i
  refine ⟨part, hcov, hdisj, ?_⟩
  have h1 : ENNReal.ofReal
        (∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      = ENNReal.ofReal (dist (D.target.pts i) (D.target.pts (i + 1))) := by
    calc ENNReal.ofReal
          (∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
        = ∑ e ∈ part,
            ENNReal.ofReal (dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) :=
          ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg)
      _ = ∑ e ∈ part, edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) :=
          Finset.sum_congr rfl fun e _ => (edist_dist _ _).symm
      _ = edist (D.target.pts i) (D.target.pts (i + 1)) := hsum
      _ = ENNReal.ofReal (dist (D.target.pts i) (D.target.pts (i + 1))) := edist_dist _ _
  exact (ENNReal.ofReal_eq_ofReal_iff
    (Finset.sum_nonneg fun e _ => dist_nonneg) dist_nonneg).mp h1
end Erdos634.Geometry
end

section
open MeasureTheory Set
namespace Erdos634.SectorArea
def polarBox (θ : ℝ) : Set (ℝ × ℝ) := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) θ
def sector (θ : ℝ) : Set (ℝ × ℝ) := polarCoord.symm '' polarBox θ
theorem polarBox_subset_target {θ : ℝ} (hθ' : θ < Real.pi) :
    polarBox θ ⊆ polarCoord.target := by
  rintro ⟨r, φ⟩ ⟨⟨hr0, hr1⟩, hφ0, hφθ⟩
  exact ⟨hr0, by linarith [Real.pi_pos], by linarith⟩
theorem lintegral_id_Ioo : ∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal r = ENNReal.ofReal (1/2) := by
  have hmeas : MeasurableSet (Ioo (0:ℝ) 1) := measurableSet_Ioo
  have hint : IntegrableOn (fun r : ℝ => r) (Ioo (0:ℝ) 1) :=
    (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0:ℝ) 1)] fun r : ℝ => r := by
    filter_upwards [ae_restrict_mem hmeas] with r hr using le_of_lt hr.1
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_id]
  norm_num
theorem lintegral_jacobian {θ : ℝ} (hθ : 0 ≤ θ) :
    ∫⁻ p in polarBox θ, ENNReal.ofReal p.1 = ENNReal.ofReal (θ / 2) := by
  have hprod : (volume : Measure (ℝ × ℝ)).restrict (polarBox θ)
      = ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioo (0:ℝ) θ))) := by
    rw [Measure.prod_restrict, polarBox, ← Measure.volume_eq_prod]
  rw [hprod, MeasureTheory.lintegral_prod _ (by fun_prop)]
  have hinner : ∀ r : ℝ, ∫⁻ _ in Ioo (0:ℝ) θ, ENNReal.ofReal r
      = ENNReal.ofReal r * ENNReal.ofReal θ := by
    intro r
    rw [MeasureTheory.setLIntegral_const, Real.volume_Ioo]
    congr 1
    rw [ENNReal.ofReal_eq_ofReal_iff (by linarith) hθ]
    ring
  simp_rw [hinner]
  rw [MeasureTheory.lintegral_mul_const _ (by fun_prop), lintegral_id_Ioo,
      ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring
theorem volume_sector {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < Real.pi) :
    volume (sector θ) = ENNReal.ofReal (θ / 2) := by
  have hsub := polarBox_subset_target hθ'
  have hboxOpen : IsOpen (polarBox θ) := isOpen_Ioo.prod isOpen_Ioo
  have hbox : MeasurableSet (polarBox θ) := hboxOpen.measurableSet
  have hsec : MeasurableSet (sector θ) :=
    (OpenPartialHomeomorph.isOpen_image_symm_of_subset_target polarCoord hboxOpen hsub).measurableSet
  have key := lintegral_comp_polarCoord_symm ((sector θ).indicator (fun _ => (1 : ENNReal)))
  rw [lintegral_indicator hsec, setLIntegral_one] at key
  have hpt : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 • (sector θ).indicator (fun _ => (1 : ENNReal)) (polarCoord.symm p)
        = (polarBox θ).indicator (fun q => ENNReal.ofReal q.1) p := by
    intro p hp
    by_cases hpb : p ∈ polarBox θ
    · have hmem : polarCoord.symm p ∈ sector θ := mem_image_of_mem _ hpb
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpb, smul_eq_mul, mul_one]
    · have hnot : polarCoord.symm p ∉ sector θ := by
        rintro ⟨q, hq, hqp⟩
        exact hpb (polarCoord.symm.injOn (hsub hq) hp hqp ▸ hq)
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hpb, smul_zero]
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet hpt,
    setLIntegral_indicator hbox, Set.inter_eq_self_of_subset_left hsub,
    lintegral_jacobian hθ] at key
  exact key.symm
end Erdos634.SectorArea
end

section
open Set Real
namespace Erdos634.Wedge
def polarBox (θ : ℝ) : Set (ℝ × ℝ) := Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) θ
def sector (θ : ℝ) : Set (ℝ × ℝ) := polarCoord.symm '' polarBox θ
theorem symm_apply (r φ : ℝ) : polarCoord.symm (r, φ) = (r * Real.cos φ, r * Real.sin φ) := rfl
theorem sector_subset_halfplanes {θ : ℝ} (hπ : θ < Real.pi) :
    sector θ ⊆ {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
             ∩ {p : ℝ × ℝ | 0 < p.2}
             ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} := by
  rintro _ ⟨⟨r, φ⟩, ⟨hr, hφ⟩, rfl⟩
  obtain ⟨hr0, hr1⟩ := hr
  obtain ⟨hφ0, hφθ⟩ := hφ
  have hφπ : φ < Real.pi := lt_trans hφθ hπ
  have hsinφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ0 hφπ
  rw [symm_apply]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · 
    have : (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ
      nlinarith [this]
    rw [this]
    nlinarith
  · 
    exact mul_pos hr0 hsinφ
  · 
    have hexp : Real.sin θ * (r * Real.cos φ) - Real.cos θ * (r * Real.sin φ)
        = r * Real.sin (θ - φ) := by
      rw [Real.sin_sub]; ring
    rw [hexp]
    have : 0 < Real.sin (θ - φ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    exact mul_pos hr0 this
theorem pos_of_sin_pos {x : ℝ} (hlo : -Real.pi < x) (hs : 0 < Real.sin x) : 0 < x := by
  by_contra h
  simp only [not_lt] at h
  have : Real.sin x ≤ 0 := by
    rcases eq_or_lt_of_le h with rfl | hneg
    · simp
    · have h1 : 0 < -x := by linarith
      have h2 : -x < Real.pi := by linarith
      have := Real.sin_pos_of_pos_of_lt_pi h1 h2
      rw [Real.sin_neg] at this; linarith
  linarith
theorem halfplanes_subset_sector {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
      ∩ {p : ℝ × ℝ | 0 < p.2}
      ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} ⊆ sector θ := by
  rintro p ⟨⟨hball, hy⟩, hwedge⟩
  simp only [Set.mem_setOf_eq] at hball hy hwedge
  have hsrc : p ∈ polarCoord.source := Or.inr (by simpa using ne_of_gt hy)
  set q := polarCoord p with hq
  have hinv : polarCoord.symm q = p := polarCoord.left_inv hsrc
  have hqt : q ∈ polarCoord.target := polarCoord.map_source hsrc
  obtain ⟨hr, hφ⟩ := hqt
  simp only [Set.mem_Ioi] at hr
  simp only [Set.mem_Ioo] at hφ
  have hp1 : p.1 = q.1 * Real.cos q.2 := by rw [← hinv]; rfl
  have hp2 : p.2 = q.1 * Real.sin q.2 := by rw [← hinv]; rfl
  have hsinφ : 0 < Real.sin q.2 := by
    by_contra h
    simp only [not_lt] at h
    rw [hp2] at hy
    nlinarith
  have hφpos : 0 < q.2 := pos_of_sin_pos hφ.1 hsinφ
  have hkey : Real.sin θ * p.1 - Real.cos θ * p.2 = q.1 * Real.sin (θ - q.2) := by
    rw [hp1, hp2, Real.sin_sub]; ring
  have hsinsub : 0 < Real.sin (θ - q.2) := by
    by_contra h
    simp only [not_lt] at h
    rw [hkey] at hwedge
    nlinarith
  have hφθ : q.2 < θ := by
    have := pos_of_sin_pos (by linarith [hφ.2]) hsinsub
    linarith
  have hrad : q.1 < 1 := by
    have hsq : q.1 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
      rw [hp1, hp2]; nlinarith [Real.sin_sq_add_cos_sq q.2]
    nlinarith
  exact ⟨q, ⟨⟨hr, hrad⟩, ⟨hφpos, hφθ⟩⟩, hinv⟩
theorem sector_eq_halfplanes {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    sector θ = {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
             ∩ {p : ℝ × ℝ | 0 < p.2}
             ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2} :=
  Set.Subset.antisymm (sector_subset_halfplanes hπ) (halfplanes_subset_sector h0 hπ)
end Erdos634.Wedge
end

section
open MeasureTheory Set
namespace Erdos634.E2Join
theorem sector_agree (θ : ℝ) : Wedge.sector θ = SectorArea.sector θ := rfl
theorem volume_halfplane_wedge {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    volume ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
          ∩ {p : ℝ × ℝ | 0 < p.2}
          ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2})
      = ENNReal.ofReal (θ / 2) := by
  rw [← Wedge.sector_eq_halfplanes h0 hπ, sector_agree]
  exact SectorArea.volume_sector (le_of_lt h0) hπ
def toPair (p : EuclideanSpace ℝ (Fin 2)) : ℝ × ℝ :=
  MeasurableEquiv.finTwoArrow (WithLp.ofLp p)
theorem measurePreserving_toPair : MeasurePreserving toPair :=
  (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))
def wedge (θ : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  toPair ⁻¹' ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
            ∩ {p : ℝ × ℝ | 0 < p.2}
            ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2})
theorem volume_wedge {θ : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi) :
    volume (wedge θ) = ENNReal.ofReal (θ / 2) := by
  have hopen : IsOpen ({p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < 1}
      ∩ {p : ℝ × ℝ | 0 < p.2} ∩ {p : ℝ × ℝ | 0 < Real.sin θ * p.1 - Real.cos θ * p.2}) := by
    refine IsOpen.inter (IsOpen.inter ?_ ?_) ?_
    · exact isOpen_lt (by fun_prop) continuous_const
    · exact isOpen_lt continuous_const (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  rw [wedge, measurePreserving_toPair.measure_preimage hopen.measurableSet.nullMeasurableSet]
  exact volume_halfplane_wedge h0 hπ
end Erdos634.E2Join
end

section
namespace Erdos634.Geometry
open MeasureTheory Set Metric InnerProductGeometry
open scoped RealInnerProductSpace Pointwise
theorem inner_coords (x y : Plane) : ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Fin.sum_univ_two]
  ring
theorem norm_sq_coords (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coords]
  ring
theorem cross_swap (u v : Plane) : cross u v = - cross v u := by
  simp only [cross]; ring
theorem mem_ball_sq (y : Plane) : y ∈ Metric.ball (0 : Plane) 1 ↔ y 0 ^ 2 + y 1 ^ 2 < 1 := by
  rw [Metric.mem_ball, dist_zero_right, ← norm_sq_coords]
  constructor
  · intro h
    nlinarith [norm_nonneg y]
  · intro h
    nlinarith [norm_nonneg y]
noncomputable def rot90 (u : Plane) : Plane :=
  EuclideanSpace.single 0 (-(u 1)) + EuclideanSpace.single 1 (u 0)
@[simp] theorem rot90_apply0 (u : Plane) : rot90 u 0 = -(u 1) := by
  simp [rot90]
@[simp] theorem rot90_apply1 (u : Plane) : rot90 u 1 = u 0 := by
  simp [rot90]
noncomputable def frame (u n : Plane) : Plane →ₗ[ℝ] Plane where
  toFun q := q 0 • u + q 1 • n
  map_add' a b := by
    show ((a + b) 0) • u + ((a + b) 1) • n = (a 0 • u + a 1 • n) + (b 0 • u + b 1 • n)
    simp only [PiLp.add_apply]
    module
  map_smul' c a := by
    show ((c • a) 0) • u + ((c • a) 1) • n = c • (a 0 • u + a 1 • n)
    simp only [PiLp.smul_apply, smul_eq_mul]
    module
theorem frame_apply (u n q : Plane) (i : Fin 2) :
    frame u n q i = q 0 * u i + q 1 * n i := by
  show (q 0 • u + q 1 • n) i = _
  simp [PiLp.add_apply, PiLp.smul_apply]
theorem frame_det (u n : Plane) : LinearMap.det (frame u n) = u 0 * n 1 - n 0 * u 1 := by
  classical
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (frame u n),
    Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, frame_apply, PiLp.single_apply]
  norm_num
theorem inner_sq_add_cross_sq (u v : Plane) :
    ⟪u, v⟫ ^ 2 + cross u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [inner_coords, norm_sq_coords, norm_sq_coords]
  simp only [cross]
  ring
theorem cos_angle_eq_inner (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Real.cos (angle u v) = ⟪u, v⟫ := by
  rw [cos_angle, hu, hv]
  norm_num
theorem sin_angle_eq_cross (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) : Real.sin (angle u v) = cross u v := by
  have h := sin_angle_mul_norm_mul_norm u v
  rw [hu, hv] at h
  have hlag : ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ * ⟪u, v⟫ = cross u v ^ 2 := by
    have hl := inner_sq_add_cross_sq u v
    rw [hu, hv] at hl
    have huu : ⟪u, u⟫ = (1:ℝ) := by
      rw [real_inner_self_eq_norm_sq, hu]; norm_num
    have hvv : ⟪v, v⟫ = (1:ℝ) := by
      rw [real_inner_self_eq_norm_sq, hv]; norm_num
    rw [huu, hvv]
    linear_combination - hl
  rw [hlag] at h
  rw [Real.sqrt_sq hpos.le] at h
  simpa using h
theorem angle_mem_Ioo (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) : 0 < angle u v ∧ angle u v < Real.pi := by
  have hsin : 0 < Real.sin (angle u v) := by
    rw [sin_angle_eq_cross u v hu hv hpos]; exact hpos
  constructor
  · rcases (angle_nonneg u v).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, Real.sin_zero] at hsin
      exact lt_irrefl 0 hsin
  · rcases (angle_le_pi u v).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h, Real.sin_pi] at hsin
      exact lt_irrefl 0 hsin
theorem mem_wedge_iff (θ : ℝ) (q : Plane) :
    q ∈ Erdos634.E2Join.wedge θ ↔
      q 0 ^ 2 + q 1 ^ 2 < 1 ∧ 0 < q 1 ∧ 0 < Real.sin θ * q 0 - Real.cos θ * q 1 := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by simpa [pow_two, Erdos634.E2Join.toPair] using h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨by simpa [pow_two, Erdos634.E2Join.toPair] using h1, h2⟩, h3⟩
theorem frame_image_wedge (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) :
    frame u (rot90 u) '' Erdos634.E2Join.wedge (angle u v)
      = {y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
          ∩ Metric.ball (0 : Plane) 1 := by
  have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_coords, hu]; norm_num
  have hsin := sin_angle_eq_cross u v hu hv hpos
  have hcos := cos_angle_eq_inner u v hu hv
  have hF0 : ∀ q : Plane, frame u (rot90 u) q 0 = q 0 * u 0 - q 1 * u 1 := by
    intro q; rw [frame_apply, rot90_apply0]; ring
  have hF1 : ∀ q : Plane, frame u (rot90 u) q 1 = q 0 * u 1 + q 1 * u 0 := by
    intro q; rw [frame_apply, rot90_apply1]
  have hnorm : ∀ q : Plane,
      (frame u (rot90 u) q) 0 ^ 2 + (frame u (rot90 u) q) 1 ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    intro q
    rw [hF0, hF1]
    linear_combination (q 0 ^ 2 + q 1 ^ 2) * hu2
  have hcru : ∀ q : Plane, cross u (frame u (rot90 u) q) = q 1 := by
    intro q
    simp only [cross]
    rw [hF0, hF1]
    linear_combination (q 1) * hu2
  have hcrv : ∀ q : Plane, cross (frame u (rot90 u) q) v
      = Real.sin (angle u v) * q 0 - Real.cos (angle u v) * q 1 := by
    intro q
    rw [hsin, hcos, inner_coords]
    simp only [cross]
    rw [hF0, hF1]
    ring
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_wedge_iff] at hq
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show 0 < cross u (frame u (rot90 u) q)
      rw [hcru]; exact h2
    · show 0 < cross (frame u (rot90 u) q) v
      rw [hcrv]; exact h3
    · rw [mem_ball_sq, hnorm]; exact h1
  · rintro ⟨⟨hy1, hy2⟩, hy3⟩
    set q : Plane := EuclideanSpace.single (0 : Fin 2) (u 0 * y 0 + u 1 * y 1)
      + EuclideanSpace.single (1 : Fin 2) (cross u y) with hqdef
    have hq0 : q 0 = u 0 * y 0 + u 1 * y 1 := by
      rw [hqdef]; simp
    have hq1 : q 1 = cross u y := by
      rw [hqdef]; simp
    have hcuy : cross u y = u 0 * y 1 - u 1 * y 0 := rfl
    have hy2' : 0 < y 0 * v 1 - y 1 * v 0 := hy2
    have hy1' : 0 < cross u y := hy1
    refine ⟨q, ?_, ?_⟩
    · rw [mem_wedge_iff]
      rw [mem_ball_sq] at hy3
      refine ⟨?_, ?_, ?_⟩
      · rw [hq0, hq1, hcuy]
        have hid : (u 0 * y 0 + u 1 * y 1) ^ 2 + (u 0 * y 1 - u 1 * y 0) ^ 2
            = y 0 ^ 2 + y 1 ^ 2 := by
          linear_combination (y 0 ^ 2 + y 1 ^ 2) * hu2
        rw [hid]
        exact hy3
      · rw [hq1]; exact hy1'
      · rw [hq0, hq1, hsin, hcos, inner_coords, hcuy]
        have hid : cross u v * (u 0 * y 0 + u 1 * y 1)
            - (u 0 * v 0 + u 1 * v 1) * (u 0 * y 1 - u 1 * y 0)
            = y 0 * v 1 - y 1 * v 0 := by
          simp only [cross]
          linear_combination (y 0 * v 1 - y 1 * v 0) * hu2
        rw [hid]
        exact hy2'
    · ext i
      fin_cases i
      · show frame u (rot90 u) q 0 = y 0
        rw [hF0, hq0, hq1, hcuy]
        linear_combination (y 0) * hu2
      · show frame u (rot90 u) q 1 = y 1
        rw [hF1, hq0, hq1, hcuy]
        linear_combination (y 1) * hu2
def vertexCone (u v : Plane) : Set Plane :=
  {y | 0 ≤ cross u y * cross u v ∧ 0 ≤ cross y v * cross u v}
theorem vertexCone_swap (u v : Plane) : vertexCone v u = vertexCone u v := by
  ext y
  simp only [vertexCone, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · calc (0:ℝ) ≤ cross y u * cross v u := h2
        _ = cross u y * cross u v := by rw [cross_swap y u, cross_swap v u]; ring
    · calc (0:ℝ) ≤ cross v y * cross v u := h1
        _ = cross y v * cross u v := by rw [cross_swap v y, cross_swap v u]; ring
  · rintro ⟨h1, h2⟩
    constructor
    · calc (0:ℝ) ≤ cross y v * cross u v := h2
        _ = cross v y * cross v u := by rw [cross_swap v y, cross_swap v u]; ring
    · calc (0:ℝ) ≤ cross u y * cross u v := h1
        _ = cross y u * cross v u := by rw [cross_swap y u, cross_swap v u]; ring
theorem nonneg_of_mul_nonneg_left' {a c : ℝ} (h : 0 ≤ c * a) (hc : 0 < c) : 0 ≤ a := by
  nlinarith
theorem vertexCone_smul (u v : Plane) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    vertexCone (s • u) (t • v) = vertexCone u v := by
  have e1 : ∀ y : Plane, cross (s • u) y * cross (s • u) (t • v)
      = (s * s * t) * (cross u y * cross u v) := by
    intro y
    rw [cross_smul_left, cross_smul_left, cross_smul_right]
    ring
  have e2 : ∀ y : Plane, cross y (t • v) * cross (s • u) (t • v)
      = (s * t * t) * (cross y v * cross u v) := by
    intro y
    rw [cross_smul_right, cross_smul_left, cross_smul_right]
    ring
  have h1 : (0:ℝ) < s * s * t := by positivity
  have h2 : (0:ℝ) < s * t * t := by positivity
  ext y
  simp only [vertexCone, Set.mem_setOf_eq, e1, e2]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨nonneg_of_mul_nonneg_left' ha h1, nonneg_of_mul_nonneg_left' hb h2⟩
  · rintro ⟨ha, hb⟩
    exact ⟨mul_nonneg h1.le ha, mul_nonneg h2.le hb⟩
theorem volume_cross_zero (u v : Plane) (hne : cross u v ≠ 0) :
    volume {y : Plane | cross u y = 0} = 0 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    apply hne
    show (0:Plane) 0 * v 1 - (0:Plane) 1 * v 0 = 0
    simp
  have hsub : {y : Plane | cross u y = 0} ⊆ (Submodule.span ℝ {u} : Submodule ℝ Plane) := by
    intro y hy
    obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hu0 hy
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨τ, hτ.symm⟩
  have htop : (Submodule.span ℝ ({u} : Set Plane)) ≠ ⊤ := by
    intro htop
    have hv : v ∈ Submodule.span ℝ ({u} : Set Plane) := by
      rw [htop]; trivial
    obtain ⟨τ, hτ⟩ := Submodule.mem_span_singleton.mp hv
    apply hne
    rw [← hτ, cross_smul_right, cross_self, mul_zero]
  have hnull := MeasureTheory.Measure.addHaar_submodule (volume : Measure Plane) _ htop
  have hle : volume {y : Plane | cross u y = 0}
      ≤ volume ((Submodule.span ℝ ({u} : Set Plane) : Submodule ℝ Plane) : Set Plane) :=
    measure_mono hsub
  rw [hnull] at hle
  exact nonpos_iff_eq_zero.mp hle
theorem volume_vertexCone_unit_pos (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hpos : 0 < cross u v) :
    volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
      = ENNReal.ofReal (angle u v / 2) := by
  set θ := angle u v with hθ
  obtain ⟨hθ0, hθπ⟩ := angle_mem_Ioo u v hu hv hpos
  have hopen : volume ({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
      ∩ Metric.ball (0 : Plane) 1) = ENNReal.ofReal (θ / 2) := by
    rw [← frame_image_wedge u v hu hv hpos,
      Measure.addHaar_image_linearMap volume (frame u (rot90 u))]
    have hdet : LinearMap.det (frame u (rot90 u)) = 1 := by
      rw [frame_det, rot90_apply0, rot90_apply1]
      have hu2 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_coords, hu]; norm_num
      linear_combination hu2
    rw [hdet]
    simp only [abs_one, ENNReal.ofReal_one, one_mul]
    exact Erdos634.E2Join.volume_wedge hθ0 hθπ
  have hCpos : vertexCone u v = {y : Plane | 0 ≤ cross u y ∧ 0 ≤ cross y v} := by
    ext y
    simp only [vertexCone, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · nlinarith [h1, hpos]
      · nlinarith [h2, hpos]
    · rintro ⟨h1, h2⟩
      exact ⟨mul_nonneg h1 hpos.le, mul_nonneg h2 hpos.le⟩
  have hsplit : vertexCone u v ∩ Metric.ball (0 : Plane) 1
      ⊆ ({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
          ∩ Metric.ball (0 : Plane) 1)
        ∪ ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0}) := by
    rintro y ⟨hy, hyb⟩
    rw [hCpos] at hy
    obtain ⟨h1, h2⟩ := hy
    rcases h1.lt_or_eq with h1' | h1'
    · rcases h2.lt_or_eq with h2' | h2'
      · exact Or.inl ⟨⟨h1', h2'⟩, hyb⟩
      · exact Or.inr (Or.inr h2'.symm)
    · exact Or.inr (Or.inl h1'.symm)
  have hnull1 : volume {y : Plane | cross u y = 0} = 0 :=
    volume_cross_zero u v hpos.ne'
  have hnull2 : volume {y : Plane | cross y v = 0} = 0 := by
    have hvu : cross v u ≠ 0 := by
      rw [cross_swap v u]
      simpa using hpos.ne'
    have h := volume_cross_zero v u hvu
    have hEq : {y : Plane | cross y v = 0} = {y : Plane | cross v y = 0} := by
      ext y
      simp only [Set.mem_setOf_eq]
      rw [cross_swap y v]
      constructor <;> intro h' <;> linarith
    rw [hEq]
    exact h
  have hle1 : volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
      ≤ ENNReal.ofReal (θ / 2) := by
    calc volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
        ≤ volume (({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
            ∩ Metric.ball (0 : Plane) 1)
          ∪ ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0})) :=
          measure_mono hsplit
      _ ≤ volume ({y : Plane | 0 < cross u y} ∩ {y : Plane | 0 < cross y v}
            ∩ Metric.ball (0 : Plane) 1)
          + volume ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0}) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (θ / 2) + (volume {y : Plane | cross u y = 0}
          + volume {y : Plane | cross y v = 0}) := by
          rw [hopen]
          have hun : volume ({y : Plane | cross u y = 0} ∪ {y : Plane | cross y v = 0})
              ≤ volume {y : Plane | cross u y = 0} + volume {y : Plane | cross y v = 0} :=
            measure_union_le _ _
          exact add_le_add le_rfl hun
      _ = ENNReal.ofReal (θ / 2) := by rw [hnull1, hnull2, add_zero, add_zero]
  have hle2 : ENNReal.ofReal (θ / 2)
      ≤ volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1) := by
    rw [← hopen]
    refine measure_mono ?_
    rintro y ⟨⟨h1, h2⟩, hyb⟩
    refine ⟨?_, hyb⟩
    rw [hCpos]
    exact ⟨h1.le, h2.le⟩
  exact le_antisymm hle1 hle2
theorem volume_vertexCone_unit (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hne : cross u v ≠ 0) :
    volume (vertexCone u v ∩ Metric.ball (0 : Plane) 1)
      = ENNReal.ofReal (angle u v / 2) := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hpos' : 0 < cross v u := by
      rw [cross_swap v u]; linarith
    rw [← vertexCone_swap, angle_comm]
    exact volume_vertexCone_unit_pos v u hv hu hpos'
  · exact volume_vertexCone_unit_pos u v hu hv hpos
theorem vertexCone_ball_smul (u v : Plane) {r : ℝ} (hr : 0 < r) :
    vertexCone u v ∩ Metric.ball (0 : Plane) r
      = r • (vertexCone u v ∩ Metric.ball (0 : Plane) 1) := by
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  simp only [vertexCone, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_ball,
    dist_zero_right, cross_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hrinv]
  have hcl : ∀ z : Plane, cross (r⁻¹ • y) z = r⁻¹ * cross y z := fun z =>
    cross_smul_left r⁻¹ y z
  rw [hcl]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc (0:ℝ) ≤ r⁻¹ * (cross u y * cross u v) := by positivity
        _ = r⁻¹ * cross u y * cross u v := by ring
    · calc (0:ℝ) ≤ r⁻¹ * (cross y v * cross u v) := by positivity
        _ = r⁻¹ * cross y v * cross u v := by ring
    · calc r⁻¹ * ‖y‖ < r⁻¹ * r := mul_lt_mul_of_pos_left h3 hrinv
        _ = 1 := inv_mul_cancel₀ hr.ne'
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1' : 0 ≤ r * (r⁻¹ * cross u y * cross u v) := by positivity
      calc (0:ℝ) ≤ r * (r⁻¹ * cross u y * cross u v) := h1'
        _ = cross u y * cross u v := by
            field_simp
    · have h2' : 0 ≤ r * (r⁻¹ * cross y v * cross u v) := by positivity
      calc (0:ℝ) ≤ r * (r⁻¹ * cross y v * cross u v) := h2'
        _ = cross y v * cross u v := by
            field_simp
    · have := mul_lt_mul_of_pos_left h3 hr
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_one] at this
      exact this
theorem volume_vertexCone_ball (u v : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hne : cross u v ≠ 0) {r : ℝ} (hr : 0 < r) :
    volume (vertexCone u v ∩ Metric.ball (0 : Plane) r)
      = ENNReal.ofReal (angle u v / 2 * r ^ 2) := by
  rw [vertexCone_ball_smul u v hr, Measure.addHaar_smul,
    volume_vertexCone_unit u v hu hv hne]
  have hfr : Module.finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  rw [hfr]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ 2)]
  ring
noncomputable def Tri.edgeVec (T : Tri) (j : Fin 3) : Plane := T.pts (j + 1) - T.pts j
theorem Tri.edgeVec_ne_zero (T : Tri) (j : Fin 3) : T.edgeVec j ≠ 0 := by
  rw [Tri.edgeVec, sub_ne_zero]
  intro h
  have h1 : j + 1 = j := T.indep.injective h
  have h2 : ∀ m : Fin 3, m + 1 ≠ m := by decide
  exact h2 j h1
noncomputable def Tri.edgeVec' (T : Tri) (j : Fin 3) : Plane := T.pts (j + 2) - T.pts j
theorem Tri.edgeVec'_ne_zero (T : Tri) (j : Fin 3) : T.edgeVec' j ≠ 0 := by
  rw [Tri.edgeVec', sub_ne_zero]
  intro h
  have h1 : j + 2 = j := T.indep.injective h
  have h2 : ∀ m : Fin 3, m + 2 ≠ m := by decide
  exact h2 j h1
theorem Tri.cross_edgeVec (T : Tri) (j : Fin 3) :
    cross (T.edgeVec j) (T.edgeVec' j) = T.det := T.det_cyclic j
theorem Tri.inter_ball_eq_vertexCone (T : Tri) (j : Fin 3) :
    ∃ r > 0, T.carrier ∩ Metric.ball (T.pts j) r
      = {y : Plane | y - T.pts j ∈ vertexCone (T.edgeVec j) (T.edgeVec' j)}
        ∩ Metric.ball (T.pts j) r := by
  have hcont : Continuous (T.basis.coord j) := AffineMap.continuous_of_finiteDimensional _
  have hj1 : T.basis.coord j (T.pts j) = 1 := T.basis.coord_apply_eq j
  have hopen : IsOpen {y : Plane | 0 < T.basis.coord j y} :=
    isOpen_lt continuous_const hcont
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (T.pts j) (by
    rw [Set.mem_setOf_eq, hj1]; norm_num)
  refine ⟨r, hr, ?_⟩
  have hfin : ∀ m : Fin 3, (m + 2) + 2 = m + 1 ∧ (m + 2) + 1 = m := by decide
  have hc2 : ∀ y : Plane, T.basis.coord (j + 2) y * T.det
      = cross (T.edgeVec j) (y - T.pts j) := fun y => T.coord_mul_det j y
  have hc1 : ∀ y : Plane, T.basis.coord (j + 1) y * T.det
      = cross (y - T.pts j) (T.edgeVec' j) := by
    intro y
    have h := T.coord_mul_det (j + 2) y
    rw [(hfin j).1, (hfin j).2] at h
    rw [h]
    have hsplit : y - T.pts (j + 2) = (y - T.pts j) - T.edgeVec' j := by
      rw [Tri.edgeVec']; abel
    have h1 : T.pts j - T.pts (j + 2) = -(T.edgeVec' j) := by
      rw [Tri.edgeVec']; abel
    rw [hsplit, cross_sub_right, h1, cross_neg_left, cross_neg_left, cross_self,
      neg_zero, sub_zero]
    rw [cross_swap (T.edgeVec' j) ((y - T.pts j))]
    ring
  have hsq : (0:ℝ) < T.det ^ 2 := by
    have := T.det_ne_zero
    positivity
  ext y
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, T.carrier_eq_nonneg_coord, vertexCone]
  constructor
  · rintro ⟨hy, hyb⟩
    refine ⟨⟨?_, ?_⟩, hyb⟩
    · rw [T.cross_edgeVec j]
      have h := hc2 y
      have hcd : cross (T.edgeVec j) (y - T.pts j) * T.det
          = T.basis.coord (j + 2) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd]
      exact mul_nonneg (hy (j + 2)) hsq.le
    · rw [T.cross_edgeVec j]
      have h := hc1 y
      have hcd : cross (y - T.pts j) (T.edgeVec' j) * T.det
          = T.basis.coord (j + 1) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd]
      exact mul_nonneg (hy (j + 1)) hsq.le
  · rintro ⟨⟨h1, h2⟩, hyb⟩
    rw [T.cross_edgeVec j] at h1 h2
    refine ⟨fun i => ?_, hyb⟩
    have hexh : ∀ m i : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    rcases hexh j i with rfl | rfl | rfl
    · exact (hball hyb).le
    · have h := hc1 y
      have hcd : cross (y - T.pts j) (T.edgeVec' j) * T.det
          = T.basis.coord (j + 1) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd] at h2
      nlinarith [h2, hsq]
    · have h := hc2 y
      have hcd : cross (T.edgeVec j) (y - T.pts j) * T.det
          = T.basis.coord (j + 2) y * T.det ^ 2 := by rw [← h]; ring
      rw [hcd] at h1
      nlinarith [h1, hsq]
theorem Tri.cornerAngle_eq_angle (T : Tri) (j : Fin 3) :
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))
      = angle (T.edgeVec j) (T.edgeVec' j) := by
  rw [cornerAngle, EuclideanGeometry.angle, Tri.edgeVec, Tri.edgeVec']
  simp [vsub_eq_sub]
theorem Tri.volume_inter_ball_vertex (T : Tri) (j : Fin 3) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball (T.pts j) r')
        = ENNReal.ofReal
            (cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) / 2 * r' ^ 2) := by
  obtain ⟨r, hr, hEq⟩ := T.inter_ball_eq_vertexCone j
  refine ⟨r, hr, fun r' hr' hle => ?_⟩
  rw [inter_ball_mono hEq hle]
  set u := T.edgeVec j with hudef
  set v := T.edgeVec' j with hvdef
  have hu0 : u ≠ 0 := T.edgeVec_ne_zero j
  have hv0 : v ≠ 0 := T.edgeVec'_ne_zero j
  have hun : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hvn : (0:ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  have hsupos : 0 < ‖u‖⁻¹ := inv_pos.mpr hun
  have hsvpos : 0 < ‖v‖⁻¹ := inv_pos.mpr hvn
  have hunorm : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsupos, inv_mul_cancel₀ hun.ne']
  have hvnorm : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsvpos, inv_mul_cancel₀ hvn.ne']
  have hcone : vertexCone u v = vertexCone (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) :=
    (vertexCone_smul u v hsupos hsvpos).symm
  have hangle : angle (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) = angle u v := by
    rw [angle_smul_left_of_pos _ _ hsupos, angle_smul_right_of_pos _ _ hsvpos]
  have hcross : cross (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) ≠ 0 := by
    rw [cross_smul_left, cross_smul_right, T.cross_edgeVec j]
    have hd := T.det_ne_zero
    positivity
  have htrans : (fun z : Plane => T.pts j + z) ⁻¹'
      ({y : Plane | y - T.pts j ∈ vertexCone u v} ∩ Metric.ball (T.pts j) r')
      = vertexCone u v ∩ Metric.ball (0 : Plane) r' := by
    ext z
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_ball]
    rw [add_sub_cancel_left, dist_eq_norm, add_sub_cancel_left, dist_zero_right]
  calc volume ({y : Plane | y - T.pts j ∈ vertexCone u v} ∩ Metric.ball (T.pts j) r')
      = volume ((fun z : Plane => T.pts j + z) ⁻¹'
          ({y : Plane | y - T.pts j ∈ vertexCone u v} ∩ Metric.ball (T.pts j) r')) := by
        rw [measure_preimage_add]
    _ = volume (vertexCone u v ∩ Metric.ball (0 : Plane) r') := by rw [htrans]
    _ = volume (vertexCone (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) ∩ Metric.ball (0 : Plane) r') := by
        rw [← hcone]
    _ = ENNReal.ofReal (angle (‖u‖⁻¹ • u) (‖v‖⁻¹ • v) / 2 * r' ^ 2) :=
        volume_vertexCone_ball _ _ hunorm hvnorm hcross hr'
    _ = ENNReal.ofReal
          (cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) / 2 * r' ^ 2) := by
        rw [hangle, hudef, hvdef, ← T.cornerAngle_eq_angle j]
theorem volume_ball_plane (x : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball x r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  rw [EuclideanSpace.volume_ball]
  have hcard : Fintype.card (Fin 2) = 2 := by simp
  rw [hcard]
  have hg : Real.Gamma (1 + 1) = 1 := by
    have h := Real.Gamma_add_one (s := 1) one_ne_zero
    rw [Real.Gamma_one] at h
    simpa using h
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  rw [show (2 : ℝ) / 2 + 1 = 1 + 1 by norm_num, hg, Real.sq_sqrt Real.pi_pos.le]
  ring
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open MeasureTheory Set Metric
open scoped ENNReal
open Classical in
noncomputable def Tri.localAngle (T : Tri) (p : Plane) : ℝ :=
  if h : ∃ j, p = T.pts j then
    cornerAngle (T.pts (h.choose + 1)) (T.pts h.choose) (T.pts (h.choose + 2))
  else if ∀ j, 0 < T.basis.coord j p then 2 * Real.pi
  else if ∃ k, T.basis.coord k p = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j p then Real.pi
  else 0
theorem Tri.localAngle_nonneg (T : Tri) (p : Plane) : 0 ≤ T.localAngle p := by
  classical
  rw [Tri.localAngle]
  split
  · exact EuclideanGeometry.angle_nonneg _ _ _
  · split
    · positivity
    · split
      · exact Real.pi_pos.le
      · exact le_refl 0
theorem Tri.volume_inter_ball_localAngle (T : Tri) (p : Plane) :
    ∃ r > 0, ∀ r', 0 < r' → r' ≤ r →
      volume (T.carrier ∩ Metric.ball p r')
        = ENNReal.ofReal (T.localAngle p / 2 * r' ^ 2) := by
  classical
  by_cases hv : ∃ j, p = T.pts j
  · 
    obtain ⟨r, hr, h⟩ := T.volume_inter_ball_vertex hv.choose
    refine ⟨r, hr, fun r' h1 h2 => ?_⟩
    rw [Tri.localAngle, dif_pos hv]
    have hspec := hv.choose_spec
    set j0 := hv.choose with hj0
    rw [hspec]
    exact h r' h1 h2
  · push_neg at hv
    rcases T.classify hv with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hkneg⟩
    · 
      obtain ⟨r, hr, h⟩ := T.volume_inter_ball_interior hpos
      refine ⟨r, hr, fun r' h1 h2 => ?_⟩
      rw [Tri.localAngle, dif_neg (not_exists.mpr hv), if_pos hpos,
        h r' h1 h2, volume_ball_plane p h1.le]
      congr 1
      ring
    · 
      have hne : ∀ j : Fin 3, j + 1 ≠ j ∧ j + 2 ≠ j := by decide
      obtain ⟨r, hr, h⟩ := T.volume_inter_ball_edge k hk0
        (hkpos _ (hne k).1) (hkpos _ (hne k).2)
      refine ⟨r, hr, fun r' h1 h2 => ?_⟩
      have hIn : ¬ ∀ j, 0 < T.basis.coord j p := fun hI => absurd hk0 (ne_of_gt (hI k))
      rw [Tri.localAngle, dif_neg (not_exists.mpr hv), if_neg hIn,
        if_pos ⟨k, hk0, hkpos⟩]
      have h2v := h r' h1 h2
      rw [volume_ball_plane p h1.le] at h2v
      have hhalf : (2 : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 2 * r' ^ 2)
          = ENNReal.ofReal (Real.pi * r' ^ 2) := by
        rw [show ((2 : ℝ≥0∞)) = ENNReal.ofReal (2 : ℝ) by simp,
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        ring
      rw [← hhalf] at h2v
      exact (ENNReal.mul_right_inj (by norm_num) (by norm_num)).mp h2v
    · 
      obtain ⟨r, hr, h⟩ := T.volume_inter_ball_exterior hkneg
      refine ⟨r, hr, fun r' h1 h2 => ?_⟩
      have hIn : ¬ ∀ j, 0 < T.basis.coord j p := fun hI =>
        absurd (hI k) (not_lt.mpr hkneg.le)
      have hOn : ¬ ∃ m, T.basis.coord m p = 0 ∧ ∀ j, j ≠ m → 0 < T.basis.coord j p := by
        rintro ⟨m, hm, hrest⟩
        by_cases hmk : k = m
        · rw [hmk] at hkneg; exact absurd hm (ne_of_lt hkneg)
        · exact absurd (hrest k hmk) (not_lt.mpr hkneg.le)
      rw [Tri.localAngle, dif_neg (not_exists.mpr hv), if_neg hIn, if_neg hOn,
        h r' h1 h2]
      simp
theorem Tri.mem_interior_iff_coord_pos (T : Tri) (p : Plane) :
    p ∈ interior T.carrier ↔ ∀ j, 0 < T.basis.coord j p := by
  constructor
  · exact fun hp => T.interior_coord_pos hp
  · intro hpos
    obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
    exact mem_interior.mpr ⟨Metric.ball p r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
theorem Tri.localAngle_interior (T : Tri) {p : Plane} (hp : p ∈ interior T.carrier) :
    T.localAngle p = 2 * Real.pi := by
  classical
  have hpos := T.interior_coord_pos hp
  have hv : ¬ ∃ j, p = T.pts j := by
    rintro ⟨j, rfl⟩
    have hne : ∀ m : Fin 3, m + 1 ≠ m := by decide
    have h0 : T.basis.coord (j + 1) (T.pts j) = 0 := T.basis.coord_apply_ne (hne j)
    exact absurd h0 (ne_of_gt (hpos (j + 1)))
  rw [Tri.localAngle, dif_neg hv, if_pos hpos]
theorem Tri.localAngle_frontier (T : Tri) {p : Plane} (hp : p ∈ frontier T.carrier)
    (hv : p ∉ Set.range T.pts) : T.localAngle p = Real.pi := by
  classical
  have hv' : ∀ k, p ≠ T.pts k := fun k h => hv ⟨k, h.symm⟩
  have hcar : p ∈ T.carrier := by
    have h1 : p ∈ closure T.carrier := frontier_subset_closure hp
    rwa [T.isCompact.isClosed.closure_eq] at h1
  have hnint : p ∉ interior T.carrier := fun h => hp.2 h
  rcases T.classify hv' with hpos | ⟨k, hk0, hkpos⟩ | ⟨k, hkneg⟩
  · exact absurd ((T.mem_interior_iff_coord_pos p).mpr hpos) hnint
  · have hIn : ¬ ∀ j, 0 < T.basis.coord j p := fun hI => absurd hk0 (ne_of_gt (hI k))
    rw [Tri.localAngle, dif_neg (not_exists.mpr hv'), if_neg hIn,
      if_pos ⟨k, hk0, hkpos⟩]
  · rw [T.carrier_eq_nonneg_coord] at hcar
    exact absurd (hcar k) (not_le.mpr hkneg)
theorem Tri.localAngle_vertex (T : Tri) (k : Fin 3) :
    T.localAngle (T.pts k)
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  classical
  have hv : ∃ j, T.pts k = T.pts j := ⟨k, rfl⟩
  rw [Tri.localAngle, dif_pos hv]
  have hk : hv.choose = k := T.indep.injective hv.choose_spec.symm
  rw [hk]
theorem Dissection.volume_inter_ball_eq_sum {N : ℕ} (D : Dissection N) (x : Plane) (r : ℝ) :
    volume (D.target.carrier ∩ Metric.ball x r)
      = ∑ i, volume ((D.tile i).carrier ∩ Metric.ball x r) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ Metric.ball x r)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter
      Metric.isOpen_ball.measurableSet.nullMeasurableSet)
  have hU : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ Metric.ball x r))
          = D.target.carrier ∩ Metric.ball x r := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
  rw [hU] at h
  exact h
theorem Dissection.sum_localAngle_eq {N : ℕ} (D : Dissection N) (p : Plane) :
    ∑ i, (D.tile i).localAngle p = D.target.localAngle p := by
  classical
  obtain ⟨rT, hrT, hT⟩ := D.target.volume_inter_ball_localAngle p
  choose ri hri hcontrib using fun i => (D.tile i).volume_inter_ball_localAngle p
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius D.pos ri hri
  set r : ℝ := min rT r0 with hrdef
  have hrpos : 0 < r := lt_min hrT hr0
  have hsum := D.volume_inter_ball_eq_sum p r
  rw [hT r hrpos (min_le_left _ _)] at hsum
  have htiles : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      volume ((D.tile i).carrier ∩ Metric.ball p r)
        = ENNReal.ofReal ((D.tile i).localAngle p / 2 * r ^ 2) := fun i _ =>
    hcontrib i r hrpos ((min_le_right _ _).trans (hr0le i))
  rw [Finset.sum_congr rfl htiles,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      have := (D.tile i).localAngle_nonneg p
      positivity)] at hsum
  have hreal := (ENNReal.ofReal_eq_ofReal_iff
    (by have := D.target.localAngle_nonneg p; positivity)
    (Finset.sum_nonneg fun i _ => by
      have := (D.tile i).localAngle_nonneg p
      positivity)).mp hsum
  have hfact : ∑ i, (D.tile i).localAngle p / 2 * r ^ 2
      = (∑ i, (D.tile i).localAngle p) * (r ^ 2 / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfact] at hreal
  have hr2 : (0:ℝ) < r ^ 2 / 2 := by positivity
  have hkey : (∑ i, (D.tile i).localAngle p) * (r ^ 2 / 2)
      = D.target.localAngle p * (r ^ 2 / 2) := by
    rw [← hreal]; ring
  exact mul_right_cancel₀ hr2.ne' hkey
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
def Tri.Congruent (T U : Tri) : Prop :=
  ∃ (f : Plane ≃ᵢ Plane) (σ : Equiv.Perm (Fin 3)), ∀ k, f (T.pts k) = U.pts (σ k)
theorem Tri.Congruent.symm {T U : Tri} (h : T.Congruent U) : U.Congruent T := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨f.symm, σ.symm, fun k => ?_⟩
  have hk := hf (σ.symm k)
  rw [Equiv.apply_symm_apply] at hk
  rw [← hk, IsometryEquiv.symm_apply_apply]
theorem Tri.Congruent.trans {T U V : Tri} (h₁ : T.Congruent U) (h₂ : U.Congruent V) :
    T.Congruent V := by
  obtain ⟨f, σ, hf⟩ := h₁
  obtain ⟨g, τ, hg⟩ := h₂
  exact ⟨f.trans g, σ.trans τ, fun k => by simp [hf k, hg (σ k)]⟩
theorem Tri.Congruent.dist_eq {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts (σ i)) (U.pts (σ j)) := by
  obtain ⟨f, σ, hf⟩ := h
  exact ⟨σ, fun i j => by rw [← hf i, ← hf j, f.dist_eq]⟩
noncomputable def Tri.relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : Tri where
  pts := T.pts ∘ τ
  indep := T.indep.comp_embedding τ.toEmbedding
theorem Tri.relabel_pts (T : Tri) (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.relabel τ).pts k = T.pts (τ k) := rfl
theorem Tri.congruent_relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : T.Congruent (T.relabel τ) := by
  refine ⟨IsometryEquiv.refl Plane, τ.symm, fun k => ?_⟩
  show T.pts k = (T.relabel τ).pts (τ.symm k)
  simp [Tri.relabel_pts]
structure CongruentDissection (N : ℕ) extends Dissection N where
  model : Tri
  tiles_congruent : ∀ i, (tile i).Congruent model
namespace CongruentDissection
variable {N : ℕ}
end CongruentDissection
end Erdos634.Geometry
end

section
namespace Erdos634.CongruentArea
open Erdos634.Geometry MeasureTheory
open scoped ENNReal
theorem measurePreserving_isometryEquiv (f : Plane ≃ᵢ Plane) :
    MeasurePreserving f volume volume := by
  have hdecomp : (f : Plane → Plane) = (fun y => y + f 0) ∘ (f.toRealLinearIsometryEquiv) := by
    funext x
    simp
  have hlin : MeasurePreserving (f.toRealLinearIsometryEquiv) volume volume :=
    LinearIsometryEquiv.measurePreserving _
  have htr : MeasurePreserving (fun y : Plane => y + f 0) volume volume :=
    measurePreserving_add_right volume (f 0)
  rw [show (f : Plane → Plane) = (fun y => y + f 0) ∘ (f.toRealLinearIsometryEquiv) from hdecomp]
  exact htr.comp hlin
theorem volume_image_isometryEquiv (f : Plane ≃ᵢ Plane) (s : Set Plane)
    (hs : NullMeasurableSet s volume) :
    volume (f '' s) = volume s := by
  have himg : f '' s = (f.symm) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨f.symm y, hy, by simp⟩
  rw [himg]
  exact (measurePreserving_isometryEquiv f.symm).measure_preimage hs
theorem image_carrier_of_congruent {T U : Tri} {f : Plane ≃ᵢ Plane} {σ : Equiv.Perm (Fin 3)}
    (hf : ∀ k, f (T.pts k) = U.pts (σ k)) :
    f '' T.carrier = U.carrier := by
  have hpts : f '' (Set.range T.pts) = Set.range U.pts := by
    ext y
    constructor
    · rintro ⟨x, ⟨k, rfl⟩, rfl⟩
      exact ⟨σ k, (hf k).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨T.pts (σ.symm j), ⟨σ.symm j, rfl⟩, ?_⟩
      rw [hf (σ.symm j), Equiv.apply_symm_apply]
  have haff : ⇑f.toRealAffineIsometryEquiv.toAffineMap = ⇑f := rfl
  rw [Erdos634.Geometry.Tri.carrier, Erdos634.Geometry.Tri.carrier, ← hpts, ← haff,
    AffineMap.image_convexHull]
theorem volume_congruent {T U : Tri} (h : T.Congruent U) :
    volume T.carrier = volume U.carrier := by
  obtain ⟨f, σ, hf⟩ := h
  rw [← image_carrier_of_congruent hf, volume_image_isometryEquiv f _ T.nullMeasurableSet]
theorem congruentDissection_volume_target {N : ℕ} (D : CongruentDissection N) :
    volume D.target.carrier = (N : ℝ≥0∞) * volume D.model.carrier :=
  D.toDissection.volume_target_of_congruent (volume D.model.carrier)
    (fun i => volume_congruent (D.tiles_congruent i))
end Erdos634.CongruentArea
end

section
namespace Erdos634.AreaDet
open Erdos634.Geometry MeasureTheory
noncomputable def pb : Module.Basis (Fin 2) ℝ Plane := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
noncomputable def edgeMap (T : Tri) : Plane →ₗ[ℝ] Plane :=
  pb.constr ℝ (fun i : Fin 2 => T.pts i.succ - T.pts 0)
noncomputable def detTri (T : Tri) : ℝ := LinearMap.det (edgeMap T)
noncomputable def stdCarrier : Set Plane :=
  convexHull ℝ (Set.range ![(0 : Plane), pb 0, pb 1])
noncomputable def placeMap (T : Tri) : Plane →ᵃ[ℝ] Plane :=
  (AffineEquiv.constVAdd ℝ Plane (T.pts 0)).toAffineMap.comp (edgeMap T).toAffineMap
theorem placeMap_apply (T : Tri) (x : Plane) : placeMap T x = T.pts 0 + edgeMap T x := by
  rfl
theorem edgeMap_basis (T : Tri) (i : Fin 2) : edgeMap T (pb i) = T.pts i.succ - T.pts 0 := by
  simp [edgeMap, Module.Basis.constr_basis]
theorem placeMap_range (T : Tri) :
    (placeMap T) '' (Set.range ![(0 : Plane), pb 0, pb 1]) = Set.range T.pts := by
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  have hv : ∀ i : Fin 3, placeMap T (![(0 : Plane), pb 0, pb 1] i) = T.pts i := by
    intro i
    rcases htri i with rfl | rfl | rfl
    · show placeMap T 0 = T.pts 0
      simp [placeMap_apply]
    · show placeMap T (pb 0) = T.pts 1
      rw [placeMap_apply, edgeMap_basis]
      show T.pts 0 + (T.pts 1 - T.pts 0) = T.pts 1
      abel
    · show placeMap T (pb 1) = T.pts 2
      rw [placeMap_apply, edgeMap_basis]
      show T.pts 0 + (T.pts 2 - T.pts 0) = T.pts 2
      abel
  rw [← Set.range_comp]
  exact congrArg Set.range (funext hv)
theorem placeMap_stdCarrier (T : Tri) : (placeMap T) '' stdCarrier = T.carrier := by
  rw [stdCarrier, AffineMap.image_convexHull, placeMap_range, Erdos634.Geometry.Tri.carrier]
theorem volume_eq_det_mul (T : Tri) :
    volume T.carrier = ENNReal.ofReal |detTri T| * volume stdCarrier := by
  rw [← placeMap_stdCarrier T]
  have hcomp : (placeMap T) '' stdCarrier
      = (fun h => T.pts 0 + h) '' (edgeMap T '' stdCarrier) := by
    rw [← Set.image_comp]
    exact congrArg (· '' stdCarrier) (funext fun x => placeMap_apply T x)
  have hpre : (fun h : Plane => T.pts 0 + h) '' (edgeMap T '' stdCarrier)
      = (fun h : Plane => (-T.pts 0) + h) ⁻¹' (edgeMap T '' stdCarrier) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hy; exact ⟨(-T.pts 0) + y, hy, by abel⟩
  rw [hcomp, hpre, measure_preimage_add, Measure.addHaar_image_linearMap]
  rfl
theorem pb_repr (v : Plane) (i : Fin 2) : pb.repr v i = v i := by
  simp [pb]
theorem detTri_eq (T : Tri) :
    detTri T = (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1
             - (T.pts 2 - T.pts 0) 0 * (T.pts 1 - T.pts 0) 1 := by
  rw [detTri, ← LinearMap.det_toMatrix pb, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, edgeMap_basis, pb_repr]
theorem isCompact_stdCarrier : IsCompact stdCarrier :=
  (Set.finite_range _).isCompact_convexHull ℝ
end Erdos634.AreaDet
end

section
namespace Erdos634.Geometry
open MeasureTheory Set
theorem Tri.carrier_subset_halfplane (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (h : ∀ i, f (T.pts i) ≤ c) : ∀ y ∈ T.carrier, f y ≤ c := by
  intro y hy
  rw [Tri.carrier] at hy
  have hsub : convexHull ℝ (Set.range T.pts) ⊆ {z | f z ≤ c} := by
    refine convexHull_min ?_ ?_
    · rintro z ⟨i, rfl⟩
      exact h i
    · intro p hp q hq a b ha hb hab
      simp only [Set.mem_setOf_eq] at hp hq ⊢
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      have habc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
      have h1 : a * f p ≤ a * c := mul_le_mul_of_nonneg_left hp ha
      have h2 : b * f q ≤ b * c := mul_le_mul_of_nonneg_left hq hb
      linarith
  exact hsub hy
theorem Dissection.carrier_point_not_interior {N : ℕ} (D : Dissection N)
    {j : Fin N} {x : Plane} (hx : x ∈ (D.tile j).carrier) :
    ∀ i, i ≠ j → x ∉ interior (D.tile i).carrier := by
  intro i hij hi
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hi
  obtain ⟨y₀, hy₀⟩ := (D.tile j).interior_nonempty
  by_cases hyx : y₀ ∈ Metric.ball x r
  · exact Set.disjoint_left.mp (D.interiors_disjoint hij) (hball hyx) hy₀
  · have hd : r ≤ ‖y₀ - x‖ := by
      rw [Metric.mem_ball, dist_eq_norm] at hyx
      push_neg at hyx
      exact hyx
    have hdpos : 0 < ‖y₀ - x‖ := lt_of_lt_of_le hr hd
    set t := r / (2 * ‖y₀ - x‖) with htdef
    have htpos : 0 < t := by positivity
    have htlt : t < 1 := by
      rw [htdef]
      rw [div_lt_one (by positivity)]
      linarith
    set z := x + t • (y₀ - x) with hzdef
    have hz₁ : z ∈ openSegment ℝ x y₀ := by
      rw [openSegment_eq_image' ℝ x y₀]
      exact ⟨t, ⟨htpos, htlt⟩, rfl⟩
    have hz₂ : z ∈ interior (D.tile j).carrier := by
      have hseg : openSegment ℝ y₀ x ⊆ interior (D.tile j).carrier :=
        (D.tile j).convex.openSegment_interior_closure_subset_interior hy₀
          (subset_closure hx)
      rw [openSegment_symm ℝ x y₀] at hz₁
      exact hseg hz₁
    have hz₃ : z ∈ interior (D.tile i).carrier := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : z - x = t • (y₀ - x) := by rw [hzdef]; abel
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      have h2 : t * ‖y₀ - x‖ = r / 2 := by
        rw [htdef]; field_simp
      rw [h2]; linarith
    exact Set.disjoint_left.mp (D.interiors_disjoint hij) hz₃ hz₂
theorem Dissection.edge_point_not_interior {N : ℕ} (D : Dissection N)
    {j : Fin N} {k : Fin 3} {x : Plane} (hx : x ∈ (D.tile j).edge k) :
    ∀ i, x ∉ interior (D.tile i).carrier := by
  intro i hi
  by_cases hij : i = j
  · subst hij
    have hz := (D.tile i).coord_eq_zero_of_mem_edge k hx
    exact absurd hz (ne_of_gt ((D.tile i).interior_coord_pos hi (k + 2)))
  · exact D.carrier_point_not_interior ((D.tile j).edge_subset_carrier k hx) i hij hi
theorem openSegment_two_sided {u₁ u₂ x : Plane} (hx : x ∈ openSegment ℝ u₁ u₂) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| < ε₀ → x + ε • (u₂ - u₁) ∈ openSegment ℝ u₁ u₂ := by
  rw [openSegment_eq_image' ℝ u₁ u₂] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  refine ⟨min t (1 - t), lt_min ht.1 (by linarith [ht.2]), fun ε hε => ?_⟩
  rw [openSegment_eq_image' ℝ u₁ u₂]
  refine ⟨t + ε, ⟨?_, ?_⟩, ?_⟩
  · have h1 : |ε| < t := lt_of_lt_of_le hε (min_le_left _ _)
    have h2 := abs_lt.mp h1
    linarith [h2.1]
  · have h1 : |ε| < 1 - t := lt_of_lt_of_le hε (min_le_right _ _)
    have h2 := abs_lt.mp h1
    linarith [h2.2]
  · show u₁ + (t + ε) • (u₂ - u₁) = u₁ + t • (u₂ - u₁) + ε • (u₂ - u₁)
    rw [add_smul]
    abel
theorem Tri.edge_on_line (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    {x : Plane} {m : Fin 3}
    (hm : T.basis.coord m x = 0) (ho : ∀ j, j ≠ m → 0 < T.basis.coord j x)
    (hfx : f x = c) {w : Plane} (hw0 : w ≠ 0) (hfw : f w = 0)
    (hcross : cross (T.leftDir (m + 1)) w = 0) :
    f (T.pts (m + 1)) = c ∧ f (T.pts (m + 2)) = c ∧ f (T.pts m) ≠ c := by
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero (T.leftDir_ne_zero (m + 1)) hcross
  have hτne : τ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hτ
    exact hw0 hτ
  have hfdir : f (T.leftDir (m + 1)) = 0 := by
    have h1 : f w = τ * f (T.leftDir (m + 1)) := by rw [hτ, map_smul, smul_eq_mul]
    rw [hfw] at h1
    rcases mul_eq_zero.mp h1.symm with h | h
    · exact absurd h hτne
    · exact h
  have hidx : (m + 1) + 1 = m + 2 := by fin_cases m <;> rfl
  have hPQ : f (T.pts (m + 2)) = f (T.pts (m + 1)) := by
    rcases T.leftDir_eq_or (m + 1) with h | h
    · have h2 := hfdir
      rw [h, hidx, map_sub] at h2
      linarith
    · have h2 := hfdir
      rw [h, hidx, map_neg, map_sub] at h2
      linarith
  have hxe := T.mem_edge_of_coord_zero hm ho
  rw [Tri.edge, hidx] at hxe
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hxe
  have hfP : f (T.pts (m + 1)) = c := by
    have h1 : a * f (T.pts (m + 1)) + b * f (T.pts (m + 2)) = c := by
      rw [← hfx, ← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    rw [hPQ] at h1
    have h2 : (a + b) * f (T.pts (m + 1)) = c := by rw [add_mul]; linarith
    rw [hab, one_mul] at h2
    exact h2
  have hfQ : f (T.pts (m + 2)) = c := by rw [hPQ, hfP]
  refine ⟨hfP, hfQ, fun hfm => ?_⟩
  have hall : ∀ i, f (T.pts i) = c := by
    intro i
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    rcases h3 i m with rfl | rfl | rfl
    · exact hfm
    · exact hfP
    · exact hfQ
  exact two_vertices_on_line T f c hf hall
open Classical in
noncomputable def Dissection.lineChain {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e =>
    f ((D.tile e.1).pts e.2) = c ∧ f ((D.tile e.1).pts (e.2 + 1)) = c
      ∧ ∀ i, f ((D.tile e.1).pts i) ≤ c
theorem Dissection.mem_lineChain {N : ℕ} {D : Dissection N} {f : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    {e : Fin N × Fin 3} :
    e ∈ D.lineChain f c ↔
      f ((D.tile e.1).pts e.2) = c ∧ f ((D.tile e.1).pts (e.2 + 1)) = c
        ∧ ∀ i, f ((D.tile e.1).pts i) ≤ c := by
  classical
  simp [Dissection.lineChain]
theorem Dissection.lineChain_edge_subset {N : ℕ} (D : Dissection N)
    {f : Plane →ₗ[ℝ] ℝ} {c : ℝ} {e : Fin N × Fin 3} (he : e ∈ D.lineChain f c) :
    ∀ y ∈ (D.tile e.1).edge e.2, f y = c := by
  obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
  intro y hy
  rw [Tri.edge] at hy
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hy
  rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, h1, h2,
    ← add_mul, hab, one_mul]
theorem Dissection.wall_cover {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (hS : segment ℝ u₁ u₂ ⊆ {y | f y = c})
    (hint : openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u₁ u₂, ∀ i, y ∉ interior (D.tile i).carrier)
    {x : Plane} (hx : x ∈ openSegment ℝ u₁ u₂) (hxv : x ∉ D.vertexSet) :
    ∃ e ∈ D.lineChain f c, x ∈ (D.tile e.1).edge e.2 := by
  classical
  have hnv := D.notMem_vertexSet hxv
  have hxint : x ∈ interior D.target.carrier := hint hx
  have hxtar : x ∈ D.target.carrier := interior_subset hxint
  have hfx : f x = c := hS (openSegment_subset_segment ℝ u₁ u₂ hx)
  have hw0 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hfw : f (u₂ - u₁) = 0 := by
    have h1 : f u₁ = c := hS (left_mem_segment ℝ u₁ u₂)
    have h2 : f u₂ = c := hS (right_mem_segment ℝ u₁ u₂)
    rw [map_sub, h1, h2, sub_self]
  obtain ⟨j₀, hj₀⟩ : ∃ j, x ∈ (D.tile j).carrier := by
    have h1 := hxtar
    rw [← D.covers] at h1
    exact Set.mem_iUnion.mp h1
  rcases (D.tile j₀).classify (hnv j₀) with hpos | ⟨m₀, hm₀, ho₀⟩ | ⟨m₀, hneg⟩
  · obtain ⟨r, hr, hsub'⟩ := (D.tile j₀).ball_subset_of_pos hpos
    exact absurd (mem_interior.mpr ⟨Metric.ball x r, hsub', Metric.isOpen_ball,
      Metric.mem_ball_self hr⟩) (hwall x hx j₀)
  · 
    have hcr : cross ((D.tile j₀).leftDir (m₀ + 1)) (u₂ - u₁) = 0 := by
      by_contra hc
      obtain ⟨ε₀, hε₀, hmove⟩ := openSegment_two_sided hx
      rcases lt_or_gt_of_ne hc with hneg' | hpos'
      · have hpos'' : 0 < cross ((D.tile j₀).leftDir (m₀ + 1)) (-(u₂ - u₁)) := by
          rw [← neg_one_smul ℝ (u₂ - u₁), cross_smul_right]
          linarith
        obtain ⟨ε₁, hε₁, hpush⟩ := (D.tile j₀).mem_interior_of_cross_pos hm₀ ho₀ hpos''
        set ε := min ε₀ ε₁ / 2 with hεdef
        have hεpos : 0 < ε := by
          rw [hεdef]; have := lt_min hε₀ hε₁; linarith
        have hlt₁ : ε < ε₁ := by
          rw [hεdef]
          have h2 := min_le_right ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have hlt₀ : ε < ε₀ := by
          rw [hεdef]
          have h2 := min_le_left ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have h1 : x + ε • -(u₂ - u₁) ∈ interior (D.tile j₀).carrier := hpush ε hεpos hlt₁
        have h2 : x + ε • -(u₂ - u₁) ∈ openSegment ℝ u₁ u₂ := by
          have h3 : x + ε • -(u₂ - u₁) = x + (-ε) • (u₂ - u₁) := by
            rw [smul_neg, neg_smul]
          rw [h3]
          apply hmove
          rw [abs_neg, abs_of_pos hεpos]
          exact hlt₀
        exact absurd h1 (hwall _ h2 j₀)
      · obtain ⟨ε₁, hε₁, hpush⟩ := (D.tile j₀).mem_interior_of_cross_pos hm₀ ho₀ hpos'
        set ε := min ε₀ ε₁ / 2 with hεdef
        have hεpos : 0 < ε := by
          rw [hεdef]; have := lt_min hε₀ hε₁; linarith
        have hlt₁ : ε < ε₁ := by
          rw [hεdef]
          have h2 := min_le_right ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have hlt₀ : ε < ε₀ := by
          rw [hεdef]
          have h2 := min_le_left ε₀ ε₁
          have := lt_min hε₀ hε₁
          linarith
        have h1 : x + ε • (u₂ - u₁) ∈ interior (D.tile j₀).carrier := hpush ε hεpos hlt₁
        have h2 : x + ε • (u₂ - u₁) ∈ openSegment ℝ u₁ u₂ := by
          apply hmove
          rw [abs_of_pos hεpos]
          exact hlt₀
        exact absurd h1 (hwall _ h2 j₀)
    obtain ⟨hfP, hfQ, hfm⟩ := (D.tile j₀).edge_on_line f c hf hm₀ ho₀ hfx hw0 hfw hcr
    have hxe : x ∈ (D.tile j₀).edge (m₀ + 1) := (D.tile j₀).mem_edge_of_coord_zero hm₀ ho₀
    have hidx : ∀ m : Fin 3, (m + 1) + 1 = m + 2 := by decide
    have h3 : ∀ i m : Fin 3, i = m ∨ i = m + 1 ∨ i = m + 2 := by decide
    rcases lt_or_gt_of_ne hfm with hlt | hgt
    · refine ⟨(j₀, m₀ + 1), ?_, hxe⟩
      rw [Dissection.mem_lineChain]
      refine ⟨hfP, by rw [hidx m₀]; exact hfQ, ?_⟩
      intro i
      rcases h3 i m₀ with rfl | rfl | rfl
      · exact hlt.le
      · exact hfP.le
      · exact hfQ.le
    · 
      have hN := D.pos
      obtain ⟨R, hR, hRt'⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
      have hRt : Metric.ball x R ⊆ D.target.carrier := hRt'.trans interior_subset
      obtain ⟨j₁, hne, hOn⟩ := D.second_tile_at_edge_point hN hnv hR hRt ⟨m₀, hm₀, ho₀⟩
      obtain ⟨m₁, hm₁, ho₁⟩ := hOn
      obtain ⟨c₀, hc₀neg, hc₀⟩ := D.leftDir_antiparallel (Ne.symm hne) hm₀ ho₀ hm₁ ho₁
      have hcr₁ : cross ((D.tile j₁).leftDir (m₁ + 1)) (u₂ - u₁) = 0 := by
        rw [hc₀, cross_smul_left, hcr, mul_zero]
      obtain ⟨hfP₁, hfQ₁, hfm₁⟩ := (D.tile j₁).edge_on_line f c hf hm₁ ho₁ hfx hw0 hfw hcr₁
      have hxe₁ : x ∈ (D.tile j₁).edge (m₁ + 1) := (D.tile j₁).mem_edge_of_coord_zero hm₁ ho₁
      rcases lt_or_gt_of_ne hfm₁ with hlt₁ | hgt₁
      · refine ⟨(j₁, m₁ + 1), ?_, hxe₁⟩
        rw [Dissection.mem_lineChain]
        refine ⟨hfP₁, by rw [hidx m₁]; exact hfQ₁, ?_⟩
        intro i
        rcases h3 i m₁ with rfl | rfl | rfl
        · exact hlt₁.le
        · exact hfP₁.le
        · exact hfQ₁.le
      · 
        exfalso
        have hle₀ : ∀ y ∈ (D.tile j₀).carrier, (-f) y ≤ -c := by
          apply (D.tile j₀).carrier_subset_halfplane
          intro i
          simp only [LinearMap.neg_apply]
          rcases h3 i m₀ with rfl | rfl | rfl
          · linarith
          · linarith [hfP.le, hfP.ge]
          · linarith [hfQ.le, hfQ.ge]
        have hle₁ : ∀ y ∈ (D.tile j₁).carrier, (-f) y ≤ -c := by
          apply (D.tile j₁).carrier_subset_halfplane
          intro i
          simp only [LinearMap.neg_apply]
          rcases h3 i m₁ with rfl | rfl | rfl
          · linarith
          · linarith [hfP₁.le, hfP₁.ge]
          · linarith [hfQ₁.le, hfQ₁.ge]
        have hfx' : (-f) x = -c := by
          simp only [LinearMap.neg_apply, hfx]
        have hf' : (-f : Plane →ₗ[ℝ] ℝ) ≠ 0 := fun h => hf (neg_eq_zero.mp h)
        exact D.no_second_tile_same_side (Ne.symm hne) (-f) (-c) hf' hle₀ hle₁ hfx'
          hm₀ ho₀ hm₁ ho₁
  · rw [(D.tile j₀).carrier_eq_nonneg_coord] at hj₀
    exact absurd (hj₀ m₀) (not_le.mpr hneg)
theorem Dissection.wall_partition {N : ℕ} (D : Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) {u₁ u₂ : Plane} (hu : u₁ ≠ u₂)
    (hS : segment ℝ u₁ u₂ ⊆ {y | f y = c})
    (hint : openSegment ℝ u₁ u₂ ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ u₁ u₂, ∀ i, y ∉ interior (D.tile i).carrier) :
    ∑ e ∈ D.lineChain f c,
        (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane)
          ((D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂)
      = (MeasureTheory.Measure.hausdorffMeasure 1 : Measure Plane) (segment ℝ u₁ u₂) := by
  classical
  have hclseg : IsClosed (segment ℝ u₁ u₂) := by
    rw [segment_eq_image ℝ u₁ u₂]
    exact (isCompact_Icc.image (by fun_prop)).isClosed
  apply sum_hausdorff_of_partition (D.lineChain f c)
    (fun e => (D.tile e.1).edge e.2 ∩ segment ℝ u₁ u₂) (segment ℝ u₁ u₂)
    (D.vertexSet ∪ {u₁, u₂})
    (D.vertexSet_finite.union ((Set.finite_singleton u₂).insert u₁))
  · exact fun e _ => (((D.tile e.1).isClosed_edge e.2).inter hclseg).measurableSet
  · intro e₁ h₁ e₂ h₂ hne
    have hsub : ((D.tile e₁.1).edge e₁.2 ∩ segment ℝ u₁ u₂)
        ∩ ((D.tile e₂.1).edge e₂.2 ∩ segment ℝ u₁ u₂)
        ⊆ (D.tile e₁.1).edge e₁.2 ∩ (D.tile e₂.1).edge e₂.2 :=
      fun y hy => ⟨hy.1.1, hy.2.1⟩
    refine Set.Subsingleton.anti ?_ hsub
    obtain ⟨hP₁, hQ₁, hle₁⟩ := Dissection.mem_lineChain.mp h₁
    obtain ⟨hP₂, hQ₂, hle₂⟩ := Dissection.mem_lineChain.mp h₂
    exact D.sameside_edges_subsingleton f c hf hne
      ((D.tile e₁.1).carrier_subset_halfplane f c hle₁)
      ((D.tile e₂.1).carrier_subset_halfplane f c hle₂)
      (D.lineChain_edge_subset h₁) (D.lineChain_edge_subset h₂)
  · exact fun e _ => Set.inter_subset_right
  · intro y hy
    obtain ⟨hyS, hyF⟩ := hy
    rw [Set.mem_union, not_or] at hyF
    obtain ⟨hyv, hyends⟩ := hyF
    have hy1 : u₁ ≠ y := fun h => hyends (by rw [← h]; exact Set.mem_insert _ _)
    have hy2 : u₂ ≠ y := fun h => hyends (by rw [← h]; simp)
    have hyopen : y ∈ openSegment ℝ u₁ u₂ :=
      mem_openSegment_of_ne_left_right hy1 hy2 hyS
    obtain ⟨e, he, hye⟩ := D.wall_cover f c hf hu hS hint hwall hyopen hyv
    exact Set.mem_iUnion₂.mpr ⟨e, he, hye, hyS⟩
theorem Tri.edge_line (T : Tri) (k : Fin 3) :
    ∃ (f : Plane →ₗ[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ ∀ y ∈ T.edge k, f y = c := by
  have hne : T.pts (k + 1) - T.pts k ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h1 : k + 1 = k := T.indep.injective h
    have h2 : ∀ m : Fin 3, m + 1 ≠ m := by decide
    exact h2 k h1
  refine ⟨crossL (T.pts (k + 1) - T.pts k),
    cross (T.pts (k + 1) - T.pts k) (T.pts k), crossL_ne_zero hne, ?_⟩
  intro y hy
  rw [Tri.edge] at hy
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hy
  have hPP' : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1))
      = cross (T.pts (k + 1) - T.pts k) (T.pts k) := by
    have h1 : cross (T.pts (k + 1) - T.pts k) (T.pts (k + 1) - T.pts k) = 0 := cross_self _
    rw [cross_sub_right] at h1
    linarith
  rw [crossL_apply, ← hcomb, cross_add_right, cross_smul_right, cross_smul_right, hPP',
    ← add_mul, hab, one_mul]
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open EuclideanGeometry
theorem angle_of_sss {p q r p' q' r' : Plane}
    (hpq : dist p q = dist p' q') (hqr : dist q r = dist q' r') (hpr : dist p r = dist p' r')
    (hp : p ≠ q) (hr : r ≠ q) :
    EuclideanGeometry.angle (V := Plane) p q r = EuclideanGeometry.angle (V := Plane) p' q' r' := by
  have hd1 : (0:ℝ) < dist p q := dist_pos.mpr hp
  have hd2 : (0:ℝ) < dist r q := dist_pos.mpr hr
  have law1 := EuclideanGeometry.law_cos (V := Plane) p q r
  have law2 := EuclideanGeometry.law_cos (V := Plane) p' q' r'
  have hqr'' : dist r q = dist r' q' := by rw [dist_comm r q, dist_comm r' q']; exact hqr
  have hcos : Real.cos (EuclideanGeometry.angle (V := Plane) p q r)
      = Real.cos (EuclideanGeometry.angle (V := Plane) p' q' r') := by
    rw [← hpq, ← hqr'', ← hpr] at law2
    have h2d : (0:ℝ) < 2 * dist p q * dist r q := by positivity
    have hmul : 2 * dist p q * dist r q * Real.cos (EuclideanGeometry.angle (V := Plane) p q r)
        = 2 * dist p q * dist r q * Real.cos (EuclideanGeometry.angle (V := Plane) p' q' r') := by
      nlinarith [law1, law2]
    exact mul_left_cancel₀ (ne_of_gt h2d) hmul
  have hmem1 : EuclideanGeometry.angle (V := Plane) p q r ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  have hmem2 : EuclideanGeometry.angle (V := Plane) p' q' r' ∈ Set.Icc 0 Real.pi :=
    ⟨EuclideanGeometry.angle_nonneg _ _ _, EuclideanGeometry.angle_le_pi _ _ _⟩
  exact Real.injOn_cos hmem1 hmem2 hcos
theorem fin3_cases (a k : Fin 3) (h : a ≠ k) : a = k + 1 ∨ a = k + 2 := by
  fin_cases a <;> fin_cases k <;> simp_all <;> decide
theorem congruent_corner_angles {T U : Tri} (h : T.Congruent U) (j : Fin 3) :
    ∃ k : Fin 3, cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  obtain ⟨σ, hd⟩ := h.dist_eq
  set k := σ.symm j with hk
  have hσk : σ k = j := by rw [hk]; simp
  refine ⟨k, ?_⟩
  have h1 : σ (k + 1) ≠ j := by
    intro hh; have := σ.injective (hh.trans hσk.symm)
    simp at this
  have h2 : σ (k + 2) ≠ j := by
    intro hh; have := σ.injective (hh.trans hσk.symm)
    simp at this
  have hne12 : σ (k + 1) ≠ σ (k + 2) := by
    intro hh; have := σ.injective hh; simp at this
  have hUne1 : U.pts (j + 1) ≠ U.pts j := by
    intro hh
    have := U.indep.injective hh
    have hne : j + 1 ≠ j := by fin_cases j <;> decide
    exact hne this
  have hUne2 : U.pts (j + 2) ≠ U.pts j := by
    intro hh
    have := U.indep.injective hh
    have hne : j + 2 ≠ j := by fin_cases j <;> decide
    exact hne this
  rcases fin3_cases (σ (k+1)) j h1 with hc1 | hc1
  · 
    have hc2 : σ (k + 2) = j + 2 := by
      rcases fin3_cases (σ (k+2)) j h2 with hx | hx
      · exfalso; exact hne12 (by rw [hc1, hx])
      · exact hx
    have ptj : U.pts j = U.pts (σ k) := by rw [hσk]
    have pt1 : U.pts (j + 1) = U.pts (σ (k + 1)) := by rw [hc1]
    have pt2 : U.pts (j + 2) = U.pts (σ (k + 2)) := by rw [hc2]
    refine angle_of_sss ?_ ?_ ?_ hUne1 hUne2
    · rw [pt1, ptj]; exact (hd (k+1) k).symm
    · rw [ptj, pt2]; exact (hd k (k+2)).symm
    · rw [pt1, pt2]; exact (hd (k+1) (k+2)).symm
  · 
    have hc2 : σ (k + 2) = j + 1 := by
      rcases fin3_cases (σ (k+2)) j h2 with hx | hx
      · exact hx
      · exfalso; exact hne12 (by rw [hc1, hx])
    have hcomm : cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
        = cornerAngle (U.pts (j + 2)) (U.pts j) (U.pts (j + 1)) :=
      EuclideanGeometry.angle_comm (V := Plane) _ _ _
    rw [hcomm]
    have ptj : U.pts j = U.pts (σ k) := by rw [hσk]
    have pt1 : U.pts (j + 2) = U.pts (σ (k + 1)) := by rw [hc1]
    have pt2 : U.pts (j + 1) = U.pts (σ (k + 2)) := by rw [hc2]
    refine angle_of_sss ?_ ?_ ?_ hUne2 hUne1
    · rw [pt1, ptj]; exact (hd (k+1) k).symm
    · rw [ptj, pt2]; exact (hd k (k+2)).symm
    · rw [pt1, pt2]; exact (hd (k+1) (k+2)).symm
end Erdos634.Geometry
end

section
namespace Erdos634.PinPlumbing
open Erdos634.Geometry
theorem localAngle_cases (T : Tri) (p : Plane) :
    (∃ j : Fin 3, p = T.pts j ∧
        T.localAngle p = cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) ∨
    T.localAngle p = 2 * Real.pi ∨ T.localAngle p = Real.pi ∨ T.localAngle p = 0 := by
  classical
  by_cases h : ∃ j, p = T.pts j
  · left
    exact ⟨h.choose, h.choose_spec, by rw [Tri.localAngle, dif_pos h]⟩
  · by_cases h2 : ∀ j, 0 < T.basis.coord j p
    · right; left
      rw [Tri.localAngle, dif_neg h, if_pos h2]
    · by_cases h3 : ∃ k, T.basis.coord k p = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j p
      · right; right; left
        rw [Tri.localAngle, dif_neg h, if_neg h2, if_pos h3]
      · right; right; right
        rw [Tri.localAngle, dif_neg h, if_neg h2, if_neg h3]
end Erdos634.PinPlumbing
end

section
namespace Erdos634.BaseSelection
open Erdos634.Geometry
theorem tile_subset_target {N : ℕ} (D : Dissection N) (i : Fin N) :
    (D.tile i).carrier ⊆ D.target.carrier := by
  rw [← D.covers]
  exact Set.subset_iUnion (fun j => (D.tile j).carrier) i
theorem tile_interior_subset {N : ℕ} (D : Dissection N) (i : Fin N) :
    interior (D.tile i).carrier ⊆ interior D.target.carrier :=
  interior_mono (tile_subset_target D i)
theorem boundary_point_on_edge {N : ℕ} (D : Dissection N) {x : Plane}
    (hx : x ∈ frontier D.target.carrier)
    (hvert : ∀ i k, x ≠ (D.tile i).pts k) :
    ∃ i, Erdos634.Geometry.OnEdge D x i := by
  classical
  have hmem : x ∈ D.target.carrier := by
    have hcl : IsClosed D.target.carrier := by
      rw [Tri.carrier]
      exact (Set.finite_range D.target.pts).isClosed_convexHull (𝕜 := ℝ)
    rw [← hcl.closure_eq]; exact hx.1
  obtain ⟨S, ⟨i, rfl⟩, hxi⟩ : ∃ S ∈ Set.range (fun j => (D.tile j).carrier), x ∈ S := by
    have : x ∈ ⋃ j, (D.tile j).carrier := by rw [D.covers]; exact hmem
    simpa [Set.mem_iUnion] using this
  refine ⟨i, ?_⟩
  have hnonneg : ∀ k, 0 ≤ (D.tile i).basis.coord k x := by
    have hxi' : x ∈ (D.tile i).carrier := hxi
    rw [(D.tile i).carrier_eq_nonneg_coord] at hxi'
    exact hxi'
  have hnotint : ¬ (∀ k, 0 < (D.tile i).basis.coord k x) := by
    intro hpos
    obtain ⟨r, hr, hsub⟩ := (D.tile i).ball_subset_of_pos hpos
    have hint : x ∈ interior (D.tile i).carrier :=
      mem_interior.mpr ⟨Metric.ball x r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
    exact hx.2 (tile_interior_subset D i hint)
  rcases (D.tile i).classify (fun k => hvert i k) with h | h | h
  · exact absurd h hnotint
  · exact h
  · obtain ⟨k, hk⟩ := h
    exact absurd (hnonneg k) (not_le.mpr hk)
theorem coord_zero_mem_segment (T : Tri) (k : Fin 3) (x : Plane)
    (h0 : T.basis.coord k x = 0) (hnn : ∀ j, 0 ≤ T.basis.coord j x) :
    x ∈ segment ℝ (T.pts (k+1)) (T.pts (k+2)) := by
  have hx : x = (T.basis.coord 0 x) • T.pts 0 + (T.basis.coord 1 x) • T.pts 1
        + (T.basis.coord 2 x) • T.pts 2 := by
    have h := T.basis.affineCombination_coord_eq_self (k := ℝ) x
    rw [Finset.affineCombination_eq_linear_combination] at h
    · rw [Fin.sum_univ_three] at h; exact h.symm
    · exact T.basis.sum_coord_apply_eq_one x
  have hsum : T.basis.coord 0 x + T.basis.coord 1 x + T.basis.coord 2 x = 1 := by
    have := T.basis.sum_coord_apply_eq_one (k := ℝ) x
    rwa [Fin.sum_univ_three] at this
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · refine ⟨T.basis.coord 1 x, T.basis.coord 2 x, hnn 1, hnn 2, by linarith [h0, hsum], ?_⟩
    simp only [show ((0:Fin 3)+1) = 1 from rfl, show ((0:Fin 3)+2) = 2 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
  · refine ⟨T.basis.coord 2 x, T.basis.coord 0 x, hnn 2, hnn 0, by linarith [h0, hsum], ?_⟩
    simp only [show ((1:Fin 3)+1) = 2 from rfl, show ((1:Fin 3)+2) = 0 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
  · refine ⟨T.basis.coord 0 x, T.basis.coord 1 x, hnn 0, hnn 1, by linarith [h0, hsum], ?_⟩
    simp only [show ((2:Fin 3)+1) = 0 from rfl, show ((2:Fin 3)+2) = 1 from rfl]
    conv_rhs => rw [hx]
    rw [h0]; module
theorem frontier_subset_edges {N : ℕ} (D : Dissection N) {x : Plane}
    (hx : x ∈ frontier D.target.carrier) :
    ∃ i k, x ∈ (D.tile i).edge k := by
  classical
  by_cases hv : ∃ i k, x = (D.tile i).pts k
  · obtain ⟨i, k, rfl⟩ := hv
    exact ⟨i, k, by rw [Tri.edge]; exact left_mem_segment ℝ _ _⟩
  · push_neg at hv
    obtain ⟨i, k, h0, hpos⟩ := boundary_point_on_edge D hx (fun i k => hv i k)
    have hnn : ∀ j, 0 ≤ (D.tile i).basis.coord j x := by
      intro j
      by_cases hjk : j = k
      · exact hjk ▸ le_of_eq h0.symm
      · exact le_of_lt (hpos j hjk)
    refine ⟨i, k + 1, ?_⟩
    rw [Tri.edge, show k + 1 + 1 = k + 2 from by omega]
    exact coord_zero_mem_segment (D.tile i) k x h0 hnn
end Erdos634.BaseSelection
end

section
namespace Erdos634.SssCongruent
open Erdos634.Geometry RealInnerProductSpace
noncomputable def ev (T : Tri) : Fin 2 → Plane := ![T.pts 1 - T.pts 0, T.pts 2 - T.pts 0]
theorem ev_indep (T : Tri) : LinearIndependent ℝ (ev T) := by
  rw [ev, LinearIndependent.pair_iff]
  intro s t hst
  have haff := affineIndependent_iff.mp T.indep Finset.univ ![-s - t, s, t]
  have hw : ∑ i, (![-s - t, s, t] : Fin 3 → ℝ) i = 0 := by
    simp [Fin.sum_univ_three]; ring
  have hp : ∑ i, (![-s - t, s, t] : Fin 3 → ℝ) i • T.pts i = 0 := by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    have h : s • (T.pts 1 - T.pts 0) + t • (T.pts 2 - T.pts 0) = 0 := hst
    rw [smul_sub, smul_sub] at h
    rw [sub_smul, neg_smul]
    linear_combination (norm := module) h
  have hz := haff hw hp
  have h1 := hz 1 (Finset.mem_univ _)
  have h2 := hz 2 (Finset.mem_univ _)
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at h1 h2
  exact ⟨h1, h2⟩
noncomputable def evBasis (T : Tri) : Module.Basis (Fin 2) ℝ Plane :=
  basisOfLinearIndependentOfCardEqFinrank (ev_indep T) (by simp)
@[simp] theorem evBasis_apply (T : Tri) (i : Fin 2) : evBasis T i = ev T i := by
  simp [evBasis, coe_basisOfLinearIndependentOfCardEqFinrank]
theorem inner_ev_eq {T U : Tri} (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j))
    (i j : Fin 2) : ⟪ev T i, ev T j⟫ = ⟪ev U i, ev U j⟫ := by
  have hnorm : ∀ (V : Tri) (a b : Fin 3), ‖V.pts a - V.pts b‖ = dist (V.pts a) (V.pts b) :=
    fun V a b => (dist_eq_norm _ _).symm
  have key : ∀ (V : Tri) (a b : Fin 2),
      ⟪ev V a, ev V b⟫
        = (dist (V.pts a.succ) (V.pts 0) ^ 2 + dist (V.pts b.succ) (V.pts 0) ^ 2
            - dist (V.pts a.succ) (V.pts b.succ) ^ 2) / 2 := by
    intro V a b
    have hsub : ev V a - ev V b = V.pts a.succ - V.pts b.succ := by
      fin_cases a <;> fin_cases b <;> simp [ev] <;> abel
    have hpol : ⟪ev V a, ev V b⟫ = (‖ev V a‖ ^ 2 + ‖ev V b‖ ^ 2 - ‖ev V a - ev V b‖ ^ 2) / 2 := by
      rw [@norm_sub_sq_real]; ring
    rw [hpol, hsub]
    have hea : ev V a = V.pts a.succ - V.pts 0 := by fin_cases a <;> simp [ev]
    have heb : ev V b = V.pts b.succ - V.pts 0 := by fin_cases b <;> simp [ev]
    rw [hea, heb, hnorm, hnorm, hnorm]
  rw [key T, key U, hd, hd, hd]
noncomputable def evMap (T U : Tri) : Plane →ₗ[ℝ] Plane := (evBasis T).constr ℝ (ev U)
theorem evMap_basis (T U : Tri) (i : Fin 2) : evMap T U (ev T i) = ev U i := by
  rw [evMap, ← evBasis_apply T i, Module.Basis.constr_basis]
theorem expand (T : Tri) (x : Plane) :
    x = (evBasis T).repr x 0 • ev T 0 + (evBasis T).repr x 1 • ev T 1 := by
  conv_lhs => rw [← (evBasis T).sum_repr x]
  rw [Fin.sum_univ_two, evBasis_apply, evBasis_apply]
theorem evMap_expand (T U : Tri) (x : Plane) :
    evMap T U x = (evBasis T).repr x 0 • ev U 0 + (evBasis T).repr x 1 • ev U 1 := by
  conv_lhs => rw [expand T x]
  rw [map_add, map_smul, map_smul, evMap_basis, evMap_basis]
theorem evMap_inner {T U : Tri} (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j))
    (x y : Plane) : ⟪evMap T U x, evMap T U y⟫ = ⟪x, y⟫ := by
  conv_lhs => rw [evMap_expand, evMap_expand]
  conv_rhs => rw [expand T x, expand T y]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    ← inner_ev_eq hd]
noncomputable def evEquiv (T U : Tri) : Plane ≃ₗ[ℝ] Plane :=
  (evBasis T).equiv (evBasis U) (Equiv.refl (Fin 2))
theorem evEquiv_eq (T U : Tri) (x : Plane) : evEquiv T U x = evMap T U x := by
  have hb : ∀ i, (evEquiv T U).toLinearMap (evBasis T i) = evMap T U (evBasis T i) := by
    intro i
    show evEquiv T U (evBasis T i) = evMap T U (evBasis T i)
    rw [evEquiv, Module.Basis.equiv_apply]
    simp only [Equiv.refl_apply, evBasis_apply, evMap_basis]
  exact congrFun (congrArg DFunLike.coe ((evBasis T).ext hb)) x
noncomputable def evIso {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) : Plane ≃ₗᵢ[ℝ] Plane :=
  (evEquiv T U).isometryOfInner (by
    intro x y
    rw [evEquiv_eq, evEquiv_eq]
    exact evMap_inner hd x y)
@[simp] theorem evIso_apply {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) (x : Plane) :
    evIso hd x = evMap T U x := by
  rw [evIso, LinearEquiv.coe_isometryOfInner, evEquiv_eq]
noncomputable def sssIso {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) : Plane ≃ᵢ Plane :=
  ((IsometryEquiv.addRight (-T.pts 0)).trans (evIso hd).toIsometryEquiv).trans
    (IsometryEquiv.addRight (U.pts 0))
theorem sssIso_apply {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) (x : Plane) :
    sssIso hd x = evMap T U (x + -T.pts 0) + U.pts 0 := by
  show evIso hd (x + -T.pts 0) + U.pts 0 = _
  rw [evIso_apply]
theorem congruent_of_dist {T U : Tri}
    (hd : ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts i) (U.pts j)) : T.Congruent U := by
  refine ⟨sssIso hd, Equiv.refl _, ?_⟩
  have htri : ∀ y : Fin 3, y = 0 ∨ y = 1 ∨ y = 2 := by decide
  intro k
  show sssIso hd (T.pts k) = U.pts k
  rcases htri k with rfl | rfl | rfl
  · rw [sssIso_apply]
    have h0 : T.pts 0 + -T.pts 0 = (0 : Plane) := by abel
    rw [h0, map_zero, zero_add]
  · rw [sssIso_apply]
    have h1 : T.pts 1 + -T.pts 0 = ev T 0 := by simp [ev]; abel
    rw [h1, evMap_basis]
    show U.pts 1 - U.pts 0 + U.pts 0 = U.pts 1
    abel
  · rw [sssIso_apply]
    have h2 : T.pts 2 + -T.pts 0 = ev T 1 := by simp [ev]; abel
    rw [h2, evMap_basis]
    show U.pts 2 - U.pts 0 + U.pts 0 = U.pts 2
    abel
end Erdos634.SssCongruent
end

section
open scoped Classical
namespace Erdos634.Geometry
noncomputable def Tri.angleAt (T : Tri) (k : Fin 3) : ℝ :=
  cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
noncomputable def Tri.oppLen (T : Tri) (k : Fin 3) : ℝ := dist (T.pts (k + 1)) (T.pts (k + 2))
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
structure GridChar (R : Type*) [CommRing R] where
  L : AddSubgroup Real.Angle
  pi_mem : ((Real.pi : ℝ) : Real.Angle) ∈ L
  ψ : AddChar L R
  ψ_pi : ψ ⟨((Real.pi : ℝ) : Real.Angle), pi_mem⟩ = -1
  anchor : Real.Angle
namespace GridChar
variable {R : Type*} [CommRing R] (G : GridChar R)
end GridChar
def signChar {A : Type*} [AddCommGroup A] (χ : A →+ ZMod 2) : AddChar A ℝ where
  toFun x := if χ x = 0 then 1 else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro a b
    simp only [map_add]
    have hcase : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have h10 : (1 : ZMod 2) ≠ 0 := by decide
    rcases hcase (χ a) with h1 | h1 <;> rcases hcase (χ b) with h2 | h2 <;>
      simp [h1, h2, h11, h10]
theorem signChar_apply {A : Type*} [AddCommGroup A] (χ : A →+ ZMod 2) (x : A) :
    signChar χ x = if χ x = 0 then 1 else -1 := rfl
noncomputable def rangePre {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle) (x : φ.range) : A :=
  Classical.choose (AddMonoidHom.mem_range.mp x.2)
theorem rangePre_spec {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle) (x : φ.range) :
    φ (rangePre φ x) = x :=
  Classical.choose_spec (AddMonoidHom.mem_range.mp x.2)
noncomputable def rangeChar {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) : φ.range →+ ZMod 2 where
  toFun x := χ (rangePre φ x)
  map_zero' := by
    have h := rangePre_spec φ 0
    exact hker _ (by rw [h]; rfl)
  map_add' := by
    intro x y
    have hx := rangePre_spec φ x
    have hy := rangePre_spec φ y
    have hxy := rangePre_spec φ (x + y)
    have h0 : φ (rangePre φ (x + y) - rangePre φ x - rangePre φ y) = 0 := by
      rw [map_sub, map_sub, hxy, hx, hy, AddSubgroup.coe_add]
      abel
    have h1 := hker _ h0
    rw [map_sub, map_sub] at h1
    linear_combination h1
theorem rangeChar_apply {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a : A) :
    rangeChar φ χ hker ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ = χ a := by
  show χ (rangePre φ ⟨φ a, _⟩) = χ a
  have hs := rangePre_spec φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have h0 : φ (rangePre φ ⟨φ a, AddMonoidHom.mem_range.mpr ⟨a, rfl⟩⟩ - a) = 0 := by
    rw [map_sub, hs]; exact sub_self _
  have h1 := hker _ h0
  rw [map_sub] at h1
  linear_combination h1
noncomputable def GridChar.ofHom {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hχ : χ a₀ = 1) (anchor : Real.Angle) :
    GridChar ℝ where
  L := φ.range
  pi_mem := AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩
  ψ := signChar (rangeChar φ χ hker)
  ψ_pi := by
    have h := rangeChar_apply φ χ hker a₀
    have e : (⟨((Real.pi : ℝ) : Real.Angle), AddMonoidHom.mem_range.mpr ⟨a₀, hπ⟩⟩ : φ.range)
        = ⟨φ a₀, AddMonoidHom.mem_range.mpr ⟨a₀, rfl⟩⟩ := Subtype.ext hπ.symm
    rw [e, signChar_apply, h, hχ]
    simp
  anchor := anchor
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
noncomputable def rank2Map (θ : ℝ) : ℤ × ℤ →+ Real.Angle where
  toFun p := p.1 • ((Real.pi : ℝ) : Real.Angle) + p.2 • ((θ : ℝ) : Real.Angle)
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, add_zsmul]
    abel
theorem rank2Map_apply (θ : ℝ) (j k : ℤ) :
    rank2Map θ (j, k) = (((j : ℝ) * Real.pi + (k : ℝ) * θ : ℝ) : Real.Angle) := by
  show j • ((Real.pi : ℝ) : Real.Angle) + k • ((θ : ℝ) : Real.Angle) = _
  rw [Real.Angle.coe_add, ← Real.Angle.coe_zsmul, ← Real.Angle.coe_zsmul, zsmul_eq_mul,
    zsmul_eq_mul]
def rank2Par (b : ZMod 2) : ℤ × ℤ →+ ZMod 2 where
  toFun p := (p.1 : ZMod 2) + b * (p.2 : ZMod 2)
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring
theorem rank2_ker (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2) (p : ℤ × ℤ)
    (hp : rank2Map θ p = 0) : rank2Par b p = 0 := by
  obtain ⟨j, k⟩ := p
  rw [rank2Map_apply, Real.Angle.coe_eq_zero_iff] at hp
  obtain ⟨m, hm⟩ := hp
  rw [zsmul_eq_mul] at hm
  by_cases hk : k = 0
  · subst hk
    have h2 : ((j : ℝ) - 2 * m) * Real.pi = 0 := by
      push_cast at hm
      linear_combination (-1 : ℝ) * hm
    have h3 : (j : ℝ) - 2 * m = 0 := (mul_eq_zero.mp h2).resolve_right Real.pi_ne_zero
    have hj : j = 2 * m := by exact_mod_cast (sub_eq_zero.mp h3)
    show (j : ZMod 2) + b * ((0 : ℤ) : ZMod 2) = 0
    rw [hj]
    push_cast
    have h20 : (2 : ZMod 2) = 0 := by decide
    rw [h20]
    ring
  · exfalso
    apply hθ
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    have h1 : (k : ℝ) * θ = (2 * m - j) * Real.pi := by
      linear_combination (-1 : ℝ) * hm
    refine ⟨((2 * m - j : ℤ) : ℚ) / (k : ℚ), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hk']
    linear_combination h1
noncomputable def GridChar.rank2 (θ : ℝ) (hθ : ¬ ∃ r : ℚ, θ = (r : ℝ) * Real.pi) (b : ZMod 2)
    (anchor : Real.Angle) : GridChar ℝ :=
  GridChar.ofHom (rank2Map θ) (rank2Par b) (rank2_ker θ hθ b) (1, 0)
    (by rw [rank2Map_apply]; push_cast; rw [one_mul, zero_mul, add_zero])
    (by show ((1 : ℤ) : ZMod 2) + b * ((0 : ℤ) : ZMod 2) = 1; push_cast; ring)
    anchor
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
theorem theta_irr_of_alpha {α : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    ¬ ∃ r : ℚ, α / 2 + Real.pi / 2 = (r : ℝ) * Real.pi := by
  rintro ⟨r, hr⟩
  apply hα
  refine ⟨2 * r - 1, ?_⟩
  push_cast
  linear_combination 2 * hr
noncomputable def chiPlus (α : ℝ) (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) : GridChar ℝ :=
  GridChar.rank2 (α / 2 + Real.pi / 2) (theta_irr_of_alpha hα) 0 0
def Tri.ThreeAlphaData (T : Tri) (α β a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = β ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * α + β ∧ T.oppLen (σ 2) = c
end Erdos634.Geometry
end

section
namespace Erdos634.TilePlacement
open Erdos634.Geometry Finset
theorem range_pts_eq (T : Tri) (j : Fin 3) :
    Set.range T.pts = {T.pts (j + 1), T.pts j, T.pts (j + 2)} := by
  have hfin : ∀ a b : Fin 3, a = b ∨ a = b + 1 ∨ a = b + 2 := by decide
  have hfin' : ∀ i : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := fun i => hfin i j
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases hfin' i with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨j + 1, rfl⟩
    · exact ⟨j, rfl⟩
    · exact ⟨j + 2, rfl⟩
theorem strict_triangle (T : Tri) (j : Fin 3) :
    dist (T.pts (j + 1)) (T.pts (j + 2))
      < dist (T.pts (j + 1)) (T.pts j) + dist (T.pts j) (T.pts (j + 2)) := by
  rcases lt_or_eq_of_le (dist_triangle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exact h
  · exfalso
    have hw : Wbtw ℝ (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) :=
      dist_add_dist_eq_iff.mp h.symm
    have hcol : Collinear ℝ (Set.range T.pts) := by
      rw [range_pts_eq T j]; exact hw.collinear
    exact (affineIndependent_iff_not_collinear.mp T.indep) hcol
theorem strict_triangle_pts (T : Tri) (j : Fin 3) :
    dist (T.pts j) (T.pts (j + 1))
      < dist (T.pts (j + 1)) (T.pts (j + 2)) + dist (T.pts j) (T.pts (j + 2)) := by
  have hsh1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
  have hsh2 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
  have h := strict_triangle T (j + 2)
  rw [hsh1 j, hsh2 j] at h
  have e1 : dist (T.pts j) (T.pts (j + 2)) = dist (T.pts (j + 2)) (T.pts j) := dist_comm _ _
  have e2 : dist (T.pts (j + 1)) (T.pts (j + 2)) = dist (T.pts (j + 2)) (T.pts (j + 1)) :=
    dist_comm _ _
  rw [e1, e2]
  have e3 : dist (T.pts (j + 2)) (T.pts (j + 1)) = dist (T.pts (j + 1)) (T.pts (j + 2)) :=
    dist_comm _ _
  linarith [h]
end Erdos634.TilePlacement
end

section
namespace Erdos634.MarchFlank
open Erdos634.Geometry Erdos634.TilePlacement
theorem cornerAngle_pos (T : Tri) (j : Fin 3) :
    0 < cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) := by
  rcases eq_or_lt_of_le (EuclideanGeometry.angle_nonneg
    (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exfalso
    have hz : cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) = 0 := h.symm
    rw [Erdos634.Geometry.cornerAngle] at hz
    have hdeg := EuclideanGeometry.dist_eq_abs_sub_dist_of_angle_eq_zero hz
    have hstrict := strict_triangle_pts T j
    rcases abs_cases (dist (T.pts (j + 1)) (T.pts j) - dist (T.pts (j + 2)) (T.pts j)) with
      ⟨he, _⟩ | ⟨he, _⟩
    · rw [he, dist_comm (T.pts (j + 1)) (T.pts j),
        dist_comm (T.pts (j + 2)) (T.pts j)] at hdeg
      linarith
    · 
      have h2 := strict_triangle_pts T (j + 2)
      have e1 : ∀ x : Fin 3, x + 2 + 1 = x := by decide
      have e2 : ∀ x : Fin 3, x + 2 + 2 = x + 1 := by decide
      rw [e1, e2] at h2
      rw [he, dist_comm (T.pts (j + 1)) (T.pts j),
        dist_comm (T.pts (j + 2)) (T.pts j)] at hdeg
      rw [dist_comm (T.pts (j + 2)) (T.pts j),
        dist_comm (T.pts (j + 2)) (T.pts (j + 1))] at h2
      linarith
  · exact h
private theorem third_index : ∀ j k : Fin 3, j ≠ k → ∃ m, m ≠ j ∧ m ≠ k := by decide
private theorem index_trichotomy :
    ∀ i j k m : Fin 3, j ≠ k → m ≠ j → m ≠ k → i ≠ m → i = j ∨ i = k := by decide
theorem localAngle_ne_zero_of_mem (T : Tri) {p : Plane} (hp : p ∈ T.carrier) :
    T.localAngle p ≠ 0 := by
  classical
  have hnn : ∀ i, 0 ≤ T.basis.coord i p := by
    rw [T.carrier_eq_nonneg_coord] at hp; exact hp
  rw [Tri.localAngle]
  split
  · exact ne_of_gt (cornerAngle_pos T _)
  · rename_i hv
    split
    · positivity
    · rename_i hpos
      push_neg at hpos
      obtain ⟨k, hk⟩ := hpos
      have hk0 : T.basis.coord k p = 0 := le_antisymm hk (hnn k)
      have huniq : ∀ j, j ≠ k → 0 < T.basis.coord j p := by
        intro j hj
        rcases lt_or_eq_of_le (hnn j) with h | h
        · exact h
        · exfalso
          have hsum := T.basis.sum_coord_apply_eq_one (k := ℝ) p
          obtain ⟨m, hmj, hmk⟩ := third_index j k hj
          have hm1 : T.basis.coord m p = 1 := by
            rw [Fin.sum_univ_three] at hsum
            fin_cases j <;> fin_cases k <;> fin_cases m <;> simp_all <;> linarith
          have hpm : p = T.pts m := by
            refine T.basis.ext_elem fun i => ?_
            have hci : T.basis.coord i (T.pts m) = if i = m then 1 else 0 :=
              AffineBasis.coord_apply T.basis i m
            rw [hci]
            by_cases him : i = m
            · subst him; simp [hm1]
            · have hz : T.basis.coord i p = 0 := by
                rcases index_trichotomy i j k m hj hmj hmk him with h' | h'
                · rw [h', ← h]
                · rw [h', hk0]
              simp [him, hz]
          exact hv ⟨m, hpm⟩
      split
      · exact Real.pi_ne_zero
      · rename_i hedge
        exact absurd ⟨k, hk0, huniq⟩ hedge
end Erdos634.MarchFlank
end

section
open scoped Classical
namespace Erdos634.Geometry
open Real
variable {N : ℕ}
theorem Row2.fin3_rot : ∀ a b c : Fin 3, b ≠ a → c ≠ a → b ≠ c →
    (b = a + 1 ∧ c = a + 2) ∨ (b = a + 2 ∧ c = a + 1) := by decide
theorem Row2.perm_succ (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (σ (k + 1) = σ k + 1 ∧ σ (k + 2) = σ k + 2) ∨ (σ (k + 1) = σ k + 2 ∧ σ (k + 2) = σ k + 1) := by
  have h1 : k + 1 ≠ k := by
    have : ∀ a : Fin 3, a + 1 ≠ a := by decide
    exact this k
  have h2 : k + 2 ≠ k := by
    have : ∀ a : Fin 3, a + 2 ≠ a := by decide
    exact this k
  have h12 : k + 1 ≠ k + 2 := by
    have : ∀ a : Fin 3, a + 1 ≠ a + 2 := by decide
    exact this k
  exact Row2.fin3_rot _ _ _ (fun h => h1 (σ.injective h)) (fun h => h2 (σ.injective h))
    (fun h => h12 (σ.injective h))
theorem Row2.angleAt_comp (T U : Tri) (σ : Equiv.Perm (Fin 3)) (hU : ∀ k, U.pts k = T.pts (σ k))
    (k : Fin 3) : U.angleAt k = T.angleAt (σ k) ∧ U.oppLen k = T.oppLen (σ k) := by
  unfold Tri.angleAt Tri.oppLen
  simp only [hU]
  rcases Row2.perm_succ σ k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact ⟨rfl, rfl⟩
  · rw [h1, h2]; exact ⟨EuclideanGeometry.angle_comm _ _ _, dist_comm _ _⟩
end Erdos634.Geometry
end

section
namespace TriangleTiling
open EuclideanGeometry
section Geometry
variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]
theorem dist_lt_dist_add_dist_of_not_collinear {A B C : P}
    (h : ¬ Collinear ℝ ({A, B, C} : Set P)) : dist A C < dist A B + dist B C := by
  rcases (dist_triangle A B C).lt_or_eq with h' | h'
  · exact h'
  · exact absurd (dist_add_dist_eq_iff.mp h'.symm).collinear h
end Geometry
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry MeasureTheory
theorem strict_triangle_ineqs {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P] {A B C : P} (h : AffineIndependent ℝ ![A, B, C]) :
    dist B C < dist C A + dist A B ∧ dist C A < dist A B + dist B C ∧
      dist A B < dist B C + dist C A := by
  have hcol := affineIndependent_iff_not_collinear_set.mp h
  have t1 := dist_lt_dist_add_dist_of_not_collinear hcol
  have t2 := dist_lt_dist_add_dist_of_not_collinear (A := B) (B := A) (C := C)
    (by rwa [Set.insert_comm])
  have t3 := dist_lt_dist_add_dist_of_not_collinear (A := A) (B := C) (C := B)
    (by rwa [Set.pair_comm])
  rw [dist_comm A C] at t1
  rw [dist_comm B A, dist_comm A C] at t2
  rw [dist_comm A C, dist_comm C B] at t3
  exact ⟨by linarith, t1, by linarith⟩
theorem tri_indep (T : Tri) : AffineIndependent ℝ ![T.pts 0, T.pts 1, T.pts 2] := by
  convert T.indep using 1
  ext i; fin_cases i <;> rfl
noncomputable def heron16 (a b c : ℝ) : ℝ :=
  2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2 - a ^ 4 - b ^ 4 - c ^ 4
theorem dist_sq_plane (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
theorem four_detTri_sq (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2 =
      heron16 (dist (T.pts 1) (T.pts 2)) (dist (T.pts 2) (T.pts 0)) (dist (T.pts 0) (T.pts 1)) := by
  rw [Erdos634.AreaDet.detTri_eq, heron16]
  have e0 := dist_sq_plane (T.pts 1) (T.pts 2)
  have e1 := dist_sq_plane (T.pts 2) (T.pts 0)
  have e2 := dist_sq_plane (T.pts 0) (T.pts 1)
  have q : ∀ x : ℝ, x ^ 4 = (x ^ 2) ^ 2 := fun x => by ring
  simp only [q, e0, e1, e2]
  simp only [PiLp.sub_apply]
  ring
theorem area_heron {N : ℕ} (D : CongruentDissection N) :
    (N : ℝ) ^ 2 * heron16 (dist (D.model.pts 1) (D.model.pts 2))
        (dist (D.model.pts 2) (D.model.pts 0)) (dist (D.model.pts 0) (D.model.pts 1)) =
      heron16 (dist (D.target.pts 1) (D.target.pts 2))
        (dist (D.target.pts 2) (D.target.pts 0)) (dist (D.target.pts 0) (D.target.pts 1)) := by
  have hv := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.volume_eq_det_mul] at hv
  have hM := D.model.volume_pos
  rw [Erdos634.AreaDet.volume_eq_det_mul] at hM
  have hc0 : volume Erdos634.AreaDet.stdCarrier ≠ 0 := by
    intro h; rw [h, mul_zero] at hM; exact lt_irrefl _ hM
  have hct : volume Erdos634.AreaDet.stdCarrier ≠ ⊤ :=
    (Erdos634.AreaDet.isCompact_stdCarrier.measure_lt_top).ne
  rw [← mul_assoc] at hv
  have h2 := (ENNReal.mul_left_inj hc0 hct).1 hv
  have h3 : ENNReal.ofReal |Erdos634.AreaDet.detTri D.target| =
      ENNReal.ofReal ((N : ℝ) * |Erdos634.AreaDet.detTri D.model|) := by
    rw [h2, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
  have h4 := (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by positivity)).1 h3
  rw [← four_detTri_sq, ← four_detTri_sq]
  have : Erdos634.AreaDet.detTri D.target ^ 2 =
      ((N : ℝ) * |Erdos634.AreaDet.detTri D.model|) ^ 2 := by
    rw [← h4, sq_abs]
  rw [this, mul_pow, sq_abs]; ring
end TriangleTiling
end

section
namespace TriangleTiling
open Polynomial Real
theorem totient_le_four {n : ℕ} (hn : 0 < n) (h : Nat.totient n ≤ 4) :
    n ∈ ({1, 2, 3, 4, 5, 6, 8, 10, 12} : Finset ℕ) := by
  have hpos : 0 < Nat.totient n := Nat.totient_pos.mpr hn
  have hdvd : ∀ d, d ∣ n → Nat.totient d ≤ 4 := fun d hd =>
    (Nat.le_of_dvd hpos (Nat.totient_dvd_of_dvd hd)).trans h
  have h120 : n ∣ 120 := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases k with _ | k
    · simp
    have hb := hdvd _ hpk
    rw [Nat.totient_prime_pow hp (Nat.succ_pos k), Nat.succ_sub_one] at hb
    have hp2 := hp.two_le
    have hpk1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
    have hp5 : p ≤ 5 := by
      have := le_trans (Nat.le_mul_of_pos_left (p - 1) hpk1) hb
      omega
    interval_cases p
    · have hk : k ≤ 2 := by
        by_contra hk
        push Not at hk
        have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
        omega
      interval_cases k <;> norm_num
    · have hk : k = 0 := by
        by_contra hk
        have : 3 ≤ 3 ^ k := by
          calc 3 = 3 ^ 1 := by norm_num
            _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hk)
        omega
      subst hk; norm_num
    · exact absurd hp (by decide)
    · have hk : k = 0 := by
        by_contra hk
        have : 5 ≤ 5 ^ k := by
          calc 5 = 5 ^ 1 := by norm_num
            _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hk)
        omega
      subst hk; norm_num
  have hmem : n ∈ Nat.divisors 120 := Nat.mem_divisors.mpr ⟨h120, by norm_num⟩
  rw [show Nat.divisors 120 = {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120} by
    decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> first | decide | (exfalso; revert h; decide)
theorem cos_mul_zeta (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) * (2 * Complex.exp (θ * Complex.I)) =
      Complex.exp (θ * Complex.I) ^ 2 + 1 := by
  have hE : Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [Complex.ofReal_cos, Complex.cos]
  calc (Complex.exp (↑θ * Complex.I) + Complex.exp (-↑θ * Complex.I)) / 2 *
        (2 * Complex.exp (↑θ * Complex.I))
      = Complex.exp (↑θ * Complex.I) ^ 2 +
          Complex.exp (-↑θ * Complex.I) * Complex.exp (↑θ * Complex.I) := by ring
    _ = _ := by rw [hE]
theorem aeval_quadratic {S : Type*} [CommRing S] [Algebra ℚ S] {P : ℚ[X]} (hdeg : P.natDegree ≤ 2)
    (x : S) : aeval x P = algebraMap ℚ S (P.coeff 0) + algebraMap ℚ S (P.coeff 1) * x +
      algebraMap ℚ S (P.coeff 2) * x ^ 2 := by
  rw [aeval_eq_sum_range' (n := 3) (by omega), Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [Algebra.smul_def, pow_zero, mul_one, pow_one]
theorem euler {m n : ℕ} (hn : 0 < n) (hmn : m.Coprime n) {P : ℚ[X]} (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ 2) (hroot : aeval (Real.cos (2 * π * m / n)) P = 0) :
    n ∈ ({1, 2, 3, 4, 5, 6, 8, 10, 12} : Finset ℕ) := by
  apply totient_le_four hn
  set θ : ℝ := 2 * π * m / n
  set ζ : ℂ := Complex.exp (θ * Complex.I)
  have hprim : IsPrimitiveRoot ζ n := by
    have := Complex.isPrimitiveRoot_exp_of_coprime m n hn.ne' hmn
    convert this using 2
    simp only [θ]
    push_cast
    ring
  set p0 := P.coeff 0
  set p1 := P.coeff 1
  set p2 := P.coeff 2
  set Q : ℚ[X] := C p2 * X ^ 4 + C (2 * p1) * X ^ 3 + C (4 * p0 + 2 * p2) * X ^ 2 +
    C (2 * p1) * X + C p2
  have hQ0 : Q ≠ 0 := by
    intro hQ
    have c4 := congrArg (coeff · 4) hQ
    have c3 := congrArg (coeff · 3) hQ
    have c2 := congrArg (coeff · 2) hQ
    simp only [Q, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at c4 c3 c2
    norm_num at c4 c3 c2
    apply hP
    ext i
    rcases Nat.lt_or_ge i 3 with hi | hi
    · interval_cases i
      · simp only [coeff_zero]; linarith
      · simp only [coeff_zero]; exact c3
      · simp only [coeff_zero]; exact c4
    · simp only [coeff_zero]; exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hQdeg : Q.natDegree ≤ 4 := by
    simp only [Q]
    compute_degree
  have hc := cos_mul_zeta θ
  have hPc := hroot
  rw [aeval_quadratic hdeg] at hPc
  have hPc' : ((p0 : ℝ) : ℂ) + (p1 : ℂ) * (Real.cos θ : ℂ) + (p2 : ℂ) * (Real.cos θ : ℂ) ^ 2 = 0 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hPc
    simp only [eq_ratCast, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ratCast, Complex.ofReal_zero] at this
    simpa using this
  have hQζ : aeval ζ Q = 0 := by
    simp only [Q, map_add, map_mul, aeval_C, aeval_X, map_pow, eq_ratCast]
    push_cast
    linear_combination (4 * ζ ^ 2) * hPc' - (2 * (p1 : ℂ) * ζ +
      (p2 : ℂ) * (2 * (Real.cos θ : ℂ) * ζ + ζ ^ 2 + 1)) * hc
  have hdvd := minpoly.dvd ℚ ζ hQζ
  rw [← cyclotomic_eq_minpoly_rat hprim hn] at hdvd
  have := natDegree_le_of_dvd hdvd hQ0
  rw [natDegree_cyclotomic] at this
  omega
theorem sin_mod (m n : ℕ) (hn : 0 < n) :
    Real.sin (2 * π * m / n) = Real.sin (2 * π * (m % n : ℕ) / n) := by
  have hm : (m : ℝ) = (m % n : ℕ) + n * (m / n : ℕ) := by exact_mod_cast (Nat.mod_add_div m n).symm
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc Real.sin (2 * π * m / n)
      = Real.sin (2 * π * (m % n : ℕ) / n + (m / n : ℕ) * (2 * π)) := by
        congr 1; rw [hm]; field_simp
    _ = _ := Real.sin_add_nat_mul_two_pi _ _
theorem coprime_mod {m n : ℕ} (h : m.Coprime n) : (m % n).Coprime n := by
  unfold Nat.Coprime at h ⊢
  rw [← Nat.gcd_rec n m, Nat.gcd_comm]; exact h
theorem euler_sin {m n : ℕ} (hn : 0 < n) (hmn : m.Coprime n) {P R : ℚ[X]} (hP : P ≠ 0)
    (hdeg : P.natDegree ≤ 2) (hroot : aeval (Real.cos (2 * π * m / n)) P = 0) (hR : R ≠ 0)
    (hRdeg : R.natDegree ≤ 2) (hRroot : aeval (Real.sin (2 * π * m / n)) R = 0) :
    n ∈ ({1, 2, 3, 4, 6, 8, 12} : Finset ℕ) := by
  have h1 := euler hn hmn hP hdeg hroot
  have key : ∀ k : ℕ, k.Coprime 20 →
      Real.sin (2 * π * m / n) = Real.cos (2 * π * k / ((20 : ℕ) : ℝ)) → False := by
    intro k hk he
    rw [he] at hRroot
    have := euler (by norm_num) hk hR hRdeg hRroot
    revert this; decide
  have hred := sin_mod m n hn
  have hcop := coprime_mod hmn
  have hlt : m % n < n := Nat.mod_lt _ hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 ⊢
  rcases h1 with h | h | h | h | h | h | h | h | h <;> subst h <;> (try simp)
  · 
    set r := m % 5
    interval_cases r
    · exact absurd hcop (by decide)
    · exact (key 1 (by decide) (by rw [hred, ← Real.cos_pi_div_two_sub]; congr 1; push_cast; ring))
    · exact (key 3 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
    · exact (key 7 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
    · exact (key 11 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
  · 
    set r := m % 10
    interval_cases r
    all_goals first
      | exact absurd hcop (by decide)
      | skip
    · exact (key 3 (by decide) (by rw [hred, ← Real.cos_pi_div_two_sub]; congr 1; push_cast; ring))
    · exact (key 1 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
    · exact (key 9 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
    · exact (key 13 (by decide) (by
        rw [hred, ← Real.cos_pi_div_two_sub, ← Real.cos_neg]; congr 1; push_cast; ring))
end TriangleTiling
end

section
namespace TriangleTiling
open Set
variable {ι : Type*}
theorem exists_bound_left (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {m₀ : ℝ} (hm₀ : m₀ < x)
    (h : ∀ k ∈ s, lo k < x → hi k < x) :
    ∃ m, m < x ∧ m₀ ≤ m ∧ ∀ k ∈ s, lo k < x → hi k ≤ m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨m₀, hm₀, le_rfl, fun k hk => absurd hk (Finset.notMem_empty k)⟩
  | insert j s hj ih =>
    obtain ⟨m, hmx, hm0, hm⟩ := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
    by_cases hjx : lo j < x
    · have hj' := h j (Finset.mem_insert_self j s) hjx
      refine ⟨max m (hi j), max_lt hmx hj', le_trans hm0 (le_max_left _ _), ?_⟩
      intro k hk hkx
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact le_max_right _ _
      · exact le_trans (hm k hk hkx) (le_max_left _ _)
    · refine ⟨m, hmx, hm0, ?_⟩
      intro k hk hkx
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact absurd hkx hjx
      · exact hm k hk hkx
theorem exists_bound_right (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {m₀ : ℝ} (hm₀ : x < m₀)
    (h : ∀ k ∈ s, x < hi k → x < lo k) :
    ∃ m, x < m ∧ m ≤ m₀ ∧ ∀ k ∈ s, x < hi k → m ≤ lo k := by
  obtain ⟨m, hmx, hm0, hm⟩ := exists_bound_left s (fun k => -hi k) (fun k => -lo k) (-x)
    (m₀ := -m₀) (by linarith) (fun k hk hkx => by have := h k hk (by linarith); linarith)
  exact ⟨-m, by linarith, by linarith, fun k hk hkx => by have := hm k hk (by linarith); linarith⟩
theorem exists_interval_left (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {E : Set ℝ} (hE : E.Finite)
    (hcov : ∀ y ∈ Ioo (x - δ₀) x, y ∉ E → ∃ k ∈ s, y ∈ Icc (lo k) (hi k)) :
    ∃ k ∈ s, lo k < x ∧ x ≤ hi k := by
  by_contra hno
  push Not at hno
  obtain ⟨m, hmx, hm0, hm⟩ := exists_bound_left s lo hi x (m₀ := x - δ₀) (by linarith) hno
  obtain ⟨y, hy, hyE⟩ := ((Set.Ioo_infinite hmx).diff hE).nonempty
  obtain ⟨k, hk, hyk⟩ := hcov y ⟨by linarith [hy.1], hy.2⟩ hyE
  have := hm k hk (lt_of_le_of_lt hyk.1 hy.2)
  linarith [hy.1, hyk.2]
theorem exists_interval_right (s : Finset ι) (lo hi : ι → ℝ) (x : ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    {E : Set ℝ} (hE : E.Finite)
    (hcov : ∀ y ∈ Ioo x (x + δ₀), y ∉ E → ∃ k ∈ s, y ∈ Icc (lo k) (hi k)) :
    ∃ k ∈ s, lo k ≤ x ∧ x < hi k := by
  by_contra hno
  push Not at hno
  obtain ⟨m, hmx, hm0, hm⟩ := exists_bound_right s lo hi x (m₀ := x + δ₀) (by linarith)
    (fun k hk hkx => by by_contra h; push Not at h; exact absurd (hno k hk h) (not_le.mpr hkx))
  obtain ⟨y, hy, hyE⟩ := ((Set.Ioo_infinite hmx).diff hE).nonempty
  obtain ⟨k, hk, hyk⟩ := hcov y ⟨hy.1, by linarith [hy.2]⟩ hyE
  have := hm k hk (lt_of_lt_of_le hy.1 hyk.2)
  linarith [hy.2, hyk.1]
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry MeasureTheory Set
theorem eq_lineMap_of_level {f : Plane →ₗ[ℝ] ℝ} (hf : f ≠ 0) {c : ℝ} {P Q y : Plane}
    (hPQ : P ≠ Q) (hP : f P = c) (hQ : f Q = c) (hy : f y = c) :
    ∃ t : ℝ, y = AffineMap.lineMap P Q t := by
  have hn := rotVec_ne_zero hf
  have hu : cross (rotVec f) (Q - P) = 0 := by rw [← rotVec_spec, map_sub, hP, hQ, sub_self]
  have hv : cross (rotVec f) (y - P) = 0 := by rw [← rotVec_spec, map_sub, hP, hy, sub_self]
  have hcr := cross_eq_zero_of_common_ker hn hu hv
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero (sub_ne_zero.mpr hPQ.symm) hcr
  refine ⟨τ, ?_⟩
  rw [AffineMap.lineMap_apply_module', ← hτ]
  abel
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
open Classical in
noncomputable def lineParam (Q W y : Plane) : ℝ :=
  if h : ∃ t : ℝ, y = AffineMap.lineMap Q W t then h.choose else 0
theorem lineMap_lineParam {Q W y : Plane} (h : ∃ t : ℝ, y = AffineMap.lineMap Q W t) :
    AffineMap.lineMap Q W (lineParam Q W y) = y := by
  classical
  rw [lineParam, dif_pos h]
  exact h.choose_spec.symm
theorem lineParam_lineMap {Q W : Plane} (hQW : Q ≠ W) (t : ℝ) :
    lineParam Q W (AffineMap.lineMap Q W t) = t :=
  AffineMap.lineMap_injective ℝ hQW (lineMap_lineParam ⟨t, rfl⟩)
noncomputable def edgeLo (Q W : Plane) (T : Tri) (k : Fin 3) : ℝ :=
  min (lineParam Q W (T.pts k)) (lineParam Q W (T.pts (k + 1)))
noncomputable def edgeHi (Q W : Plane) (T : Tri) (k : Fin 3) : ℝ :=
  max (lineParam Q W (T.pts k)) (lineParam Q W (T.pts (k + 1)))
section Line
variable {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {Q W : Plane}
theorem eq_lineMap_lineParam (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {y : Plane} (hy : g y = c) : AffineMap.lineMap Q W (lineParam Q W y) = y :=
  lineMap_lineParam (eq_lineMap_of_level hg hQW hQ hW hy)
theorem level_lineMap (hQ : g Q = c) (hW : g W = c) (t : ℝ) :
    g (AffineMap.lineMap Q W t) = c := by
  rw [AffineMap.lineMap_apply_module, map_add, map_smul, map_smul, hQ, hW, smul_eq_mul,
    smul_eq_mul]
  ring
theorem edge_eq_image (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) (T : Tri)
    (k : Fin 3) (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) :
    T.edge k = AffineMap.lineMap Q W '' Icc (edgeLo Q W T k) (edgeHi Q W T k) := by
  rw [edgeLo, edgeHi, ← segment_eq_Icc', image_segment, eq_lineMap_lineParam hg hQW hQ hW h1,
    eq_lineMap_lineParam hg hQW hQ hW h2]
  rfl
theorem lineMap_mem_edge_iff (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    (T : Tri) (k : Fin 3) (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) (t : ℝ) :
    AffineMap.lineMap Q W t ∈ T.edge k ↔ t ∈ Icc (edgeLo Q W T k) (edgeHi Q W T k) := by
  rw [edge_eq_image hg hQW hQ hW T k h1 h2]
  exact (AffineMap.lineMap_injective ℝ hQW).mem_set_image
theorem edgeLo_lt_edgeHi (T : Tri) (k : Fin 3)
    (h1 : ∃ t : ℝ, T.pts k = AffineMap.lineMap Q W t)
    (h2 : ∃ t : ℝ, T.pts (k + 1) = AffineMap.lineMap Q W t) :
    edgeLo Q W T k < edgeHi Q W T k := by
  rw [edgeLo, edgeHi]
  have hne : lineParam Q W (T.pts k) ≠ lineParam Q W (T.pts (k + 1)) := by
    intro h
    have hk : T.pts k = T.pts (k + 1) := by
      rw [← lineMap_lineParam h1, ← lineMap_lineParam h2, h]
    have := T.indep.injective hk
    have hne : ∀ m : Fin 3, m ≠ m + 1 := by decide
    exact hne k this
  rcases lt_or_gt_of_ne hne with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]; exact h
  · rw [min_eq_right h.le, max_eq_left h.le]; exact h
theorem lineMap_mem_openSegment_iff (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    (T : Tri) (k : Fin 3) (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) (t : ℝ) :
    AffineMap.lineMap Q W t ∈ openSegment ℝ (T.pts k) (T.pts (k + 1)) ↔
      t ∈ Ioo (edgeLo Q W T k) (edgeHi Q W T k) := by
  have hlt := edgeLo_lt_edgeHi T k (eq_lineMap_of_level hg hQW hQ hW h1)
    (eq_lineMap_of_level hg hQW hQ hW h2)
  have hab : lineParam Q W (T.pts k) ≠ lineParam Q W (T.pts (k + 1)) := by
    intro h
    rw [edgeLo, edgeHi, h, min_self, max_self] at hlt
    exact lt_irrefl _ hlt
  have e1 := (eq_lineMap_lineParam hg hQW hQ hW h1).symm
  have e2 := (eq_lineMap_lineParam hg hQW hQ hW h2).symm
  rw [e1, e2, ← image_openSegment, openSegment_eq_Ioo' hab,
    (AffineMap.lineMap_injective ℝ hQW).mem_set_image]
  rfl
end Line
section Chain
variable {N : ℕ} (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {Q W : Plane}
theorem lineChain_ends {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    g ((D.tile e.1).pts e.2) = c ∧ g ((D.tile e.1).pts (e.2 + 1)) = c :=
  ⟨(Dissection.mem_lineChain.mp he).1, (Dissection.mem_lineChain.mp he).2.1⟩
theorem lineChain_le {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    ∀ y ∈ (D.tile e.1).carrier, g y ≤ c :=
  (D.tile e.1).carrier_subset_halfplane g c (Dissection.mem_lineChain.mp he).2.2
theorem chain_mem_edge_iff (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) (t : ℝ) :
    AffineMap.lineMap Q W t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e.1) e.2) :=
  lineMap_mem_edge_iff hg hQW hQ hW _ _ (lineChain_ends D he).1 (lineChain_ends D he).2 t
theorem chain_lo_lt_hi (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    edgeLo Q W (D.tile e.1) e.2 < edgeHi Q W (D.tile e.1) e.2 :=
  edgeLo_lt_edgeHi _ _ (eq_lineMap_of_level hg hQW hQ hW (lineChain_ends D he).1)
    (eq_lineMap_of_level hg hQW hQ hW (lineChain_ends D he).2)
theorem lineChain_eq_of_two (hg : g ≠ 0) {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (he' : e' ∈ D.lineChain g c) {y z : Plane} (hyz : y ≠ z)
    (hy : y ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2)
    (hz : z ∈ (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2) : e = e' := by
  by_contra hne
  exact hyz (D.sameside_edges_subsingleton g c hg hne (lineChain_le D he) (lineChain_le D he')
    (D.lineChain_edge_subset he) (D.lineChain_edge_subset he') hy hz)
theorem lineChain_eq_of_overlap (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c)
    {e e' : Fin N × Fin 3} (he : e ∈ D.lineChain g c) (he' : e' ∈ D.lineChain g c)
    (h : max (edgeLo Q W (D.tile e.1) e.2) (edgeLo Q W (D.tile e'.1) e'.2)
      < min (edgeHi Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e'.1) e'.2)) : e = e' := by
  set a := max (edgeLo Q W (D.tile e.1) e.2) (edgeLo Q W (D.tile e'.1) e'.2)
  set b := min (edgeHi Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e'.1) e'.2)
  have hmem : ∀ t, a ≤ t → t ≤ b → AffineMap.lineMap Q W t ∈
      (D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2 := by
    intro t h1 h2
    refine ⟨(chain_mem_edge_iff D hg hQW hQ hW he t).mpr ⟨?_, ?_⟩,
      (chain_mem_edge_iff D hg hQW hQ hW he' t).mpr ⟨?_, ?_⟩⟩
    · exact le_trans (le_max_left _ _) h1
    · exact le_trans h2 (min_le_left _ _)
    · exact le_trans (le_max_right _ _) h1
    · exact le_trans h2 (min_le_right _ _)
  refine lineChain_eq_of_two D hg he he' ?_ (hmem a le_rfl h.le) (hmem b h.le le_rfl)
  intro hab
  exact h.ne (AffineMap.lineMap_injective ℝ hQW hab)
theorem vertex_params_finite (hQW : Q ≠ W) :
    {t : ℝ | AffineMap.lineMap Q W t ∈ D.vertexSet}.Finite :=
  D.vertexSet_finite.preimage (AffineMap.lineMap_injective ℝ hQW).injOn
theorem wall_cover_param (hg : g ≠ 0) (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) {a b : ℝ}
    (hab : a < b)
    (hint : openSegment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b)
      ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b),
      ∀ i, y ∉ interior (D.tile i).carrier)
    {t : ℝ} (ht : t ∈ Ioo a b) (hv : AffineMap.lineMap Q W t ∉ D.vertexSet) :
    ∃ e ∈ D.lineChain g c, t ∈ Icc (edgeLo Q W (D.tile e.1) e.2) (edgeHi Q W (D.tile e.1) e.2) := by
  have hne : AffineMap.lineMap Q W a ≠ (AffineMap.lineMap Q W b : Plane) :=
    fun h => hab.ne (AffineMap.lineMap_injective ℝ hQW h)
  have hS : segment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b) ⊆ {y | g y = c} := by
    rw [← image_segment]
    rintro _ ⟨s, -, rfl⟩
    exact level_lineMap hQ hW s
  have htmem : AffineMap.lineMap Q W t ∈
      openSegment ℝ (AffineMap.lineMap Q W a) (AffineMap.lineMap Q W b) := by
    rw [← image_openSegment, openSegment_eq_Ioo hab]
    exact ⟨t, ht, rfl⟩
  obtain ⟨e, he, hte⟩ := D.wall_cover g c hg hne hS hint hwall htmem hv
  exact ⟨e, he, (chain_mem_edge_iff D hg hQW hQ hW he t).mp hte⟩
end Chain
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem localAngle_mem {N : ℕ} (D : CongruentDissection N) (v : Plane) (i : Fin N) :
    (D.tile i).localAngle v = cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) ∨
    (D.tile i).localAngle v = cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) ∨
    (D.tile i).localAngle v = cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) ∨
    (D.tile i).localAngle v = Real.pi ∨ (D.tile i).localAngle v = 2 * Real.pi ∨
    (D.tile i).localAngle v = 0 := by
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with ⟨j, -, hval⟩ | h | h | h
  · obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
    rw [hval, hk]
    fin_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
theorem sum_eq_counts {ι : Type*} [Fintype ι] [DecidableEq ℝ] (f : ι → ℝ) (v : Fin 5 → ℝ)
    (hv0 : ∀ j, v j ≠ 0) (hinj : Function.Injective v)
    (hf : ∀ i, (∃ j, f i = v j) ∨ f i = 0) :
    ∑ i, f i = ∑ j, ((Finset.univ.filter fun i => f i = v j).card : ℝ) * v j := by
  have hpt : ∀ i, f i = ∑ j, if f i = v j then v j else 0 := by
    intro i
    rcases hf i with ⟨j, hj⟩ | h0
    · rw [Finset.sum_eq_single j]
      · simp [hj]
      · intro k _ hkj
        rw [if_neg]
        rw [hj]; exact fun h => hkj (hinj h).symm
      · simp
    · rw [h0, Finset.sum_eq_zero]
      intro k _
      rw [if_neg (fun h => hv0 k h.symm)]
  rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
section Defs
variable {N : ℕ} (D : CongruentDissection N)
noncomputable def tileα : ℝ := ∠ (D.model.pts 1) (D.model.pts 0) (D.model.pts 2)
noncomputable def tileβ : ℝ := ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)
noncomputable def tileγ : ℝ := ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)
noncomputable def angleCount (P : Plane) (θ : ℝ) : ℕ :=
  (Finset.univ.filter fun i => (D.tile i).localAngle P = θ).card
end Defs
def AnglesSep {N : ℕ} (D : CongruentDissection N) : Prop :=
  (∀ j, ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j ≠ 0) ∧
    Function.Injective ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi]
theorem corner_perm {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3,
      cornerAngle (U.pts (σ k + 1)) (U.pts (σ k)) (U.pts (σ k + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨σ, fun k => ?_⟩
  have hmap : cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2)))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
    rw [← hf (k + 1), ← hf k, ← hf (k + 2)]
    rw [Erdos634.Geometry.cornerAngle, Erdos634.Geometry.cornerAngle]
    rw [show (f : Plane → Plane) = f.toRealAffineIsometryEquiv from
      (IsometryEquiv.coeFn_toRealAffineIsometryEquiv f).symm]
    exact f.toRealAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _
  have hidx : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
      (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by decide
  have hne : ∀ x : Fin 3, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide
  obtain ⟨h1, h2, h12⟩ := hne k
  rcases hidx (σ k) (σ (k + 1)) (σ (k + 2))
      (fun he => h1 (σ.injective he)) (fun he => h2 (σ.injective he))
      (fun he => h12 (σ.injective he)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [← ha, ← hb]; exact hmap
  · rw [← ha, ← hb]
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]
    exact hmap
theorem tile_angle_count_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)
    (i : Fin N) :
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileα D).card = 1 ∧
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileβ D).card = 1 ∧
    (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileγ D).card = 1 := by
  classical
  obtain ⟨σ, hperm⟩ := corner_perm (D.tiles_congruent i).symm
  set M := D.model
  have hm : ∀ k : Fin 3, cornerAngle (M.pts (k + 1)) (M.pts k) (M.pts (k + 2)) =
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] (k.castLE (by norm_num)) := by
    intro k; fin_cases k <;> rfl
  have hdist : ∀ k l : Fin 3, cornerAngle (M.pts (k + 1)) (M.pts k) (M.pts (k + 2))
      = cornerAngle (M.pts (l + 1)) (M.pts l) (M.pts (l + 2)) → k = l := by
    intro k l h
    rw [hm, hm] at h
    exact Fin.castLE_injective _ (hsep.2 h)
  have hcount : ∀ k : Fin 3, (Finset.univ.filter fun j : Fin 3 =>
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        = cornerAngle (M.pts (k + 1)) (M.pts k) (M.pts (k + 2))).card = 1 := by
    intro k
    refine Finset.card_eq_one.mpr ⟨σ k, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      have h' := hperm (σ.symm j)
      rw [Equiv.apply_symm_apply] at h'
      have := hdist _ _ (h'.symm.trans hj)
      rw [← this, Equiv.apply_symm_apply]
    · intro hj; subst hj; exact hperm k
  exact ⟨hcount 0, hcount 1, hcount 2⟩
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem tri_side_subset_frontier (T : Tri) (i : Fin 3) :
    segment ℝ (T.pts i) (T.pts (i + 1)) ⊆ frontier T.carrier := by
  intro x hx
  have hcar : x ∈ T.carrier := T.convex.segment_subset
    (subset_convexHull ℝ _ ⟨i, rfl⟩) (subset_convexHull ℝ _ ⟨i + 1, rfl⟩) hx
  refine ⟨subset_closure hcar, fun hint => ?_⟩
  have hpos := (T.mem_interior_iff_coord_pos x).mp hint (i + 2)
  rw [segment_eq_image_lineMap] at hx
  obtain ⟨t, -, rfl⟩ := hx
  rw [AffineMap.apply_lineMap] at hpos
  have h1 : T.basis.coord (i + 2) (T.pts i) = 0 := by
    have : T.pts i = T.basis i := rfl
    rw [this, AffineBasis.coord_apply_ne]; fin_cases i <;> decide
  have h2 : T.basis.coord (i + 2) (T.pts (i + 1)) = 0 := by
    have : T.pts (i + 1) = T.basis (i + 1) := rfl
    rw [this, AffineBasis.coord_apply_ne]; fin_cases i <;> decide
  rw [h1, h2, AffineMap.lineMap_same_apply] at hpos
  exact lt_irrefl _ hpos
theorem fin3_ne_add_one : ∀ k : Fin 3, k ≠ k + 1 := by decide
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem edge_len_mem {N : ℕ} (D : CongruentDissection N) (j : Fin N) (k : Fin 3) :
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = dist (D.model.pts 1) (D.model.pts 2) ∨
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = dist (D.model.pts 2) (D.model.pts 0) ∨
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent j).dist_eq
  rw [hσ]
  have hne : σ k ≠ σ (k + 1) := σ.injective.ne (by fin_cases k <;> decide)
  generalize σ k = u at hne
  generalize σ (k + 1) = v at hne
  fin_cases u <;> fin_cases v <;>
    first
    | exact absurd rfl hne
    | (left; rfl) | (left; exact dist_comm _ _)
    | (right; left; rfl) | (right; left; exact dist_comm _ _)
    | (right; right; rfl) | (right; right; exact dist_comm _ _)
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem fin3_add_two_add_one : ∀ k : Fin 3, k + 2 + 1 = k := by decide
theorem fin3_add_two_add_two : ∀ k : Fin 3, k + 2 + 2 = k + 1 := by decide
theorem congruent_corner_opp {T U : Tri} (h : T.Congruent U) (k : Fin 3) :
    ∃ j : Fin 3, cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) =
        cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2)) ∧
      dist (T.pts (k + 1)) (T.pts (k + 2)) = dist (U.pts (j + 1)) (U.pts (j + 2)) := by
  obtain ⟨σ, hσ⟩ := h.dist_eq
  refine ⟨σ k, ?_, ?_⟩
  · have hang : cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) =
        cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2))) :=
      angle_of_sss (hσ _ _) (hσ _ _) (hσ _ _)
        (T.indep.injective.ne (by fin_cases k <;> decide))
        (T.indep.injective.ne (by fin_cases k <;> decide))
    rw [hang]
    have h1 : σ (k + 1) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h2 : σ (k + 2) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne (by fin_cases k <;> decide)
    generalize σ k = j0 at h1 h2 h12 ⊢
    generalize σ (k + 1) = j1 at h1 h2 h12 ⊢
    generalize σ (k + 2) = j2 at h1 h2 h12 ⊢
    fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;> simp at h1 h2 h12 ⊢ <;>
      first | rfl | exact angle_comm _ _ _
  · rw [hσ]
    have h1 : σ (k + 1) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h2 : σ (k + 2) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
    have h12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne (by fin_cases k <;> decide)
    generalize σ k = j0 at h1 h2 h12 ⊢
    generalize σ (k + 1) = j1 at h1 h2 h12 ⊢
    generalize σ (k + 2) = j2 at h1 h2 h12 ⊢
    fin_cases j0 <;> fin_cases j1 <;> fin_cases j2 <;> simp at h1 h2 h12 ⊢ <;>
      first | rfl | exact dist_comm _ _
theorem opp_side_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D) (i : Fin N)
    (k : Fin 3) :
    ((D.tile i).localAngle ((D.tile i).pts k) = tileα D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 1) (D.model.pts 2)) ∧
    ((D.tile i).localAngle ((D.tile i).pts k) = tileβ D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 2) (D.model.pts 0)) ∧
    ((D.tile i).localAngle ((D.tile i).pts k) = tileγ D →
      dist ((D.tile i).pts (k + 1)) ((D.tile i).pts (k + 2)) =
        dist (D.model.pts 0) (D.model.pts 1)) := by
  obtain ⟨-, hinj⟩ := hsep
  obtain ⟨j, hang, hd⟩ := congruent_corner_opp (D.tiles_congruent i) k
  rw [Tri.localAngle_vertex, hang, hd]
  have e0 : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = tileα D := rfl
  have e1 : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = tileβ D := rfl
  have e2 : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = tileγ D := rfl
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  fin_cases j
  · refine ⟨fun _ => rfl, fun h => absurd (e0.symm.trans h) (ne 0 1 (by decide)),
      fun h => absurd (e0.symm.trans h) (ne 0 2 (by decide))⟩
  · refine ⟨fun h => absurd (e1.symm.trans h) (ne 1 0 (by decide)), fun _ => rfl,
      fun h => absurd (e1.symm.trans h) (ne 1 2 (by decide))⟩
  · refine ⟨fun h => absurd (e2.symm.trans h) (ne 2 0 (by decide)),
      fun h => absurd (e2.symm.trans h) (ne 2 1 (by decide)), fun _ => rfl⟩
theorem localAngle_at_own_vertex_mem' {N : ℕ} (D : CongruentDissection N) (i : Fin N)
    (k : Fin 3) :
    (D.tile i).localAngle ((D.tile i).pts k) = tileα D ∨
    (D.tile i).localAngle ((D.tile i).pts k) = tileβ D ∨
    (D.tile i).localAngle ((D.tile i).pts k) = tileγ D := by
  rw [Tri.localAngle_vertex]
  obtain ⟨j, hj, -⟩ := congruent_corner_opp (D.tiles_congruent i) k
  rw [hj]
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
theorem side_walk_counts_sep {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)
    (part : Finset (Fin N × Fin 3))
    (L : ℝ) (hsum : ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = L) :
    L = ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileα D).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      + ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileβ D).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      + ((part.filter fun e => (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2))
          = tileγ D).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) := by
  classical
  obtain ⟨hv0, hinj⟩ := hsep
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  have hαβ : tileα D ≠ tileβ D := ne 0 1 (by decide)
  have hαγ : tileα D ≠ tileγ D := ne 0 2 (by decide)
  have hβγ : tileβ D ≠ tileγ D := ne 1 2 (by decide)
  have hpt : ∀ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileα D
        then dist (D.model.pts 1) (D.model.pts 2) else 0)
      + (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileβ D
        then dist (D.model.pts 2) (D.model.pts 0) else 0)
      + (if (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = tileγ D
        then dist (D.model.pts 0) (D.model.pts 1) else 0) := by
    intro e _
    have hsides := opp_side_sep D ⟨hv0, hinj⟩ e.1 (e.2 + 2)
    have e3 : e.2 + 2 + 1 = e.2 := fin3_add_two_add_one e.2
    have e4 : e.2 + 2 + 2 = e.2 + 1 := fin3_add_two_add_two e.2
    rw [e3, e4] at hsides
    have hmem := localAngle_at_own_vertex_mem' D e.1 (e.2 + 2)
    rcases hmem with h | h | h
    · rw [if_pos h, if_neg (h ▸ hαβ), if_neg (h ▸ hαγ), hsides.1 h]; ring
    · rw [if_neg (h ▸ hαβ.symm), if_pos h, if_neg (h ▸ hβγ), hsides.2.1 h]; ring
    · rw [if_neg (h ▸ hαγ.symm), if_neg (h ▸ hβγ.symm), if_pos h, hsides.2.2 h]; ring
  rw [← hsum, Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry MeasureTheory Set
theorem tri_closure_interior (T : Tri) : closure (interior T.carrier) = T.carrier := by
  rw [T.convex.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty,
    T.isCompact.isClosed.closure_eq]
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem tri_frontier_subset_edges (T : Tri) {x : Plane} (hx : x ∈ frontier T.carrier) :
    ∃ k, x ∈ T.edge k := by
  let D₁ : Dissection 1 :=
    { target := T, tile := fun _ => T, covers := Set.iUnion_const _,
      interiors_disjoint := fun i j h => absurd (Subsingleton.elim i j) h }
  obtain ⟨_, k, hk⟩ := Erdos634.BaseSelection.frontier_subset_edges D₁ hx
  exact ⟨k, hk⟩
theorem tri_frontier_subset_sides (T : Tri) {x : Plane} (hx : x ∈ frontier T.carrier) :
    x ∈ segment ℝ (T.pts 0) (T.pts 1) ∨ x ∈ segment ℝ (T.pts 1) (T.pts 2) ∨
      x ∈ segment ℝ (T.pts 2) (T.pts 0) := by
  obtain ⟨k, hk⟩ := tri_frontier_subset_edges T hx
  rw [Tri.edge] at hk
  fin_cases k
  · exact Or.inl hk
  · exact Or.inr (Or.inl hk)
  · exact Or.inr (Or.inr hk)
theorem eq_endpoint_of_mem_segment {x y u v : Plane} (hu : u ∈ segment ℝ x y)
    (hv : v ∈ segment ℝ x y) (hx : x ∈ segment ℝ u v) : x = u ∨ x = v := by
  by_cases hxy : x = y
  · subst hxy
    rw [segment_same] at hu
    exact Or.inl hu.symm
  have hL := AffineMap.lineMap_injective ℝ hxy
  rw [segment_eq_image_lineMap] at hu hv
  obtain ⟨s, hs, rfl⟩ := hu
  obtain ⟨t, ht, rfl⟩ := hv
  rw [← image_segment, segment_eq_Icc'] at hx
  obtain ⟨r, hr, hrx⟩ := hx
  have hr0 : r = 0 := hL (hrx.trans (AffineMap.lineMap_apply_zero x y).symm)
  subst hr0
  rcases le_total s t with h | h
  · left
    have h0 : s = 0 := le_antisymm (by have := hr.1; rwa [min_eq_left h] at this) hs.1
    rw [h0, AffineMap.lineMap_apply_zero]
  · right
    have h0 : t = 0 := le_antisymm (by have := hr.1; rwa [min_eq_right h] at this) ht.1
    rw [h0, AffineMap.lineMap_apply_zero]
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem Tri.basis_apply' (T : Tri) (j : Fin 3) : T.basis j = T.pts j := rfl
theorem Tri.coord_vertex (T : Tri) (i j : Fin 3) :
    T.basis.coord i (T.pts j) = if i = j then 1 else 0 := by
  rw [← Tri.basis_apply', AffineBasis.coord_apply]
theorem Tri.coord_lineMap (T : Tri) (i : Fin 3) (X Y : Plane) (t : ℝ) :
    T.basis.coord i (AffineMap.lineMap X Y t)
      = T.basis.coord i X + t * (T.basis.coord i Y - T.basis.coord i X) := by
  rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_module']
  simp only [smul_eq_mul]; ring
theorem Tri.coord_sum (T : Tri) (X : Plane) :
    T.basis.coord 0 X + T.basis.coord 1 X + T.basis.coord 2 X = 1 := by
  have := T.basis.sum_coord_apply_eq_one X
  rw [Fin.sum_univ_three] at this; exact this
theorem Tri.localAngle_openSegment (T : Tri) (m : Fin 3) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.pts m) (T.pts (m + 1))) : T.localAngle x = Real.pi := by
  classical
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  have hm : T.basis.coord m (AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t) = 1 - t := by
    rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m ≠ m + 1 by fin_cases m <;> decide]; ring
  have hm1 : T.basis.coord (m + 1) (AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t) = t := by
    rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 1 ≠ m by fin_cases m <;> decide]
  have hm2 : T.basis.coord (m + 2) (AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t) = 0 := by
    rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 2 ≠ m by fin_cases m <;> decide, show m + 2 ≠ m + 1 by fin_cases m <;> decide]
  set x := AffineMap.lineMap (T.pts m) (T.pts (m + 1)) t
  have hv : ¬ ∃ j, x = T.pts j := by
    rintro ⟨j, hj⟩
    have h1 := Tri.coord_vertex T m j
    have h2 := Tri.coord_vertex T (m + 1) j
    rw [← hj, hm] at h1
    rw [← hj, hm1] at h2
    split_ifs at h1 h2 <;> linarith
  have h2 : ¬ ∀ j, 0 < T.basis.coord j x := fun h => by have := h (m + 2); rw [hm2] at this; linarith
  have h3 : ∃ k, T.basis.coord k x = 0 ∧ ∀ j, j ≠ k → 0 < T.basis.coord j x := by
    refine ⟨m + 2, hm2, fun j hj => ?_⟩
    have : j = m ∨ j = m + 1 := by fin_cases m <;> fin_cases j <;> simp at hj ⊢
    rcases this with rfl | rfl
    · rw [hm]; linarith
    · rw [hm1]; exact ht0
  rw [Tri.localAngle, dif_neg hv, if_neg h2, if_pos h3]
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
section Counts
variable {N : ℕ} (D : CongruentDissection N)
theorem angleCount_pos {P : Plane} {θ : ℝ} {i : Fin N} (hi : (D.tile i).localAngle P = θ) :
    1 ≤ angleCount D P θ :=
  Finset.card_pos.mpr ⟨i, by simp [hi]⟩
variable (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr
variable (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hA hC
end Counts
section Corners
variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr
end Corners
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry MeasureTheory
open Classical in
theorem wall_sum {N : ℕ} (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    {U V : Plane} (hUV : U ≠ V) (hS : segment ℝ U V ⊆ {y | f y = c})
    (hint : openSegment ℝ U V ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ U V, ∀ i, y ∉ interior (D.tile i).carrier)
    (hdich : ∀ e ∈ D.lineChain f c, (D.tile e.1).edge e.2 ⊆ segment ℝ U V ∨
      ((D.tile e.1).edge e.2 ∩ segment ℝ U V).Subsingleton) :
    ∑ e ∈ (D.lineChain f c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ U V),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = dist U V := by
  classical
  haveI : NullSingletonClass (Measure.hausdorffMeasure (1 : ℝ) : Measure Plane) :=
    Measure.nullSingletonClass_hausdorff _ one_pos
  have hp := D.wall_partition f c hf hUV hS hint hwall
  rw [← Finset.sum_filter_add_sum_filter_not (D.lineChain f c)
    (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ U V)] at hp
  have h0 : ∑ e ∈ (D.lineChain f c).filter
      (fun e => ¬ (D.tile e.1).edge e.2 ⊆ segment ℝ U V),
      (Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile e.1).edge e.2 ∩ segment ℝ U V)
      = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    obtain ⟨he, hns⟩ := Finset.mem_filter.mp he
    exact ((hdich e he).resolve_left hns).measure_zero _
  have h1 : ∀ e ∈ (D.lineChain f c).filter
      (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ U V),
      (Measure.hausdorffMeasure 1 : Measure Plane) ((D.tile e.1).edge e.2 ∩ segment ℝ U V)
      = edist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
    intro e he
    rw [Set.inter_eq_left.mpr (Finset.mem_filter.mp he).2, Tri.hausdorff_edge]
  rw [h0, add_zero, Finset.sum_congr rfl h1, hausdorffMeasure_segment] at hp
  have := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_sum (fun e _ => edist_ne_top _ _)] at this
  simpa [← dist_edist] using this
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem Tri.coord_openSegment (T : Tri) (m : Fin 3) {x : Plane}
    (hx : x ∈ openSegment ℝ (T.pts m) (T.pts (m + 1))) :
    0 < T.basis.coord m x ∧ 0 < T.basis.coord (m + 1) x ∧ T.basis.coord (m + 2) x = 0 := by
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  refine ⟨?_, ?_, ?_⟩
  · rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m ≠ m + 1 by fin_cases m <;> decide]; linarith
  · rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 1 ≠ m by fin_cases m <;> decide]; exact ht0
  · rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex]
    simp [show m + 2 ≠ m by fin_cases m <;> decide, show m + 2 ≠ m + 1 by fin_cases m <;> decide]
theorem fin3_cases3 : ∀ j k : Fin 3, j = k ∨ j = k + 1 ∨ j = k + 2 := by decide
theorem level_eq_coord (T : Tri) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (k : Fin 3)
    (h1 : g (T.pts (k + 1)) = c) (h2 : g (T.pts (k + 2)) = c) (Y : Plane) :
    g Y - c = T.basis.coord k Y * (g (T.pts k) - c) := by
  have hY := T.basis.linear_combination_coord_eq_self Y
  have hs := T.basis.sum_coord_apply_eq_one Y
  have hgY : g Y = ∑ i, T.basis.coord i Y * g (T.pts i) := by
    conv_lhs => rw [← hY]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]; rfl
  have hc : c = ∑ i, T.basis.coord i Y * c := by rw [← Finset.sum_mul, hs, one_mul]
  have e3 : ∀ i : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := fun i => fin3_cases3 i k
  rw [hgY]
  conv_lhs => rw [hc]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k]
  · ring
  · intro i _ hik
    rcases e3 i with h | h | h
    · exact absurd h hik
    · rw [h, h1]; ring
    · rw [h, h2]; ring
  · simp
theorem exists_small_pos {a b : ℝ} (ha : 0 < a) :
    ∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ → 0 < a + ε * b := by
  by_cases hb : 0 ≤ b
  · exact ⟨1, one_pos, fun ε hε _ => by nlinarith⟩
  · push Not at hb
    refine ⟨a / (-b), div_pos ha (by linarith), fun ε hε hlt => ?_⟩
    rw [lt_div_iff₀ (by linarith)] at hlt
    nlinarith
theorem edge_level_oriented (T : Tri) (m : Fin 3) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ (∀ y ∈ T.edge m, g y = c) ∧ c < g (T.pts (m + 2)) := by
  obtain ⟨f, c, hf, hline⟩ := T.edge_line m
  have h1 : f (T.pts m) = c := hline _ (left_mem_segment _ _ _)
  have h2 : f (T.pts (m + 1)) = c := hline _ (right_mem_segment _ _ _)
  have hne : f (T.pts (m + 2)) ≠ c := by
    intro h3
    apply hf
    have hall : ∀ Y, f Y = c := by
      intro Y
      have := level_eq_coord T f c (m + 2) (by rw [fin3_add_two_add_one]; exact h1)
        (by rw [fin3_add_two_add_two]; exact h2) Y
      rw [h3, sub_self, mul_zero] at this; linarith
    have hc : c = 0 := by rw [← hall 0, map_zero]
    ext Y; simp [hall Y, hc]
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨-f, -c, neg_ne_zero.mpr hf, fun y hy => by simp [hline y hy], ?_⟩
    simp only [LinearMap.neg_apply]; linarith
  · exact ⟨f, c, hf, hline, h⟩
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry
theorem Tri.localAngle_le_two_pi (T : Tri) (p : Plane) : T.localAngle p ≤ 2 * Real.pi := by
  classical
  rw [Tri.localAngle]
  split
  · exact le_trans (EuclideanGeometry.angle_le_pi _ _ _) (by linarith [Real.pi_pos])
  · split
    · exact le_rfl
    · split <;> linarith [Real.pi_pos]
theorem Tri.localAngle_le_pi (T : Tri) {p : Plane} (hp : p ∉ interior T.carrier) :
    T.localAngle p ≤ Real.pi := by
  classical
  rw [Tri.localAngle]
  split
  · exact EuclideanGeometry.angle_le_pi _ _ _
  · split
    · rename_i h; exact absurd ((Tri.mem_interior_iff_coord_pos T p).mpr h) hp
    · split <;> linarith [Real.pi_pos]
theorem Tri.vertex_not_mem_openSegment (T : Tri) (k m : Fin 3) :
    T.pts k ∉ openSegment ℝ (T.pts m) (T.pts (m + 1)) := by
  intro h
  obtain ⟨h0, h1, h2⟩ := Tri.coord_openSegment T m h
  rw [Tri.coord_vertex] at h0 h1 h2
  rcases fin3_cases3 k m with rfl | rfl | rfl
  · have : ¬ (k + 1 = k) := by fin_cases k <;> decide
    simp [this] at h1
  · have : ¬ (m = m + 1) := by fin_cases m <;> decide
    simp [this] at h0
  · have : ¬ (m = m + 2) := by fin_cases m <;> decide
    simp [this] at h0
theorem Tri.openSegment_edge_unique (T : Tri) {m m' : Fin 3} {p : Plane}
    (h : p ∈ openSegment ℝ (T.pts m) (T.pts (m + 1)))
    (h' : p ∈ openSegment ℝ (T.pts m') (T.pts (m' + 1))) : m = m' := by
  obtain ⟨a0, a1, a2⟩ := Tri.coord_openSegment T m h
  obtain ⟨b0, b1, b2⟩ := Tri.coord_openSegment T m' h'
  rcases fin3_cases3 m' m with rfl | rfl | rfl
  · rfl
  · rw [show m + 1 + 1 = m + 2 by fin_cases m <;> rfl, a2] at b1
    exact absurd b1 (lt_irrefl 0)
  · rw [show m + 2 + 2 = m + 1 by fin_cases m <;> rfl] at b2
    linarith
section Dissection
variable {N : ℕ} (D : Dissection N)
theorem mem_interior_of_sum_gt {p : Plane} (hp : Real.pi < ∑ i, (D.tile i).localAngle p) :
    p ∈ interior D.target.carrier := by
  by_contra h
  rw [D.sum_localAngle_eq] at hp
  linarith [Tri.localAngle_le_pi D.target h]
theorem sum_ge_two {i j : Fin N} (hij : i ≠ j) (p : Plane) :
    (D.tile i).localAngle p + (D.tile j).localAngle p ≤ ∑ k, (D.tile k).localAngle p := by
  calc _ = ∑ k ∈ {i, j}, (D.tile k).localAngle p := (Finset.sum_pair hij).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun k _ _ => (D.tile k).localAngle_nonneg p
theorem sum_ge_three {i j k : Fin N} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (p : Plane) :
    (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p
      ≤ ∑ l, (D.tile l).localAngle p := by
  have h : ({i, j, k} : Finset (Fin N)).sum (fun l => (D.tile l).localAngle p)
      = (D.tile i).localAngle p + (D.tile j).localAngle p + (D.tile k).localAngle p := by
    rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_pair hjk, add_assoc]
  rw [← h]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun l _ _ => (D.tile l).localAngle_nonneg p
theorem interior_of_two_openSegment {i j : Fin N} (hij : i ≠ j) {m m' : Fin 3} {p : Plane}
    (hi : p ∈ openSegment ℝ ((D.tile i).pts m) ((D.tile i).pts (m + 1)))
    (hj : p ∈ openSegment ℝ ((D.tile j).pts m') ((D.tile j).pts (m' + 1))) :
    p ∈ interior D.target.carrier := by
  apply mem_interior_of_sum_gt D
  have := sum_ge_two D hij p
  rw [Tri.localAngle_openSegment _ m hi, Tri.localAngle_openSegment _ m' hj] at this
  linarith [Real.pi_pos]
theorem interior_of_vertex_openSegment {i j : Fin N} {k m : Fin 3} {p : Plane}
    (hi : (D.tile i).pts k = p)
    (hj : p ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1))) :
    p ∈ interior D.target.carrier := by
  have hij : i ≠ j := by
    rintro rfl
    exact Tri.vertex_not_mem_openSegment _ k m (hi ▸ hj)
  apply mem_interior_of_sum_gt D
  have := sum_ge_two D hij p
  rw [← hi, Tri.localAngle_vertex, hi, Tri.localAngle_openSegment _ m hj] at this
  have hc := Erdos634.MarchFlank.cornerAngle_pos (D.tile i) k
  rw [hi] at hc
  linarith
theorem openSegment_tile_unique {i j j' : Fin N} {k m m' : Fin 3} {p : Plane}
    (hi : (D.tile i).pts k = p)
    (hj : p ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
    (hj' : p ∈ openSegment ℝ ((D.tile j').pts m') ((D.tile j').pts (m' + 1))) : j = j' := by
  by_contra hjj
  have hij : i ≠ j := by
    rintro rfl
    exact Tri.vertex_not_mem_openSegment _ k m (hi ▸ hj)
  have hij' : i ≠ j' := by
    rintro rfl
    exact Tri.vertex_not_mem_openSegment _ k m' (hi ▸ hj')
  have hsum := sum_ge_three D hij hij' hjj p
  rw [← hi, Tri.localAngle_vertex, hi, Tri.localAngle_openSegment _ m hj,
    Tri.localAngle_openSegment _ m' hj', D.sum_localAngle_eq] at hsum
  have hc := Erdos634.MarchFlank.cornerAngle_pos (D.tile i) k
  rw [hi] at hc
  linarith [Tri.localAngle_le_two_pi D.target p]
end Dissection
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
section Parity
variable {α : Type*} [DecidableEq α]
theorem even_card_of_pairing (R : α → α → Prop) (hsymm : ∀ x y, R x y → R y x)
    (hirr : ∀ x, ¬ R x x) (huniq : ∀ x y z, R x y → R x z → y = z) :
    ∀ n (A : Finset α), A.card = n → (∀ x ∈ A, ∃ y ∈ A, R x y) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A hA hpair
  rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · rw [← hA, Finset.card_empty]; exact ⟨0, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hpair x hx
  have hne : y ≠ x := fun h => hirr x (h ▸ hxy)
  set A' := (A.erase x).erase y with hA'def
  have hcard : A'.card + 2 = n := by
    rw [hA'def, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne, hy⟩),
      Finset.card_erase_of_mem hx, ← hA]
    have : 2 ≤ A.card := by
      have h2 : ({x, y} : Finset α) ⊆ A := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hx
        · rw [Finset.mem_singleton.mp hz]; exact hy
      have := Finset.card_le_card h2
      rwa [Finset.card_pair hne.symm] at this
    omega
  have hpair' : ∀ z ∈ A', ∃ w ∈ A', R z w := by
    intro z hz
    have hzy : z ≠ y := (Finset.mem_erase.mp hz).1
    have hzx : z ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
    have hzA : z ∈ A := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
    obtain ⟨w, hw, hzw⟩ := hpair z hzA
    refine ⟨w, ?_, hzw⟩
    have hwx : w ≠ x := by
      rintro rfl
      exact hzy (huniq w y z hxy (hsymm z w hzw)).symm
    have hwy : w ≠ y := by
      rintro rfl
      exact hzx (huniq w x z (hsymm x w hxy) (hsymm z w hzw)).symm
    exact Finset.mem_erase.mpr ⟨hwy, Finset.mem_erase.mpr ⟨hwx, hw⟩⟩
  have := ih A'.card (by omega) A' rfl hpair'
  rw [← hcard]
  exact this.add ⟨1, rfl⟩
theorem card_filter_mod_two (S : Finset α) (R : α → α → Prop) [DecidableRel R]
    (Θ : α → Prop) [DecidablePred Θ]
    (hsymm : ∀ x ∈ S, ∀ y ∈ S, R x y → R y x) (hirr : ∀ x, ¬ R x x)
    (huniq : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R x z → y = z)
    (hnomix : ∀ x ∈ S, ∀ y ∈ S, R x y → Θ x → Θ y)
    (L : Finset α) (hL : ∀ x, x ∈ L ↔ x ∈ S ∧ Θ x ∧ ∀ y ∈ S, ¬ R x y) :
    (S.filter Θ).card % 2 = L.card % 2 := by
  have hLeq : L = S.filter fun x => Θ x ∧ ∀ y ∈ S, ¬ R x y := by
    ext x; rw [hL, Finset.mem_filter]
  subst hLeq
  set P := S.filter fun x => Θ x ∧ ∃ y ∈ S, R x y
  have hsplit : (S.filter Θ).card
      = (S.filter fun x => Θ x ∧ ∀ y ∈ S, ¬ R x y).card + P.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := S.filter Θ) (fun x => ∀ y ∈ S, ¬ R x y),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    ext x
    simp only [P, Finset.mem_filter, not_forall, not_not, exists_prop]
  let R' : α → α → Prop := fun x y => x ∈ S ∧ y ∈ S ∧ R x y
  have hP : Even P.card := by
    refine even_card_of_pairing R' (fun x y h => ⟨h.2.1, h.1, hsymm x h.1 y h.2.1 h.2.2⟩)
      (fun x h => hirr x h.2.2)
      (fun x y z h1 h2 => huniq x h1.1 y h1.2.1 z h2.2.1 h1.2.2 h2.2.2) _ P rfl ?_
    intro x hx
    obtain ⟨hxS, hxΘ, y, hyS, hxy⟩ := Finset.mem_filter.mp hx
    refine ⟨y, Finset.mem_filter.mpr ⟨hyS, hnomix x hxS y hyS hxy hxΘ, x, hxS,
      hsymm x hxS y hyS hxy⟩, hxS, hyS, hxy⟩
  rw [hsplit, Nat.add_mod, Nat.even_iff.mp hP, add_zero, Nat.mod_mod]
end Parity
section EdgesAt
variable {N : ℕ} (D : Dissection N)
open Classical in
noncomputable def edgesAt (Q : Plane) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => (D.tile e.1).pts e.2 = Q ∨ (D.tile e.1).pts (e.2 + 1) = Q
open Classical in
noncomputable def farEnd (Q : Plane) (e : Fin N × Fin 3) : Plane :=
  if (D.tile e.1).pts e.2 = Q then (D.tile e.1).pts (e.2 + 1) else (D.tile e.1).pts e.2
def SameRayAt (Q : Plane) (e e' : Fin N × Fin 3) : Prop :=
  ∃ t : ℝ, 0 < t ∧ farEnd D Q e' = AffineMap.lineMap Q (farEnd D Q e) t
theorem mem_edgesAt {Q : Plane} {e : Fin N × Fin 3} :
    e ∈ edgesAt D Q ↔ (D.tile e.1).pts e.2 = Q ∨ (D.tile e.1).pts (e.2 + 1) = Q := by
  classical
  simp [edgesAt]
theorem tri_pts_succ_ne (T : Tri) (k : Fin 3) : T.pts k ≠ T.pts (k + 1) := by
  intro h
  have := T.indep.injective h
  have hne : ∀ m : Fin 3, m ≠ m + 1 := by decide
  exact hne k this
theorem edgesAt_ends {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) :
    ((D.tile e.1).pts e.2 = Q ∧ (D.tile e.1).pts (e.2 + 1) = farEnd D Q e) ∨
    ((D.tile e.1).pts e.2 = farEnd D Q e ∧ (D.tile e.1).pts (e.2 + 1) = Q) := by
  classical
  rcases (mem_edgesAt D).mp he with h | h
  · left; exact ⟨h, by rw [farEnd, if_pos h]⟩
  · right
    have h' : (D.tile e.1).pts e.2 ≠ Q := fun h0 =>
      tri_pts_succ_ne (D.tile e.1) e.2 (h0.trans h.symm)
    exact ⟨by rw [farEnd, if_neg h'], h⟩
theorem farEnd_ne {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) : farEnd D Q e ≠ Q := by
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h2, ← h1]; exact (tri_pts_succ_ne _ _).symm
  · rw [← h1, ← h2]; exact tri_pts_succ_ne _ _
theorem edgesAt_edge {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) :
    (D.tile e.1).edge e.2 = segment ℝ Q (farEnd D Q e) := by
  rw [Tri.edge]
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, segment_symm]
theorem level_far {Q : Plane} {e : Fin N × Fin 3} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (he : e ∈ edgesAt D Q) (hQ : g Q = c) (hF : g (farEnd D Q e) = c) :
    g ((D.tile e.1).pts e.2) = c ∧ g ((D.tile e.1).pts (e.2 + 1)) = c := by
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact ⟨hQ, hF⟩
  · rw [h1, h2]; exact ⟨hF, hQ⟩
theorem not_mem_both_chains {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {e : Fin N × Fin 3}
    (h1 : e ∈ D.lineChain g c) (h2 : e ∈ D.lineChain (-g) (-c)) : False := by
  obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp h1
  obtain ⟨-, -, b3⟩ := Dissection.mem_lineChain.mp h2
  have h3 : g ((D.tile e.1).pts (e.2 + 2)) = c := by
    have := b3 (e.2 + 2)
    simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
    exact le_antisymm (a3 _) this
  obtain ⟨t, ht⟩ := eq_lineMap_of_level hg (tri_pts_succ_ne (D.tile e.1) e.2) a1 a2 h3
  have hc := congrArg ((D.tile e.1).basis.coord (e.2 + 2)) ht
  rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex, Tri.coord_vertex] at hc
  have n1 : ∀ k : Fin 3, ¬ (k + 2 = k) := by decide
  have n2 : ∀ k : Fin 3, ¬ (k + 2 = k + 1) := by decide
  simp [n1 e.2, n2 e.2] at hc
theorem edgesAt_chain {Q : Plane} {e : Fin N × Fin 3} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
    (he : e ∈ edgesAt D Q) (hQ : g Q = c) (hF : g (farEnd D Q e) = c) :
    e ∈ D.lineChain g c ∨ e ∈ D.lineChain (-g) (-c) := by
  obtain ⟨a1, a2⟩ := level_far D he hQ hF
  rcases le_total (g ((D.tile e.1).pts (e.2 + 2))) c with h | h
  · left
    refine Dissection.mem_lineChain.mpr ⟨a1, a2, fun i => ?_⟩
    rcases fin3_cases3 i e.2 with rfl | rfl | rfl
    · exact a1.le
    · exact a2.le
    · exact h
  · right
    refine Dissection.mem_lineChain.mpr ⟨by simp [a1], by simp [a2], fun i => ?_⟩
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    rcases fin3_cases3 i e.2 with rfl | rfl | rfl
    · exact a1.ge
    · exact a2.ge
    · exact h
theorem ray_level {Q F : Plane} (hQF : F ≠ Q) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧ g F = c := by
  refine ⟨crossL (F - Q), cross (F - Q) Q, crossL_ne_zero (sub_ne_zero.mpr hQF), rfl, ?_⟩
  rw [crossL_apply]
  have h := cross_sub_right (F - Q) F Q
  rw [cross_self] at h
  linarith
theorem mem_edge_of_ray {Q F : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q) {t : ℝ}
    (hF : farEnd D Q e = AffineMap.lineMap Q F t) {s : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) :
    AffineMap.lineMap Q F s ∈ (D.tile e.1).edge e.2 := by
  rw [edgesAt_edge D he, hF]
  have h0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  have : segment ℝ Q (AffineMap.lineMap Q F t) = AffineMap.lineMap Q F '' segment ℝ 0 t := by
    rw [image_segment, h0]
  rw [this, segment_eq_Icc (hs0.trans hst)]
  exact ⟨s, ⟨hs0, hst⟩, rfl⟩
theorem lineMap_lineMap_eq {Q F : Plane} (t s : ℝ) :
    AffineMap.lineMap Q (AffineMap.lineMap Q F t) s = AffineMap.lineMap Q F (s * t) := by
  simp only [AffineMap.lineMap_apply_module', smul_smul, add_sub_cancel_right]
theorem sameRayAt_symm {Q : Plane} {e e' : Fin N × Fin 3} (h : SameRayAt D Q e e') : SameRayAt D Q e' e := by
  obtain ⟨t, ht, hF⟩ := h
  refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩
  rw [hF, lineMap_lineMap_eq, inv_mul_cancel₀ ht.ne', AffineMap.lineMap_apply_one]
theorem sameRayAt_unique {Q : Plane} {e e' e'' : Fin N × Fin 3} (he : e ∈ edgesAt D Q)
    (he' : e' ∈ edgesAt D Q) (he'' : e'' ∈ edgesAt D Q) (h1 : e' ≠ e) (h2 : e'' ≠ e)
    (h3 : e' ≠ e'') (r1 : SameRayAt D Q e e') (r2 : SameRayAt D Q e e'') : False := by
  obtain ⟨t', ht', hF'⟩ := r1
  obtain ⟨t'', ht'', hF''⟩ := r2
  set F := farEnd D Q e
  obtain ⟨g, c, hg, hgQ, hgF⟩ := ray_level (farEnd_ne D he)
  set s := min 1 (min t' t'') with hsdef
  have hs : 0 < s := lt_min one_pos (lt_min ht' ht'')
  have hy : ∀ x ∈ edgesAt D Q, ∀ t : ℝ, s ≤ t → farEnd D Q x = AffineMap.lineMap Q F t →
      Q ∈ (D.tile x.1).edge x.2 ∧ AffineMap.lineMap Q F s ∈ (D.tile x.1).edge x.2 := by
    intro x hx t hst ht
    refine ⟨?_, mem_edge_of_ray D hx ht hs.le hst⟩
    rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
  have y0 := hy e he 1 (min_le_left _ _) (AffineMap.lineMap_apply_one Q F).symm
  have y1 := hy e' he' t' ((min_le_right _ _).trans (min_le_left _ _)) hF'
  have y2 := hy e'' he'' t'' ((min_le_right _ _).trans (min_le_right _ _)) hF''
  have hyQ : AffineMap.lineMap Q F s ≠ Q := by
    intro h
    have : AffineMap.lineMap Q F s = (AffineMap.lineMap Q F (0 : ℝ) : Plane) := by
      rw [h, AffineMap.lineMap_apply_zero]
    exact hs.ne' (AffineMap.lineMap_injective ℝ (farEnd_ne D he).symm this)
  have hlev : ∀ x ∈ edgesAt D Q, (∃ t : ℝ, farEnd D Q x = AffineMap.lineMap Q F t) →
      x ∈ D.lineChain g c ∨ x ∈ D.lineChain (-g) (-c) := by
    rintro x hx ⟨t, ht⟩
    exact edgesAt_chain D hx hgQ (by rw [ht]; exact level_lineMap hgQ hgF t)
  have c0 := hlev e he ⟨1, (AffineMap.lineMap_apply_one Q F).symm⟩
  have c1 := hlev e' he' ⟨t', hF'⟩
  have c2 := hlev e'' he'' ⟨t'', hF''⟩
  have key : ∀ {g' : Plane →ₗ[ℝ] ℝ} {c' : ℝ}, g' ≠ 0 → ∀ x y : Fin N × Fin 3,
      (Q ∈ (D.tile x.1).edge x.2 ∧ AffineMap.lineMap Q F s ∈ (D.tile x.1).edge x.2) →
      (Q ∈ (D.tile y.1).edge y.2 ∧ AffineMap.lineMap Q F s ∈ (D.tile y.1).edge y.2) →
      x ≠ y → x ∈ D.lineChain g' c' → y ∈ D.lineChain g' c' → False := by
    intro g' c' hg' x y hx hy' hxy hxc hyc
    exact hxy (lineChain_eq_of_two D hg' hxc hyc hyQ.symm ⟨hx.1, hy'.1⟩ ⟨hx.2, hy'.2⟩)
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  rcases c0 with c0 | c0 <;> rcases c1 with c1 | c1 <;> rcases c2 with c2 | c2
  · exact key hg e e' y0 y1 h1.symm c0 c1
  · exact key hg e e' y0 y1 h1.symm c0 c1
  · exact key hg e e'' y0 y2 h2.symm c0 c2
  · exact key hng e' e'' y1 y2 h3 c1 c2
  · exact key hg e' e'' y1 y2 h3 c1 c2
  · exact key hng e e'' y0 y2 h2.symm c0 c2
  · exact key hng e e' y0 y1 h1.symm c0 c1
  · exact key hng e e' y0 y1 h1.symm c0 c1
theorem lonely_openSegment {Q : Plane} {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q)
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (hgQ : g Q = c) (hgF : g (farEnd D Q e) = c)
    (hec : e ∈ D.lineChain g c)
    (hlonely : ∀ e' ∈ edgesAt D Q, e' ≠ e → ¬ SameRayAt D Q e e')
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (hint : AffineMap.lineMap Q (farEnd D Q e) τ ∈ interior D.target.carrier) :
    ∃ e₂ ∈ D.lineChain (-g) (-c),
      Q ∈ openSegment ℝ ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) := by
  set F := farEnd D Q e
  have hQF : Q ≠ F := (farEnd_ne D he).symm
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  have hnQ : (-g) Q = -c := by simp [hgQ]
  have hnF : (-g) F = -c := by simp [hgF]
  have hL0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  have hQt : Q ∈ D.target.carrier := by
    rw [← D.covers]
    refine Set.mem_iUnion.mpr ⟨e.1, ?_⟩
    have : Q ∈ (D.tile e.1).edge e.2 := by rw [edgesAt_edge D he]; exact left_mem_segment ℝ _ _
    exact (D.tile e.1).edge_subset_carrier e.2 this
  have hseg : openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F τ)
      ⊆ interior D.target.carrier := by
    rw [hL0]
    exact D.target.convex.openSegment_closure_interior_subset_interior (subset_closure hQt) hint
  have hwall : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F τ),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    rw [← image_openSegment, openSegment_eq_Ioo hτ.1] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact D.edge_point_not_interior (mem_edge_of_ray D he (t := 1)
      (AffineMap.lineMap_apply_one Q F).symm hs.1.le (hs.2.le.trans hτ.2.le))
  obtain ⟨e₂, he₂, hlo, hhi⟩ := exists_interval_right (D.lineChain (-g) (-c))
    (fun x => edgeLo Q F (D.tile x.1) x.2) (fun x => edgeHi Q F (D.tile x.1) x.2) 0
    hτ.1 (vertex_params_finite D hQF) (fun y hy hyv => by
      rw [zero_add] at hy
      exact wall_cover_param D hng hQF hnQ hnF hτ.1 hseg hwall hy hyv)
  obtain ⟨n1, n2⟩ := lineChain_ends D he₂
  have n1' : g ((D.tile e₂.1).pts e₂.2) = c := by simpa using n1
  have n2' : g ((D.tile e₂.1).pts (e₂.2 + 1)) = c := by simpa using n2
  rcases hlo.lt_or_eq with hlo | hlo
  · refine ⟨e₂, he₂, ?_⟩
    rw [← hL0]
    exact (lineMap_mem_openSegment_iff hg hQF hgQ hgF _ _ n1' n2' 0).mpr ⟨hlo, hhi⟩
  · exfalso
    have hne : e₂ ≠ e := fun h => not_mem_both_chains D hg hec (h ▸ he₂)
    have e1 := eq_lineMap_lineParam hg hQF hgQ hgF n1'
    have e2 := eq_lineMap_lineParam hg hQF hgQ hgF n2'
    simp only [edgeLo, edgeHi] at hlo hhi
    rcases min_choice (lineParam Q F ((D.tile e₂.1).pts e₂.2))
      (lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1))) with hm | hm
    · rw [hm] at hlo
      have hQ2 : (D.tile e₂.1).pts e₂.2 = Q := by rw [← e1, hlo, hL0]
      have hmem : e₂ ∈ edgesAt D Q := (mem_edgesAt D).mpr (Or.inl hQ2)
      refine hlonely e₂ hmem hne ⟨lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1)), ?_, ?_⟩
      · rcases max_choice (lineParam Q F ((D.tile e₂.1).pts e₂.2))
          (lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1))) with h' | h'
        · rw [h', hlo] at hhi; exact absurd hhi (lt_irrefl _)
        · rw [h'] at hhi; exact hhi
      · rw [farEnd, if_pos hQ2, e2]
    · rw [hm] at hlo
      have hQ2 : (D.tile e₂.1).pts (e₂.2 + 1) = Q := by rw [← e2, hlo, hL0]
      have hmem : e₂ ∈ edgesAt D Q := (mem_edgesAt D).mpr (Or.inr hQ2)
      have hQ1 : (D.tile e₂.1).pts e₂.2 ≠ Q := fun h0 =>
        tri_pts_succ_ne (D.tile e₂.1) e₂.2 (h0.trans hQ2.symm)
      refine hlonely e₂ hmem hne ⟨lineParam Q F ((D.tile e₂.1).pts e₂.2), ?_, ?_⟩
      · rcases max_choice (lineParam Q F ((D.tile e₂.1).pts e₂.2))
          (lineParam Q F ((D.tile e₂.1).pts (e₂.2 + 1))) with h' | h'
        · rw [h'] at hhi; exact hhi
        · rw [h', hlo] at hhi; exact absurd hhi (lt_irrefl _)
      · rw [farEnd, if_neg hQ1, e1]
end EdgesAt
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
def edgeType (φ : ℝ) (e : Fin N × Fin 3) : Prop :=
  (D.tile e.1).localAngle ((D.tile e.1).pts (e.2 + 2)) = φ
theorem sum_two_edges (k0 : Fin 3) (f : Fin 3 → Prop) [DecidablePred f] :
    (∑ k : Fin 3, if (k = k0 ∨ k = k0 + 2) ∧ f k then (1 : ℕ) else 0)
      = (if f k0 then 1 else 0) + (if f (k0 + 2) then 1 else 0) := by
  rw [Fin.sum_univ_three]
  fin_cases k0 <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceAdd,
    Fin.reduceEq, or_true, or_false, true_and, false_and, if_false, add_zero, zero_add,
    or_self] <;> split_ifs <;> simp
theorem card_three (k0 : Fin 3) (p : Fin 3 → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card
      = (if p k0 then 1 else 0) + (if p (k0 + 1) then 1 else 0) + (if p (k0 + 2) then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_three]
  fin_cases k0 <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
    Fin.reduceAdd] <;> split_ifs <;> simp
variable (hsep : AnglesSep D)
include hsep
theorem localAngle_ne_of_not_vertex {i : Fin N} {Q : Plane} (hQ : ∀ k, (D.tile i).pts k ≠ Q)
    {φ : ℝ} (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) : (D.tile i).localAngle Q ≠ φ := by
  have ⟨hv0, hinj⟩ := hsep
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) Q with ⟨j, hj, -⟩ | h | h | h
  · exact absurd hj.symm (hQ j)
  · rw [h]
    rcases hφ with rfl | rfl | rfl
    · exact (ne 4 0 (by decide))
    · exact (ne 4 1 (by decide))
    · exact (ne 4 2 (by decide))
  · rw [h]
    rcases hφ with rfl | rfl | rfl
    · exact (ne 3 0 (by decide))
    · exact (ne 3 1 (by decide))
    · exact (ne 3 2 (by decide))
  · rw [h]
    rcases hφ with rfl | rfl | rfl
    · exact (hv0 0).symm
    · exact (hv0 1).symm
    · exact (hv0 2).symm
open Classical in
theorem tile_marked_count (i : Fin N) (Q : Plane) {φ : ℝ}
    (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) :
    (∑ k : Fin 3, if ((D.tile i).pts k = Q ∨ (D.tile i).pts (k + 1) = Q) ∧
        edgeType D φ (i, k) then 1 else 0)
      + (if (D.tile i).localAngle Q = φ then 1 else 0)
      = (if (D.tile i).localAngle Q = tileα D then 1 else 0)
        + (if (D.tile i).localAngle Q = tileβ D then 1 else 0)
        + (if (D.tile i).localAngle Q = tileγ D then 1 else 0) := by
  have ⟨hv0, hinj⟩ := hsep
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  have hαβ : tileα D ≠ tileβ D := ne 0 1 (by decide)
  have hαγ : tileα D ≠ tileγ D := ne 0 2 (by decide)
  have hβγ : tileβ D ≠ tileγ D := ne 1 2 (by decide)
  by_cases hv : ∃ k0, (D.tile i).pts k0 = Q
  · obtain ⟨k0, hk0⟩ := hv
    have hinj' := (D.tile i).indep.injective
    have hcond : ∀ k : Fin 3, ((D.tile i).pts k = Q ∨ (D.tile i).pts (k + 1) = Q) ↔
        (k = k0 ∨ k = k0 + 2) := by
      intro k
      rw [← hk0]
      constructor
      · rintro (h | h)
        · exact Or.inl (hinj' h)
        · right
          have := hinj' h
          rw [← this]
          fin_cases k <;> rfl
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · right
          congr 1
          fin_cases k0 <;> rfl
    simp only [hcond]
    rw [sum_two_edges k0 (fun k => edgeType D φ (i, k))]
    have hloc : ∀ k, (D.tile i).localAngle ((D.tile i).pts k)
        = cornerAngle ((D.tile i).pts (k + 1)) ((D.tile i).pts k) ((D.tile i).pts (k + 2)) :=
      Tri.localAngle_vertex _
    obtain ⟨cα, cβ, cγ⟩ := tile_angle_count_sep D hsep i
    have hone : (if (D.tile i).localAngle ((D.tile i).pts k0) = φ then 1 else 0)
        + (if (D.tile i).localAngle ((D.tile i).pts (k0 + 1)) = φ then 1 else 0)
        + (if (D.tile i).localAngle ((D.tile i).pts (k0 + 2)) = φ then 1 else 0) = 1 := by
      have hc : (Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
          ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = φ).card = 1 := by
        rcases hφ with rfl | rfl | rfl
        · exact cα
        · exact cβ
        · exact cγ
      simp only [← hloc] at hc
      have h3 := card_three k0 (fun k => (D.tile i).localAngle ((D.tile i).pts k) = φ)
      rw [hc] at h3
      exact h3.symm
    have hk2 : k0 + 2 + 2 = k0 + 1 := by fin_cases k0 <;> rfl
    have e1 : edgeType D φ (i, k0) ↔ (D.tile i).localAngle ((D.tile i).pts (k0 + 2)) = φ :=
      Iff.rfl
    have e2 : edgeType D φ (i, k0 + 2) ↔ (D.tile i).localAngle ((D.tile i).pts (k0 + 1)) = φ := by
      show (D.tile i).localAngle ((D.tile i).pts (k0 + 2 + 2)) = φ ↔ _
      rw [hk2]
    simp only [e1, e2]
    rw [← hk0]
    set θ := (D.tile i).localAngle ((D.tile i).pts k0)
    rcases localAngle_at_own_vertex_mem' D i k0 with h | h | h
    · have n1 : ¬ θ = tileβ D := fun h' => hαβ (h.symm.trans h')
      have n2 : ¬ θ = tileγ D := fun h' => hαγ (h.symm.trans h')
      rw [if_pos h, if_neg n1, if_neg n2]
      omega
    · have n1 : ¬ θ = tileα D := fun h' => hαβ (h'.symm.trans h)
      have n2 : ¬ θ = tileγ D := fun h' => hβγ (h.symm.trans h')
      rw [if_neg n1, if_pos h, if_neg n2]
      omega
    · have n1 : ¬ θ = tileα D := fun h' => hαγ (h'.symm.trans h)
      have n2 : ¬ θ = tileβ D := fun h' => hβγ (h'.symm.trans h)
      rw [if_neg n1, if_neg n2, if_pos h]
      omega
  · push Not at hv
    have h0 : ∀ k : Fin 3, ¬ (((D.tile i).pts k = Q ∨ (D.tile i).pts (k + 1) = Q) ∧
        edgeType D φ (i, k)) := fun k h => by
      rcases h.1 with h' | h'
      · exact hv k h'
      · exact hv (k + 1) h'
    simp only [h0, if_false, Finset.sum_const_zero, zero_add]
    rw [if_neg (localAngle_ne_of_not_vertex D hsep hv hφ),
      if_neg (localAngle_ne_of_not_vertex D hsep hv (Or.inl rfl)),
      if_neg (localAngle_ne_of_not_vertex D hsep hv (Or.inr (Or.inl rfl))),
      if_neg (localAngle_ne_of_not_vertex D hsep hv (Or.inr (Or.inr rfl)))]
open Classical in
theorem card_marked (Q : Plane) {φ : ℝ} (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) :
    ((edgesAt D.toDissection Q).filter (edgeType D φ)).card + angleCount D Q φ
      = angleCount D Q (tileα D) + angleCount D Q (tileβ D) + angleCount D Q (tileγ D) := by
  have hfilt : (edgesAt D.toDissection Q).filter (edgeType D φ) = Finset.univ.filter fun e =>
      ((D.tile e.1).pts e.2 = Q ∨ (D.tile e.1).pts (e.2 + 1) = Q) ∧ edgeType D φ e := by
    rw [edgesAt, Finset.filter_filter]
  rw [hfilt, Finset.card_filter, Fintype.sum_prod_type]
  simp only [angleCount, Finset.card_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => tile_marked_count D hsep i Q hφ
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : Dissection N) (isθ : Fin N × Fin 3 → Prop)
structure LinkData (Q R : Plane) (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) : Prop where
  ne : Q ≠ R
  hg : g ≠ 0
  hQ : g Q = c
  hR : g R = c
  cov : ∀ y ∈ openSegment ℝ Q R, ∃ e ∈ D.lineChain g c, y ∈ (D.tile e.1).edge e.2
  inner : ∀ e ∈ D.lineChain g c, ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty →
    (D.tile e.1).edge e.2 ⊆ segment ℝ Q R ∧ isθ e
  start : ∀ e ∈ D.lineChain g c, isθ e → Q ∈ (D.tile e.1).edge e.2 →
    ∀ y ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ y R
  past : ∃ e ∈ D.lineChain g c, ¬ isθ e ∧ R ∈ (D.tile e.1).edge e.2 ∧
    ∃ y ∈ (D.tile e.1).edge e.2, R ∈ openSegment ℝ Q y
  across : ∃ e ∈ D.lineChain (-g) (-c),
    R ∈ openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
def IsLink (Q R : Plane) : Prop := ∃ g c, LinkData D isθ Q R g c
theorem openSegment_param {Q R y : Plane} :
    y ∈ openSegment ℝ Q R ↔ ∃ t ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap Q R t = y := by
  rw [openSegment_eq_image_lineMap]
  rfl
theorem segment_param {Q R y : Plane} :
    y ∈ segment ℝ Q R ↔ ∃ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap Q R t = y := by
  rw [segment_eq_image_lineMap]
  rfl
theorem lineMap_mem_openSegment_params {Q R : Plane} (hQR : Q ≠ R) {a b t : ℝ} :
    AffineMap.lineMap Q R t ∈
        openSegment ℝ (AffineMap.lineMap Q R a) (AffineMap.lineMap Q R b) ↔
      t ∈ openSegment ℝ a b := by
  rw [← image_openSegment]
  exact (AffineMap.lineMap_injective ℝ hQR).mem_set_image
theorem third_off_line (T : Tri) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (k : Fin 3)
    (h1 : g (T.pts k) = c) (h2 : g (T.pts (k + 1)) = c) : g (T.pts (k + 2)) ≠ c := by
  intro h3
  obtain ⟨t, ht⟩ := eq_lineMap_of_level hg (tri_pts_succ_ne T k) h1 h2 h3
  have hc := congrArg (T.basis.coord (k + 2)) ht
  rw [Tri.coord_lineMap, Tri.coord_vertex, Tri.coord_vertex, Tri.coord_vertex] at hc
  have n1 : ∀ k : Fin 3, ¬ (k + 2 = k) := by decide
  have n2 : ∀ k : Fin 3, ¬ (k + 2 = k + 1) := by decide
  simp [n1 k, n2 k] at hc
theorem chain_transfer {g₁ g₂ : Plane →ₗ[ℝ] ℝ} {c₁ c₂ : ℝ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {ε : Fin N × Fin 3} (h₁ : ε ∈ D.lineChain (-g₁) (-c₁)) (h₂ : ε ∈ D.lineChain (-g₂) (-c₂)) :
    (∀ y, g₂ y = c₂ → g₁ y = c₁) ∧ (∀ e ∈ D.lineChain g₂ c₂, e ∈ D.lineChain g₁ c₁) := by
  obtain ⟨j, m⟩ := ε
  set S := D.tile j
  have i1 : ∀ m : Fin 3, m + 2 + 1 = m := by decide
  have i2 : ∀ m : Fin 3, m + 2 + 2 = m + 1 := by decide
  have lev : ∀ {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}, g ≠ 0 → (j, m) ∈ D.lineChain (-g) (-c) →
      g (S.pts (m + 2 + 1)) = c ∧ g (S.pts (m + 2 + 2)) = c ∧ 0 < g (S.pts (m + 2)) - c := by
    intro g c hg hε
    obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp hε
    simp only [LinearMap.neg_apply, neg_inj] at a1 a2
    have b3 := a3 (m + 2)
    simp only [LinearMap.neg_apply, neg_le_neg_iff] at b3
    refine ⟨by rw [i1]; exact a1, by rw [i2]; exact a2, ?_⟩
    have := third_off_line S hg m a1 a2
    exact sub_pos.mpr (lt_of_le_of_ne b3 (Ne.symm this))
  obtain ⟨p1, p2, d1⟩ := lev hg₁ h₁
  obtain ⟨q1, q2, d2⟩ := lev hg₂ h₂
  have key1 := level_eq_coord S g₁ c₁ (m + 2) p1 p2
  have key2 := level_eq_coord S g₂ c₂ (m + 2) q1 q2
  have hon : ∀ y, g₂ y = c₂ → g₁ y = c₁ := by
    intro y hy
    have h2y := key2 y
    rw [hy, sub_self] at h2y
    have hc : S.basis.coord (m + 2) y = 0 := by
      rcases mul_eq_zero.mp h2y.symm with h | h
      · exact h
      · linarith
    have h1y := key1 y
    rw [hc, zero_mul] at h1y
    linarith
  refine ⟨hon, fun e he => ?_⟩
  obtain ⟨e1, e2, e3⟩ := Dissection.mem_lineChain.mp he
  refine Dissection.mem_lineChain.mpr ⟨hon _ e1, hon _ e2, fun i => ?_⟩
  have h2y := key2 ((D.tile e.1).pts i)
  have h1y := key1 ((D.tile e.1).pts i)
  have hle := e3 i
  have hc : S.basis.coord (m + 2) ((D.tile e.1).pts i) ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith
  nlinarith
namespace LinkData
variable {D isθ} {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
theorem mem_edge_iff (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (t : ℝ) : AffineMap.lineMap Q R t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2) :=
  chain_mem_edge_iff D h.hg h.ne h.hQ h.hR he t
theorem params_of_inner (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) (hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ Q R) :
    0 ≤ edgeLo Q R (D.tile e.1) e.2 ∧ edgeHi Q R (D.tile e.1) e.2 ≤ 1 := by
  have hlt := chain_lo_lt_hi D h.hg h.ne h.hQ h.hR he
  have key : ∀ t ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2),
      t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := segment_param.mp (hsub ((h.mem_edge_iff he t).mpr ht))
    rwa [← AffineMap.lineMap_injective ℝ h.ne hst]
  exact ⟨(key _ ⟨le_rfl, hlt.le⟩).1, (key _ ⟨hlt.le, le_rfl⟩).2⟩
theorem arrive (h : LinkData D isθ Q R g c) :
    ∃ e ∈ D.lineChain g c, isθ e ∧ 0 ≤ edgeLo Q R (D.tile e.1) e.2 ∧
      edgeLo Q R (D.tile e.1) e.2 < 1 ∧ edgeHi Q R (D.tile e.1) e.2 = 1 := by
  obtain ⟨e, he, hlo, hhi⟩ := exists_interval_left (D.lineChain g c)
    (fun x => edgeLo Q R (D.tile x.1) x.2) (fun x => edgeHi Q R (D.tile x.1) x.2) 1
    one_pos Set.finite_empty (fun y hy _ => by
      rw [sub_self] at hy
      obtain ⟨e, he, hye⟩ := h.cov _ (openSegment_param.mpr ⟨y, hy, rfl⟩)
      exact ⟨e, he, (h.mem_edge_iff he y).mp hye⟩)
  set m := max (edgeLo Q R (D.tile e.1) e.2) 0
  have hm1 : m < 1 := max_lt hlo one_pos
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty := by
    refine ⟨AffineMap.lineMap Q R ((m + 1) / 2), (h.mem_edge_iff he _).mpr ⟨?_, ?_⟩,
      openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith [le_max_left (edgeLo Q R (D.tile e.1) e.2) 0]
    · linarith
    · linarith [le_max_right (edgeLo Q R (D.tile e.1) e.2) 0]
    · linarith
  obtain ⟨hsub, hθ⟩ := h.inner e he hmeet
  obtain ⟨h0, h1⟩ := h.params_of_inner he hsub
  exact ⟨e, he, hθ, h0, hlo, le_antisymm h1 hhi⟩
theorem end_of_param (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) :
    ∃ k : Fin 3, (D.tile e.1).pts k = AffineMap.lineMap Q R (edgeHi Q R (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  rcases max_choice (lineParam Q R ((D.tile e.1).pts e.2))
    (lineParam Q R ((D.tile e.1).pts (e.2 + 1))) with hm | hm
  · exact ⟨e.2, by rw [edgeHi, hm, eq_lineMap_lineParam h.hg h.ne h.hQ h.hR n1]⟩
  · exact ⟨e.2 + 1, by rw [edgeHi, hm, eq_lineMap_lineParam h.hg h.ne h.hQ h.hR n2]⟩
theorem end_vertex (h : LinkData D isθ Q R g c) : ∃ i k, (D.tile i).pts k = R := by
  obtain ⟨e, he, -, -, -, hhi⟩ := h.arrive
  obtain ⟨k, hk⟩ := h.end_of_param he
  exact ⟨e.1, k, by rw [hk, hhi, AffineMap.lineMap_apply_one]⟩
theorem end_interior (h : LinkData D isθ Q R g c) : R ∈ interior D.target.carrier := by
  obtain ⟨i, k, hk⟩ := h.end_vertex
  obtain ⟨e, -, he⟩ := h.across
  exact interior_of_vertex_openSegment D hk he
theorem leave (h : LinkData D isθ Q R g c) :
    ∃ e ∈ D.lineChain g c, ¬ isθ e ∧ edgeLo Q R (D.tile e.1) e.2 = 1 ∧
      1 < edgeHi Q R (D.tile e.1) e.2 := by
  obtain ⟨e, he, hθ, hRe, y, hy, hRy⟩ := h.past
  have hR1 : (1 : ℝ) ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2) := by
    rw [← h.mem_edge_iff he, AffineMap.lineMap_apply_one]; exact hRe
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  obtain ⟨s, hs⟩ : ∃ s, AffineMap.lineMap Q R s = y := by
    have hgy : g y = c := D.lineChain_edge_subset he y hy
    exact ⟨_, eq_lineMap_lineParam h.hg h.ne h.hQ h.hR hgy⟩
  have hs1 : 1 < s := by
    have hseg : openSegment ℝ Q y = AffineMap.lineMap Q R '' openSegment ℝ 0 s := by
      rw [image_openSegment, AffineMap.lineMap_apply_zero, hs]
    rw [hseg] at hRy
    obtain ⟨t, ht, hteq⟩ := hRy
    have ht1 : t = 1 :=
      AffineMap.lineMap_injective ℝ h.ne (hteq.trans (AffineMap.lineMap_apply_one Q R).symm)
    rw [ht1] at ht
    rcases lt_trichotomy 0 s with h0 | h0 | h0
    · rw [openSegment_eq_Ioo h0] at ht; exact ht.2
    · rw [← h0, openSegment_same] at ht; norm_num at ht
    · rw [openSegment_symm, openSegment_eq_Ioo h0] at ht; linarith [ht.1, ht.2]
  have hsI : s ∈ Icc (edgeLo Q R (D.tile e.1) e.2) (edgeHi Q R (D.tile e.1) e.2) := by
    rw [← h.mem_edge_iff he, hs]; exact hy
  refine ⟨e, he, hθ, ?_, lt_of_lt_of_le hs1 hsI.2⟩
  by_contra hne
  have hlo : edgeLo Q R (D.tile e.1) e.2 < 1 := lt_of_le_of_ne hR1.1 hne
  set m := max (edgeLo Q R (D.tile e.1) e.2) 0
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty := by
    refine ⟨AffineMap.lineMap Q R ((m + 1) / 2), (h.mem_edge_iff he _).mpr ⟨?_, ?_⟩,
      openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith [le_max_left (edgeLo Q R (D.tile e.1) e.2) 0, max_lt hlo one_pos]
    · linarith [max_lt hlo one_pos, hR1.2]
    · linarith [le_max_right (edgeLo Q R (D.tile e.1) e.2) 0]
    · linarith [max_lt hlo one_pos]
  exact hθ (h.inner e he hmeet).2
section Two
variable {Q₁ Q₂ : Plane} {g₁ g₂ : Plane →ₗ[ℝ] ℝ} {c₁ c₂ : ℝ}
theorem same_side (h1 : LinkData D isθ Q₁ R g₁ c₁) (h2 : LinkData D isθ Q₂ R g₂ c₂) :
    (∀ y, g₂ y = c₂ → g₁ y = c₁) ∧ (∀ e ∈ D.lineChain g₂ c₂, e ∈ D.lineChain g₁ c₁) := by
  obtain ⟨i, k, hik⟩ := h1.end_vertex
  obtain ⟨ε₁, hε₁, hR₁⟩ := h1.across
  obtain ⟨ε₂, hε₂, hR₂⟩ := h2.across
  have hj : ε₁.1 = ε₂.1 := openSegment_tile_unique D hik hR₁ hR₂
  obtain ⟨j, m⟩ := ε₁
  obtain ⟨j', m'⟩ := ε₂
  simp only at hj
  subst hj
  have hm : m = m' := Tri.openSegment_edge_unique (D.tile j) hR₁ hR₂
  subst hm
  exact chain_transfer D h1.hg h2.hg hε₁ hε₂
theorem not_between (h1 : LinkData D isθ Q₁ R g₁ c₁) (h2 : LinkData D isθ Q₂ R g₂ c₂)
    (hQ : Q₂ ∈ openSegment ℝ Q₁ R) : False := by
  obtain ⟨t2, ht2, hQ2⟩ := openSegment_param.mp hQ
  obtain ⟨e, he, hlo, hhi⟩ := exists_interval_left (D.lineChain g₁ c₁)
    (fun x => edgeLo Q₁ R (D.tile x.1) x.2) (fun x => edgeHi Q₁ R (D.tile x.1) x.2) t2
    ht2.1 Set.finite_empty (fun y hy _ => by
      rw [sub_self] at hy
      obtain ⟨e, he, hye⟩ := h1.cov _ (openSegment_param.mpr ⟨y, ⟨hy.1, hy.2.trans ht2.2⟩, rfl⟩)
      exact ⟨e, he, (h1.mem_edge_iff he y).mp hye⟩)
  set m := max (edgeLo Q₁ R (D.tile e.1) e.2) 0
  have hm : m < t2 := max_lt hlo ht2.1
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q₁ R).Nonempty := by
    refine ⟨AffineMap.lineMap Q₁ R ((m + t2) / 2), (h1.mem_edge_iff he _).mpr ⟨?_, ?_⟩,
      openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith [le_max_left (edgeLo Q₁ R (D.tile e.1) e.2) 0]
    · linarith
    · linarith [le_max_right (edgeLo Q₁ R (D.tile e.1) e.2) 0]
    · linarith [ht2.2]
  obtain ⟨-, hθ⟩ := h1.inner e he hmeet
  have he2 : e ∈ D.lineChain g₂ c₂ := (same_side h2 h1).2 e he
  refine h2.start e he2 hθ ?_ (AffineMap.lineMap Q₁ R (edgeLo Q₁ R (D.tile e.1) e.2))
    ((h1.mem_edge_iff he _).mpr ⟨le_rfl, (hlo.trans_le hhi).le⟩) ?_
  · rw [← hQ2]; exact (h1.mem_edge_iff he _).mpr ⟨hlo.le, hhi⟩
  · rw [← hQ2]
    have := (lineMap_mem_openSegment_params h1.ne (a := edgeLo Q₁ R (D.tile e.1) e.2) (b := 1)
      (t := t2)).mpr (by rw [openSegment_eq_Ioo (hlo.trans ht2.2)]; exact ⟨hlo, ht2.2⟩)
    rwa [AffineMap.lineMap_apply_one] at this
theorem not_opposite (h1 : LinkData D isθ Q₁ R g₁ c₁) (h2 : LinkData D isθ Q₂ R g₂ c₂)
    {t2 : ℝ} (ht2 : 1 < t2) (hQ2 : AffineMap.lineMap Q₁ R t2 = Q₂) : False := by
  obtain ⟨e, he, hθ, hlo, hhi⟩ := h1.leave
  have he2 : e ∈ D.lineChain g₂ c₂ := (same_side h2 h1).2 e he
  set s := (1 + min (edgeHi Q₁ R (D.tile e.1) e.2) t2) / 2
  have hs1 : 1 < s := by
    have := lt_min hhi ht2
    simp only [s]; linarith
  have hs2 : s < min (edgeHi Q₁ R (D.tile e.1) e.2) t2 := by
    have := lt_min hhi ht2
    simp only [s]; linarith
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q₂ R).Nonempty := by
    refine ⟨AffineMap.lineMap Q₁ R s, (h1.mem_edge_iff he _).mpr
      ⟨by rw [hlo]; exact hs1.le, (hs2.trans_le (min_le_left _ _)).le⟩, ?_⟩
    rw [← hQ2, openSegment_symm]
    have := (lineMap_mem_openSegment_params h1.ne (a := 1) (b := t2) (t := s)).mpr
      (by rw [openSegment_eq_Ioo ht2]; exact ⟨hs1, hs2.trans_le (min_le_right _ _)⟩)
    rwa [AffineMap.lineMap_apply_one] at this
  exact hθ (h2.inner e he2 hmeet).2
end Two
end LinkData
theorem link_unique {Q₁ Q₂ R : Plane} (h1 : IsLink D isθ Q₁ R) (h2 : IsLink D isθ Q₂ R) :
    Q₁ = Q₂ := by
  obtain ⟨g₁, c₁, h1⟩ := h1
  obtain ⟨g₂, c₂, h2⟩ := h2
  have hon := (h1.same_side h2).1 Q₂ h2.hQ
  obtain ⟨t2, ht2⟩ := eq_lineMap_of_level h1.hg h1.ne h1.hQ h1.hR hon
  rcases lt_trichotomy t2 0 with h0 | h0 | h0
  · exfalso
    refine h2.not_between h1 ?_
    rw [ht2]
    have := (lineMap_mem_openSegment_params h1.ne (a := t2) (b := 1) (t := 0)).mpr
      (by rw [openSegment_eq_Ioo (h0.trans one_pos)]; exact ⟨h0, one_pos⟩)
    rwa [AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero] at this
  · rw [ht2, h0, AffineMap.lineMap_apply_zero]
  · rcases lt_trichotomy t2 1 with h1' | h1' | h1'
    · exact (h1.not_between h2 (openSegment_param.mpr ⟨t2, ⟨h0, h1'⟩, ht2.symm⟩)).elim
    · exact absurd (by rw [ht2, h1', AffineMap.lineMap_apply_one]) h2.ne
    · exact (h1.not_opposite h2 h1' ht2.symm).elim
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
theorem Tri.lineMap_mem_interior (T : Tri) (m : Fin 3) {Q Z : Plane}
    (hQ : Q ∈ openSegment ℝ (T.pts m) (T.pts (m + 1))) (hZ : 0 < T.basis.coord (m + 2) Z) :
    ∃ τ₀ > (0 : ℝ), ∀ τ, 0 < τ → τ < τ₀ → AffineMap.lineMap Q Z τ ∈ interior T.carrier := by
  obtain ⟨h0, h1, h2⟩ := Tri.coord_openSegment T m hQ
  obtain ⟨ε0, hε0, hε⟩ := exists_small_pos (b := T.basis.coord m Z - T.basis.coord m Q) h0
  obtain ⟨ε1, hε1, hε'⟩ :=
    exists_small_pos (b := T.basis.coord (m + 1) Z - T.basis.coord (m + 1) Q) h1
  refine ⟨min ε0 ε1, lt_min hε0 hε1, fun τ hτ hτ' => ?_⟩
  rw [Tri.mem_interior_iff_coord_pos]
  intro j
  rw [Tri.coord_lineMap]
  rcases fin3_cases3 j m with rfl | rfl | rfl
  · exact hε τ hτ (lt_of_lt_of_le hτ' (min_le_left _ _))
  · exact hε' τ hτ (lt_of_lt_of_le hτ' (min_le_right _ _))
  · rw [h2, sub_zero, zero_add]; exact mul_pos hτ hZ
theorem tile_side_of_openSegment {N : ℕ} (D : Dissection N) {j : Fin N} {m : Fin 3} {Q : Plane}
    (hQ : Q ∈ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
    {i : Fin N} (hij : i ≠ j) (hQi : Q ∈ (D.tile i).carrier) :
    ∀ z ∈ (D.tile i).carrier, (D.tile j).basis.coord (m + 2) z ≤ 0 := by
  intro z hz
  by_contra hpos
  push Not at hpos
  obtain ⟨τ0, hτ0, hint⟩ := Tri.lineMap_mem_interior (D.tile j) m hQ hpos
  set τ := min τ0 1 / 2
  have hτ : 0 < τ := by have := lt_min hτ0 one_pos; simp only [τ]; linarith
  have hττ : τ < τ0 := by have := min_le_left τ0 1; simp only [τ]; linarith
  have hτ1 : τ ≤ 1 := by have := min_le_right τ0 1; simp only [τ]; linarith
  have hyS := hint τ hτ hττ
  have hyT : AffineMap.lineMap Q z τ ∈ (D.tile i).carrier := by
    refine (D.tile i).convex.segment_subset hQi hz ?_
    rw [segment_eq_image_lineMap]
    exact ⟨τ, ⟨hτ.le, hτ1⟩, rfl⟩
  have hcl : AffineMap.lineMap Q z τ ∈ closure (interior (D.tile i).carrier) := by
    rw [tri_closure_interior]; exact hyT
  obtain ⟨w, hwS, hwT⟩ := mem_closure_iff.mp hcl _ isOpen_interior hyS
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hwT hwS
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : Dissection N) (isθ : Fin N × Fin 3 → Prop)
theorem edgesAt_params {Q F : Plane} (hQF : Q ≠ F) {e : Fin N × Fin 3} (he : e ∈ edgesAt D Q)
    {t : ℝ} (ht : 0 < t) (hfar : farEnd D Q e = AffineMap.lineMap Q F t) :
    edgeLo Q F (D.tile e.1) e.2 = 0 ∧ edgeHi Q F (D.tile e.1) e.2 = t := by
  have h0 : lineParam Q F Q = 0 := by
    have := lineParam_lineMap hQF 0
    rwa [AffineMap.lineMap_apply_zero] at this
  have ht' : lineParam Q F (farEnd D Q e) = t := by rw [hfar, lineParam_lineMap hQF]
  rw [edgeLo, edgeHi]
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, h0, ht', min_eq_left ht.le, max_eq_right ht.le]; exact ⟨rfl, rfl⟩
  · rw [h1, h2, h0, ht', min_eq_right ht.le, max_eq_left ht.le]; exact ⟨rfl, rfl⟩
theorem tile_ne_of_chains {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {e₁ e₂ : Fin N × Fin 3}
    (h1 : e₁ ∈ D.lineChain g c) (h2 : e₂ ∈ D.lineChain (-g) (-c)) : e₁.1 ≠ e₂.1 := by
  intro h
  obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp h1
  obtain ⟨-, -, b3⟩ := Dissection.mem_lineChain.mp h2
  apply third_off_line (D.tile e₁.1) hg e₁.2 a1 a2
  have := b3 (e₁.2 + 2)
  rw [← h] at this
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at this
  exact le_antisymm (a3 _) this
theorem pair_line {Q : Plane} {e₁ e₂ : Fin N × Fin 3} (he₁ : e₁ ∈ edgesAt D Q)
    (he₂ : e₂ ∈ edgesAt D Q) (hne : e₂ ≠ e₁) (hray : SameRayAt D Q e₁ e₂) :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (t₂ : ℝ), g ≠ 0 ∧ g Q = c ∧ g (farEnd D Q e₁) = c ∧
      e₁ ∈ D.lineChain g c ∧ e₂ ∈ D.lineChain (-g) (-c) ∧ 0 < t₂ ∧
      farEnd D Q e₂ = AffineMap.lineMap Q (farEnd D Q e₁) t₂ := by
  obtain ⟨t₂, ht₂, hF₂⟩ := hray
  set F := farEnd D Q e₁
  have hQF : Q ≠ F := (farEnd_ne D he₁).symm
  obtain ⟨g₀, c₀, hg₀, hQ₀, hF₀⟩ := ray_level (farEnd_ne D he₁)
  obtain ⟨g, c, hg, hQ, hF, h1⟩ : ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧ g F = c ∧
      e₁ ∈ D.lineChain g c := by
    rcases edgesAt_chain D he₁ hQ₀ hF₀ with h | h
    · exact ⟨g₀, c₀, hg₀, hQ₀, hF₀, h⟩
    · exact ⟨-g₀, -c₀, neg_ne_zero.mpr hg₀, by simp [hQ₀], by simp only [LinearMap.neg_apply, F, hF₀], h⟩
  refine ⟨g, c, t₂, hg, hQ, hF, h1, ?_, ht₂, hF₂⟩
  have hF2 : g (farEnd D Q e₂) = c := by rw [hF₂]; exact level_lineMap hQ hF t₂
  rcases edgesAt_chain D he₂ hQ hF2 with h2 | h2
  · exfalso
    have hs : 0 < min 1 t₂ := lt_min one_pos ht₂
    have hm1 := mem_edge_of_ray D he₁ (t := 1) (AffineMap.lineMap_apply_one Q F).symm hs.le
      (min_le_left _ _)
    have hm2 := mem_edge_of_ray D he₂ hF₂ hs.le (min_le_right _ _)
    have hQ1 : Q ∈ (D.tile e₁.1).edge e₁.2 := by
      rw [edgesAt_edge D he₁]; exact left_mem_segment ℝ _ _
    have hQ2 : Q ∈ (D.tile e₂.1).edge e₂.2 := by
      rw [edgesAt_edge D he₂]; exact left_mem_segment ℝ _ _
    have hneq : Q ≠ AffineMap.lineMap Q F (min 1 t₂) := by
      intro h
      have : AffineMap.lineMap Q F (0 : ℝ) = AffineMap.lineMap Q F (min 1 t₂) := by
        rw [AffineMap.lineMap_apply_zero]; exact h
      exact hs.ne (AffineMap.lineMap_injective ℝ hQF this)
    exact hne (lineChain_eq_of_two D hg h1 h2 hneq ⟨hQ1, hQ2⟩ ⟨hm1, hm2⟩).symm
  · exact h2
theorem param_dich {lo hi T : ℝ} (h : ∀ x ∈ Ioo 0 T, x ∈ Icc lo hi → 0 ≤ lo ∧ hi ≤ T) :
    Icc lo hi ⊆ Icc 0 T ∨ (Icc lo hi ∩ Icc 0 T).Subsingleton := by
  by_cases hx : ∃ x ∈ Ioo 0 T, x ∈ Icc lo hi
  · obtain ⟨x, hx, hxI⟩ := hx
    obtain ⟨h0, hT⟩ := h x hx hxI
    left
    exact fun y hy => ⟨h0.trans hy.1, hy.2.trans hT⟩
  · right
    push Not at hx
    intro a ha b hb
    by_contra hab
    apply hx ((a + b) / 2)
    · rcases lt_or_gt_of_ne hab with h' | h'
      · constructor <;> linarith [ha.2.1, hb.2.2]
      · constructor <;> linarith [ha.2.2, hb.2.1]
    · constructor <;> linarith [ha.1.1, hb.1.1, ha.1.2, hb.1.2]
theorem exists_pts_eq_hi {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q F : Plane} (hQF : Q ≠ F)
    (hQ : g Q = c) (hF : g F = c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c) :
    ∃ k : Fin 3, (D.tile e.1).pts k = AffineMap.lineMap Q F (edgeHi Q F (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  rcases max_choice (lineParam Q F ((D.tile e.1).pts e.2))
    (lineParam Q F ((D.tile e.1).pts (e.2 + 1))) with hm | hm
  · exact ⟨e.2, by rw [edgeHi, hm, eq_lineMap_lineParam hg hQF hQ hF n1]⟩
  · exact ⟨e.2 + 1, by rw [edgeHi, hm, eq_lineMap_lineParam hg hQF hQ hF n2]⟩
theorem dich_of_param {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q F : Plane} (hQF : Q ≠ F)
    (hQ : g Q = c) (hF : g F = c) {T : ℝ} (hT : 0 < T)
    (hin : ∀ e ∈ D.lineChain g c, ∀ x ∈ Ioo 0 T,
      x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
        0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T) :
    ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ Q (AffineMap.lineMap Q F T) ∨
      ((D.tile e.1).edge e.2 ∩ segment ℝ Q (AffineMap.lineMap Q F T)).Subsingleton := by
  have hseg : AffineMap.lineMap Q F '' Icc 0 T = segment ℝ Q (AffineMap.lineMap Q F T) := by
    rw [← segment_eq_Icc hT.le, image_segment, AffineMap.lineMap_apply_zero]
  intro e he
  have himg : (D.tile e.1).edge e.2 =
      AffineMap.lineMap Q F '' Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) :=
    edge_eq_image hg hQF hQ hF _ _ (lineChain_ends D he).1 (lineChain_ends D he).2
  rw [himg, ← hseg]
  rcases param_dich (hin e he) with h | h
  · left; exact Set.image_mono h
  · right
    rw [← Set.image_inter (AffineMap.lineMap_injective ℝ hQF)]
    exact h.image _
structure TermSeg (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (Q R : Plane) : Prop where
  ne : Q ≠ R
  hg : g ≠ 0
  hQ : g Q = c
  hR : g R = c
  int : openSegment ℝ Q R ⊆ interior D.target.carrier
  wall : ∀ y ∈ openSegment ℝ Q R, ∀ i, y ∉ interior (D.tile i).carrier
  dich₁ : ∀ e ∈ D.lineChain g c, (D.tile e.1).edge e.2 ⊆ segment ℝ Q R ∨
    ((D.tile e.1).edge e.2 ∩ segment ℝ Q R).Subsingleton
  dich₂ : ∀ e ∈ D.lineChain (-g) (-c), (D.tile e.1).edge e.2 ⊆ segment ℝ Q R ∨
    ((D.tile e.1).edge e.2 ∩ segment ℝ Q R).Subsingleton
open Classical in
noncomputable def sideEdges (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (Q R : Plane) : Finset (Fin N × Fin 3) :=
  (D.lineChain g c).filter fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ Q R
theorem segment_level {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {Q R : Plane} (hQ : g Q = c) (hR : g R = c) :
    segment ℝ Q R ⊆ {y | g y = c} := by
  rintro _ ⟨s, t, -, -, hst, rfl⟩
  simp only [Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul, hQ, hR]
  rw [← add_mul, hst, one_mul]
theorem TermSeg.sums {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} {Q R : Plane} (h : TermSeg D g c Q R) :
    ∑ e ∈ sideEdges D g c Q R, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = dist Q R ∧
    ∑ e ∈ sideEdges D (-g) (-c) Q R, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = dist Q R := by
  classical
  have hnQ : (-g) Q = -c := by simp [h.hQ]
  have hnR : (-g) R = -c := by simp [h.hR]
  refine ⟨?_, ?_⟩
  · unfold sideEdges
    convert wall_sum D g c h.hg h.ne (segment_level h.hQ h.hR) h.int h.wall h.dich₁
  · unfold sideEdges
    convert wall_sum D (-g) (-c) (neg_ne_zero.mpr h.hg) h.ne (segment_level hnQ hnR) h.int h.wall
      h.dich₂
def WallRel : Prop :=
  ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ) (Q R : Plane), TermSeg D g c Q R ∧
    (∀ e ∈ sideEdges D g c Q R, isθ e) ∧ ∃ e ∈ sideEdges D (-g) (-c) Q R, ¬ isθ e
theorem relation_of_wallRel (h : WallRel D isθ) :
    ∃ s₁ s₂ : Finset (Fin N × Fin 3), (∀ e ∈ s₁, isθ e) ∧ (∃ e ∈ s₂, ¬ isθ e) ∧
      ∑ e ∈ s₁, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = ∑ e ∈ s₂, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
  obtain ⟨g, c, Q, R, ht, h1, h2⟩ := h
  exact ⟨_, _, h1, h2, ht.sums.1.trans ht.sums.2.symm⟩
set_option maxHeartbeats 4000000 in
open Classical in
theorem extend_link_wall {Q : Plane} {e₁ e₂ : Fin N × Fin 3} (he₁ : e₁ ∈ edgesAt D Q)
    (he₂ : e₂ ∈ edgesAt D Q) (hne : e₂ ≠ e₁) (hray : SameRayAt D Q e₁ e₂)
    (hθ₁ : isθ e₁) (hθ₂ : ¬ isθ e₂)
    (hback : ∀ e : Fin N × Fin 3, Q ∈ (D.tile e.1).edge e.2 →
      ∀ y ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ y (farEnd D Q e₁)) :
    (∃ R, IsLink D isθ Q R) ∨ WallRel D isθ := by
  obtain ⟨g, c, t₂, hg, hQ, hF, h1, h2, ht₂, hF₂⟩ := pair_line D he₁ he₂ hne hray
  set F := farEnd D Q e₁ with hFdef
  have hQF : Q ≠ F := (farEnd_ne D he₁).symm
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  have hnQ : (-g) Q = -c := by simp [hQ]
  have hnF : (-g) F = -c := by simp only [LinearMap.neg_apply, hF]
  have hQ0 : AffineMap.lineMap Q F (0 : ℝ) = Q := AffineMap.lineMap_apply_zero Q F
  have mem₁ : ∀ e ∈ D.lineChain g c, ∀ t, AffineMap.lineMap Q F t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) :=
    fun e he t => chain_mem_edge_iff D hg hQF hQ hF he t
  have mem₂ : ∀ e ∈ D.lineChain (-g) (-c), ∀ t,
      AffineMap.lineMap Q F t ∈ (D.tile e.1).edge e.2 ↔
        t ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) :=
    fun e he t => chain_mem_edge_iff D hng hQF hnQ hnF he t
  have lt₁ : ∀ e ∈ D.lineChain g c, edgeLo Q F (D.tile e.1) e.2 < edgeHi Q F (D.tile e.1) e.2 :=
    fun e he => chain_lo_lt_hi D hg hQF hQ hF he
  have ov₁ : ∀ e ∈ D.lineChain g c, ∀ e' ∈ D.lineChain g c,
      max (edgeLo Q F (D.tile e.1) e.2) (edgeLo Q F (D.tile e'.1) e'.2)
        < min (edgeHi Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e'.1) e'.2) → e = e' :=
    fun e he e' he' h => lineChain_eq_of_overlap D hg hQF hQ hF he he' h
  have ov₂ : ∀ e ∈ D.lineChain (-g) (-c), ∀ e' ∈ D.lineChain (-g) (-c),
      max (edgeLo Q F (D.tile e.1) e.2) (edgeLo Q F (D.tile e'.1) e'.2)
        < min (edgeHi Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e'.1) e'.2) → e = e' :=
    fun e he e' he' h => lineChain_eq_of_overlap D hng hQF hnQ hnF he he' h
  obtain ⟨p₁lo, p₁hi⟩ := edgesAt_params D hQF he₁ one_pos (AffineMap.lineMap_apply_one Q F).symm
  obtain ⟨p₂lo, p₂hi⟩ := edgesAt_params D hQF he₂ ht₂ hF₂
  have back : ∀ e : Fin N × Fin 3, (∀ t, AffineMap.lineMap Q F t ∈ (D.tile e.1).edge e.2 ↔
      t ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2)) →
      edgeLo Q F (D.tile e.1) e.2 < 0 → edgeHi Q F (D.tile e.1) e.2 < 0 := by
    intro e hmem hlo
    by_contra hhi
    push Not at hhi
    have hQe : Q ∈ (D.tile e.1).edge e.2 := by
      have := (hmem 0).mpr ⟨hlo.le, hhi⟩
      rwa [hQ0] at this
    refine hback e hQe _ ((hmem _).mpr ⟨le_rfl, (hlo.trans_le hhi).le⟩) ?_
    have := (lineMap_mem_openSegment_params hQF (a := edgeLo Q F (D.tile e.1) e.2) (b := 1)
      (t := 0)).mpr (by rw [openSegment_eq_Ioo (hlo.trans one_pos)]; exact ⟨hlo, one_pos⟩)
    rwa [hQ0, AffineMap.lineMap_apply_one] at this
  let Good : ℝ → Prop := fun t => 0 < t ∧ ∀ x ∈ Icc (0 : ℝ) t, ∃ e ∈ D.lineChain g c, isθ e ∧
    0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ t ∧
    x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2)
  have good1 : Good 1 :=
    ⟨one_pos, fun x hx => ⟨e₁, h1, hθ₁, p₁lo.ge, p₁hi.le, by rw [p₁lo, p₁hi]; exact hx⟩⟩
  set Cand := ((D.lineChain g c).image fun e => edgeHi Q F (D.tile e.1) e.2).filter Good
  have h1C : (1 : ℝ) ∈ Cand := Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e₁, h1, p₁hi⟩, good1⟩
  set T := Cand.max' ⟨1, h1C⟩ with hTdef
  have hTgood : Good T := (Finset.mem_filter.mp (Finset.max'_mem Cand ⟨1, h1C⟩)).2
  have hTpos : 0 < T := hTgood.1
  have hmax : ∀ t, Good t → t ∈ (D.lineChain g c).image (fun e => edgeHi Q F (D.tile e.1) e.2) →
      t ≤ T := fun t ht hti => Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hti, ht⟩)
  have inner₁ : ∀ e ∈ D.lineChain g c, ∀ x ∈ Ioo 0 T,
      x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
        isθ e ∧ 0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T := by
    intro e he x hx hxe
    set S := (D.lineChain g c).filter fun e => isθ e ∧ 0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧
      edgeHi Q F (D.tile e.1) e.2 ≤ T
    have hcovS : ∀ y ∈ Icc 0 T, ∃ e' ∈ S,
        y ∈ Icc (edgeLo Q F (D.tile e'.1) e'.2) (edgeHi Q F (D.tile e'.1) e'.2) := by
      intro y hy
      obtain ⟨e', he', hθ', hlo', hhi', hye'⟩ := hTgood.2 y hy
      exact ⟨e', Finset.mem_filter.mpr ⟨he', hθ', hlo', hhi'⟩, hye'⟩
    suffices hS : e ∈ S from (Finset.mem_filter.mp hS).2
    rcases hxe.2.lt_or_eq with hxhi | hxhi
    · obtain ⟨e', he', hlo', hhi'⟩ := exists_interval_right S
        (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) x
        (δ₀ := T - x) (by linarith [hx.2]) Set.finite_empty
        (fun y hy _ => hcovS y ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩)
      have : e = e' := ov₁ e he e' (Finset.mem_filter.mp he').1
        (lt_of_le_of_lt (max_le hxe.1 hlo') (lt_min hxhi hhi'))
      rw [this]; exact he'
    · obtain ⟨e', he', hlo', hhi'⟩ := exists_interval_left S
        (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) x
        (δ₀ := x) hx.1 Set.finite_empty
        (fun y hy _ => hcovS y ⟨by linarith [hy.1], by linarith [hy.2, hx.2]⟩)
      have : e = e' := ov₁ e he e' (Finset.mem_filter.mp he').1
        (lt_of_lt_of_le (max_lt (by rw [hxhi]; exact lt₁ e he) hlo') (le_min hxhi.le hhi'))
      rw [this]; exact he'
  set R := AffineMap.lineMap Q F T with hRdef
  have hOS : openSegment ℝ Q R = AffineMap.lineMap Q F '' Ioo 0 T := by
    rw [← openSegment_eq_Ioo hTpos, image_openSegment, hQ0]
  have hSeg : segment ℝ Q R = AffineMap.lineMap Q F '' Icc 0 T := by
    rw [← segment_eq_Icc hTpos.le, image_segment, hQ0]
  have hQR : Q ≠ R := by
    intro h
    have : AffineMap.lineMap Q F (0 : ℝ) = AffineMap.lineMap Q F T := by rw [hQ0]; exact h
    exact hTpos.ne (AffineMap.lineMap_injective ℝ hQF this)
  have hRc : g R = c := level_lineMap hQ hF T
  obtain ⟨eR, heR, -, -, heRhi, heRT⟩ := hTgood.2 T ⟨hTpos.le, le_rfl⟩
  have hRhi : edgeHi Q F (D.tile eR.1) eR.2 = T := le_antisymm heRhi heRT.2
  obtain ⟨kR, hkR⟩ := exists_pts_eq_hi D hg hQF hQ hF heR
  rw [hRhi] at hkR
  have hRt : R ∈ D.target.carrier := by
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨eR.1, (D.tile eR.1).edge_subset_carrier eR.2 ((mem₁ eR heR T).mpr heRT)⟩
  have hT12 : e₁.1 ≠ e₂.1 := tile_ne_of_chains D hg h1 h2
  have near : ∀ τ : ℝ, 0 < τ → τ < 1 → τ < t₂ →
      AffineMap.lineMap Q F τ ∈ interior D.target.carrier := by
    intro τ h0 h1' h2'
    obtain ⟨a1, a2⟩ := lineChain_ends D h1
    obtain ⟨b1, b2⟩ := lineChain_ends D h2
    have ha := (lineMap_mem_openSegment_iff hg hQF hQ hF _ _ a1 a2 τ).mpr
      (by rw [p₁lo, p₁hi]; exact ⟨h0, h1'⟩)
    have hb := (lineMap_mem_openSegment_iff hng hQF hnQ hnF _ _ b1 b2 τ).mpr
      (by rw [p₂lo, p₂hi]; exact ⟨h0, h2'⟩)
    exact interior_of_two_openSegment D hT12 ha hb
  have hint : openSegment ℝ Q R ⊆ interior D.target.carrier := by
    rw [hOS]
    rintro _ ⟨x, hx, rfl⟩
    set τ := min (min x 1) t₂ / 2
    have hm : 0 < min (min x 1) t₂ := lt_min (lt_min hx.1 one_pos) ht₂
    have hτ0 : 0 < τ := by simp only [τ]; linarith
    have hτx : τ < x := by
      have := min_le_left (min x 1) t₂; have := min_le_left x 1; simp only [τ]; linarith
    have hτ1 : τ < 1 := by
      have := min_le_left (min x 1) t₂; have := min_le_right x 1; simp only [τ]; linarith
    have hτ2 : τ < t₂ := by
      have := min_le_right (min x 1) t₂; simp only [τ]; linarith
    have hxin : AffineMap.lineMap Q F x ∈ openSegment ℝ (AffineMap.lineMap Q F τ) R :=
      (lineMap_mem_openSegment_params hQF).mpr
        (by rw [openSegment_eq_Ioo (hτx.trans hx.2)]; exact ⟨hτx, hx.2⟩)
    exact D.target.convex.openSegment_interior_closure_subset_interior (near τ hτ0 hτ1 hτ2)
      (subset_closure hRt) hxin
  have hwall : ∀ y ∈ openSegment ℝ Q R, ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    rw [hOS] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨e, he, -, -, -, hxe⟩ := hTgood.2 x ⟨hx.1.le, hx.2.le⟩
    exact D.edge_point_not_interior ((mem₁ e he x).mpr hxe)
  have hint0 : openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F T)
      ⊆ interior D.target.carrier := by rw [hQ0]; exact hint
  have hwall0 : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q F (0 : ℝ)) (AffineMap.lineMap Q F T),
      ∀ i, y ∉ interior (D.tile i).carrier := by rw [hQ0]; exact hwall
  obtain ⟨ε, hε, hεlo, hεhi⟩ := exists_interval_left (D.lineChain (-g) (-c))
    (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) T
    hTpos (vertex_params_finite D hQF) (fun y hy hyv => by
      rw [sub_self] at hy
      exact wall_cover_param D hng hQF hnQ hnF hTpos hint0 hwall0 hy hyv)
  rcases hεhi.lt_or_eq with hεhi | hεhi
  · 
    left
    refine ⟨R, g, c, ⟨hQR, hg, hQ, hRc, ?_, ?_, ?_, ?_, ?_⟩⟩
    · intro y hy
      rw [hOS] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      obtain ⟨e, he, -, -, -, hxe⟩ := hTgood.2 x ⟨hx.1.le, hx.2.le⟩
      exact ⟨e, he, (mem₁ e he x).mpr hxe⟩
    · intro e he hmeet
      obtain ⟨y, hye, hyo⟩ := hmeet
      rw [hOS] at hyo
      obtain ⟨x, hx, rfl⟩ := hyo
      obtain ⟨hθ, hlo, hhi⟩ := inner₁ e he x hx ((mem₁ e he x).mp hye)
      refine ⟨?_, hθ⟩
      rw [edge_eq_image hg hQF hQ hF _ _ (lineChain_ends D he).1 (lineChain_ends D he).2, hSeg]
      exact Set.image_mono fun z hz => ⟨hlo.trans hz.1, hz.2.trans hhi⟩
    · intro e he _ hQe y hy hQy
      have hgy : g y = c := D.lineChain_edge_subset he y hy
      obtain ⟨s, rfl⟩ : ∃ s, AffineMap.lineMap Q F s = y :=
        ⟨_, eq_lineMap_lineParam hg hQF hQ hF hgy⟩
      have hs : s < 0 := by
        have hQy' : AffineMap.lineMap Q F (0 : ℝ) ∈
            openSegment ℝ (AffineMap.lineMap Q F s) (AffineMap.lineMap Q F T) := by
          rw [hQ0]; exact hQy
        have h0 := (lineMap_mem_openSegment_params hQF (a := s) (b := T) (t := 0)).mp hQy'
        rcases lt_trichotomy s T with h | h | h
        · rw [openSegment_eq_Ioo h] at h0; exact h0.1
        · rw [h, openSegment_same] at h0; exact absurd (Set.mem_singleton_iff.mp h0) hTpos.ne
        · rw [openSegment_symm, openSegment_eq_Ioo h] at h0; linarith [h0.1]
      refine hback e hQe _ hy ?_
      have := (lineMap_mem_openSegment_params hQF (a := s) (b := 1) (t := 0)).mpr
        (by rw [openSegment_eq_Ioo (hs.trans one_pos)]; exact ⟨hs, one_pos⟩)
      rwa [hQ0, AffineMap.lineMap_apply_one] at this
    · 
      have hRint : R ∈ interior D.target.carrier := by
        obtain ⟨b1, b2⟩ := lineChain_ends D hε
        have hRε := (lineMap_mem_openSegment_iff hng hQF hnQ hnF _ _ b1 b2 T).mpr ⟨hεlo, hεhi⟩
        exact interior_of_vertex_openSegment D hkR hRε
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior R hRint
      have hdQF : 0 < dist Q F := dist_pos.mpr hQF
      set δ₁ := min (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F) / 2 with hδ₁def
      have hδ₁ : 0 < δ₁ := by
        have : 0 < min (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F) :=
          lt_min (by linarith) (div_pos hr hdQF)
        simp only [δ₁]; linarith
      have hδ₁ε : T + δ₁ < edgeHi Q F (D.tile ε.1) ε.2 := by
        have := min_le_left (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F)
        simp only [δ₁]; linarith
      have hδ₁r : δ₁ * dist Q F < r := by
        have h := min_le_right (edgeHi Q F (D.tile ε.1) ε.2 - T) (r / dist Q F)
        have : δ₁ < r / dist Q F := by simp only [δ₁]; linarith [div_pos hr hdQF]
        calc δ₁ * dist Q F < r / dist Q F * dist Q F := mul_lt_mul_of_pos_right this hdQF
          _ = r := div_mul_cancel₀ r hdQF.ne'
      have hint' : openSegment ℝ (AffineMap.lineMap Q F T) (AffineMap.lineMap Q F (T + δ₁))
          ⊆ interior D.target.carrier := by
        rw [← image_openSegment, openSegment_eq_Ioo (by linarith)]
        rintro _ ⟨s, hs, rfl⟩
        apply hball
        rw [Metric.mem_ball, hRdef, dist_lineMap_lineMap, Real.dist_eq, abs_of_pos (by linarith [hs.1])]
        calc (s - T) * dist Q F < δ₁ * dist Q F :=
              mul_lt_mul_of_pos_right (by linarith [hs.2]) hdQF
          _ < r := hδ₁r
      have hwall' : ∀ y ∈ openSegment ℝ (AffineMap.lineMap Q F T)
          (AffineMap.lineMap Q F (T + δ₁)), ∀ i, y ∉ interior (D.tile i).carrier := by
        rw [← image_openSegment, openSegment_eq_Ioo (by linarith)]
        rintro _ ⟨s, hs, rfl⟩
        exact D.edge_point_not_interior ((mem₂ ε hε s).mpr
          ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      obtain ⟨e', he', hlo', hhi'⟩ := exists_interval_right (D.lineChain g c)
        (fun e => edgeLo Q F (D.tile e.1) e.2) (fun e => edgeHi Q F (D.tile e.1) e.2) T
        hδ₁ (vertex_params_finite D hQF)
        (fun y hy hyv => wall_cover_param D hg hQF hQ hF (by linarith) hint' hwall' hy hyv)
      have hθ' : ¬ isθ e' := by
        intro hθ'
        rcases hlo'.lt_or_eq with hlt | heq
        · set m := max (edgeLo Q F (D.tile e'.1) e'.2) 0
          have hm : m < T := max_lt hlt hTpos
          have := (inner₁ e' he' ((m + T) / 2)
            ⟨by linarith [le_max_right (edgeLo Q F (D.tile e'.1) e'.2) 0], by linarith⟩
            ⟨by linarith [le_max_left (edgeLo Q F (D.tile e'.1) e'.2) 0], by linarith⟩).2.2
          linarith
        · have hgood : Good (edgeHi Q F (D.tile e'.1) e'.2) := by
            refine ⟨hTpos.trans hhi', fun x hx => ?_⟩
            rcases le_or_gt x T with hxT | hxT
            · obtain ⟨e, he, hθ, h0, hT', hxe⟩ := hTgood.2 x ⟨hx.1, hxT⟩
              exact ⟨e, he, hθ, h0, hT'.trans hhi'.le, hxe⟩
            · exact ⟨e', he', hθ', by rw [heq]; exact hTpos.le, le_rfl,
                ⟨by rw [heq]; exact hxT.le, hx.2⟩⟩
          have := hmax _ hgood (Finset.mem_image.mpr ⟨e', he', rfl⟩)
          linarith
      refine ⟨e', he', hθ', (mem₁ e' he' T).mpr ⟨hlo', hhi'.le⟩,
        AffineMap.lineMap Q F (edgeHi Q F (D.tile e'.1) e'.2),
        (mem₁ e' he' _).mpr ⟨(hlo'.trans hhi'.le), le_rfl⟩, ?_⟩
      have := (lineMap_mem_openSegment_params hQF (a := 0)
        (b := edgeHi Q F (D.tile e'.1) e'.2) (t := T)).mpr
        (by rw [openSegment_eq_Ioo (hTpos.trans hhi')]; exact ⟨hTpos, hhi'⟩)
      rwa [hQ0] at this
    · obtain ⟨b1, b2⟩ := lineChain_ends D hε
      exact ⟨ε, hε, (lineMap_mem_openSegment_iff hng hQF hnQ hnF _ _ b1 b2 T).mpr ⟨hεlo, hεhi⟩⟩
  · 
    right
    have inner₂ : ∀ e ∈ D.lineChain (-g) (-c), ∀ x ∈ Ioo 0 T,
        x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
          0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T := by
      intro e he x hx hxe
      constructor
      · by_contra hlo
        push Not at hlo
        have := back e (mem₂ e he) hlo
        linarith [hxe.2, hx.1]
      · by_contra hhi
        push Not at hhi
        have := ov₂ e he ε hε (lt_of_lt_of_le
          (max_lt (lt_of_le_of_lt hxe.1 hx.2) hεlo) (le_min hhi.le hεhi.le))
        rw [this] at hhi
        linarith
    have hin₁ : ∀ e ∈ D.lineChain g c, ∀ x ∈ Ioo 0 T,
        x ∈ Icc (edgeLo Q F (D.tile e.1) e.2) (edgeHi Q F (D.tile e.1) e.2) →
          0 ≤ edgeLo Q F (D.tile e.1) e.2 ∧ edgeHi Q F (D.tile e.1) e.2 ≤ T :=
      fun e he x hx hxe => (inner₁ e he x hx hxe).2
    have d₁ := dich_of_param D hg hQF hQ hF hTpos hin₁
    have d₂ := dich_of_param D hng hQF hnQ hnF hTpos inner₂
    refine ⟨g, c, Q, R, ⟨hQR, hg, hQ, hRc, hint, hwall, d₁, d₂⟩, ?_, ⟨e₂, ?_, hθ₂⟩⟩
    · intro e he
      obtain ⟨he, hsub⟩ := Finset.mem_filter.mp he
      rw [edge_eq_image hg hQF hQ hF _ _ (lineChain_ends D he).1 (lineChain_ends D he).2,
        hSeg, Set.image_subset_image_iff (AffineMap.lineMap_injective ℝ hQF)] at hsub
      have hlt := lt₁ e he
      have hlo := (hsub ⟨le_rfl, hlt.le⟩).1
      have hhi := (hsub ⟨hlt.le, le_rfl⟩).2
      exact (inner₁ e he ((edgeLo Q F (D.tile e.1) e.2 + edgeHi Q F (D.tile e.1) e.2) / 2)
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩).1
    · refine Finset.mem_filter.mpr ⟨h2, ?_⟩
      have := (inner₂ e₂ h2 (min t₂ T / 2)
        ⟨by positivity, by linarith [min_le_right t₂ T]⟩
        (by rw [p₂lo, p₂hi]; exact ⟨by positivity, by linarith [min_le_left t₂ T]⟩)).2
      rw [p₂hi] at this
      rw [edge_eq_image hng hQF hnQ hnF _ _ (lineChain_ends D h2).1 (lineChain_ends D h2).2,
        hSeg, p₂lo, p₂hi]
      exact Set.image_mono fun z hz => ⟨hz.1, hz.2.trans this⟩
open Classical in
theorem extend_link {Q : Plane} {e₁ e₂ : Fin N × Fin 3} (he₁ : e₁ ∈ edgesAt D Q)
    (he₂ : e₂ ∈ edgesAt D Q) (hne : e₂ ≠ e₁) (hray : SameRayAt D Q e₁ e₂)
    (hθ₁ : isθ e₁) (hθ₂ : ¬ isθ e₂)
    (hback : ∀ e : Fin N × Fin 3, Q ∈ (D.tile e.1).edge e.2 →
      ∀ y ∈ (D.tile e.1).edge e.2, Q ∉ openSegment ℝ y (farEnd D Q e₁)) :
    (∃ R, IsLink D isθ Q R) ∨
    ∃ s₁ s₂ : Finset (Fin N × Fin 3), (∀ e ∈ s₁, isθ e) ∧ (∃ e ∈ s₂, ¬ isθ e) ∧
      ∑ e ∈ s₁, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
        = ∑ e ∈ s₂, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) :=
  (extend_link_wall D isθ he₁ he₂ hne hray hθ₁ hθ₂ hback).imp id (relation_of_wallRel D isθ)
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} {D : Dissection N} {isθ : Fin N × Fin 3 → Prop}
theorem exists_pts_eq_lo (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0)
    {Q F : Plane} (hQF : Q ≠ F) (hQ : g Q = c) (hF : g F = c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) :
    ∃ k : Fin 3, (D.tile e.1).pts k = AffineMap.lineMap Q F (edgeLo Q F (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  rcases min_choice (lineParam Q F ((D.tile e.1).pts e.2))
    (lineParam Q F ((D.tile e.1).pts (e.2 + 1))) with hm | hm
  · exact ⟨e.2, by rw [edgeLo, hm, eq_lineMap_lineParam hg hQF hQ hF n1]⟩
  · exact ⟨e.2 + 1, by rw [edgeLo, hm, eq_lineMap_lineParam hg hQF hQ hF n2]⟩
theorem lineMap_params {Q R : Plane} (a b t : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap Q R a) (AffineMap.lineMap Q R b) t
      = AffineMap.lineMap Q R (a + t * (b - a)) := by
  simp only [AffineMap.lineMap_apply_module']
  rw [show (b • (R - Q) + Q) - (a • (R - Q) + Q) = (b - a) • (R - Q) by
    rw [sub_smul]; abel]
  rw [smul_smul, add_smul]
  abel
theorem chain_iff {g₁ g₂ : Plane →ₗ[ℝ] ℝ} {c₁ c₂ : ℝ} (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {ε : Fin N × Fin 3} (h₁ : ε ∈ D.lineChain (-g₁) (-c₁)) (h₂ : ε ∈ D.lineChain (-g₂) (-c₂))
    (e : Fin N × Fin 3) : e ∈ D.lineChain g₁ c₁ ↔ e ∈ D.lineChain g₂ c₂ :=
  ⟨(chain_transfer D hg₂ hg₁ h₂ h₁).2 e, (chain_transfer D hg₁ hg₂ h₁ h₂).2 e⟩
theorem chain_coord {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c)) :
    0 < g ((D.tile ε.1).pts (ε.2 + 2)) - c ∧ ∀ z, g z - c =
      (D.tile ε.1).basis.coord (ε.2 + 2) z * (g ((D.tile ε.1).pts (ε.2 + 2)) - c) := by
  obtain ⟨a1, a2, a3⟩ := Dissection.mem_lineChain.mp hε
  simp only [LinearMap.neg_apply, neg_inj] at a1 a2
  have b3 := a3 (ε.2 + 2)
  simp only [LinearMap.neg_apply, neg_le_neg_iff] at b3
  have i1 : ∀ m : Fin 3, m + 2 + 1 = m := by decide
  have i2 : ∀ m : Fin 3, m + 2 + 2 = m + 1 := by decide
  refine ⟨sub_pos.mpr (lt_of_le_of_ne b3 (Ne.symm (third_off_line _ hg ε.2 a1 a2))), fun z => ?_⟩
  exact level_eq_coord _ g c (ε.2 + 2) (by rw [i1]; exact a1) (by rw [i2]; exact a2) z
theorem end_param_at (D : Dissection N) {Q W : Plane} (hQW : Q ≠ W) {q : ℝ} {e : Fin N × Fin 3}
    (he : e ∈ edgesAt D (AffineMap.lineMap Q W q)) :
    edgeLo Q W (D.tile e.1) e.2 = q ∨ edgeHi Q W (D.tile e.1) e.2 = q := by
  have hq : lineParam Q W (AffineMap.lineMap Q W q) = q := lineParam_lineMap hQW q
  rcases (mem_edgesAt D).mp he with h1 | h1
  · rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with h2 | h2
    · left; rw [edgeLo, min_eq_left h2, h1, hq]
    · right; rw [edgeHi, max_eq_left h2, h1, hq]
  · rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with h2 | h2
    · right; rw [edgeHi, max_eq_right h2, h1, hq]
    · left; rw [edgeLo, min_eq_right h2, h1, hq]
theorem edgesAt_of_hi (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q W : Plane}
    (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) {q : ℝ} (hhi : edgeHi Q W (D.tile e.1) e.2 = q) :
    e ∈ edgesAt D (AffineMap.lineMap Q W q) ∧
      farEnd D (AffineMap.lineMap Q W q) e = AffineMap.lineMap Q W (edgeLo Q W (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  have e1 := eq_lineMap_lineParam hg hQW hQ hW n1
  have e2 := eq_lineMap_lineParam hg hQW hQ hW n2
  rw [edgeHi] at hhi
  rw [edgeLo]
  rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with hle | hle
  · rw [max_eq_right hle] at hhi
    rw [min_eq_left hle]
    have hR : (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap Q W q := by rw [← e2, hhi]
    have hne : (D.tile e.1).pts e.2 ≠ AffineMap.lineMap Q W q := fun h0 =>
      tri_pts_succ_ne (D.tile e.1) e.2 (h0.trans hR.symm)
    exact ⟨(mem_edgesAt D).mpr (Or.inr hR), by rw [farEnd, if_neg hne, e1]⟩
  · rw [max_eq_left hle] at hhi
    rw [min_eq_right hle]
    have hR : (D.tile e.1).pts e.2 = AffineMap.lineMap Q W q := by rw [← e1, hhi]
    exact ⟨(mem_edgesAt D).mpr (Or.inl hR), by rw [farEnd, if_pos hR, e2]⟩
theorem edgesAt_of_lo (D : Dissection N) {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) {Q W : Plane}
    (hQW : Q ≠ W) (hQ : g Q = c) (hW : g W = c) {e : Fin N × Fin 3}
    (he : e ∈ D.lineChain g c) {q : ℝ} (hlo : edgeLo Q W (D.tile e.1) e.2 = q) :
    e ∈ edgesAt D (AffineMap.lineMap Q W q) ∧
      farEnd D (AffineMap.lineMap Q W q) e = AffineMap.lineMap Q W (edgeHi Q W (D.tile e.1) e.2) := by
  obtain ⟨n1, n2⟩ := lineChain_ends D he
  have e1 := eq_lineMap_lineParam hg hQW hQ hW n1
  have e2 := eq_lineMap_lineParam hg hQW hQ hW n2
  rw [edgeLo] at hlo
  rw [edgeHi]
  rcases le_total (lineParam Q W ((D.tile e.1).pts e.2))
      (lineParam Q W ((D.tile e.1).pts (e.2 + 1))) with hle | hle
  · rw [min_eq_left hle] at hlo
    rw [max_eq_right hle]
    have hR : (D.tile e.1).pts e.2 = AffineMap.lineMap Q W q := by rw [← e1, hlo]
    exact ⟨(mem_edgesAt D).mpr (Or.inl hR), by rw [farEnd, if_pos hR, e2]⟩
  · rw [min_eq_right hle] at hlo
    rw [max_eq_left hle]
    have hR : (D.tile e.1).pts (e.2 + 1) = AffineMap.lineMap Q W q := by rw [← e2, hlo]
    have hne : (D.tile e.1).pts e.2 ≠ AffineMap.lineMap Q W q := fun h0 =>
      tri_pts_succ_ne (D.tile e.1) e.2 (h0.trans hR.symm)
    exact ⟨(mem_edgesAt D).mpr (Or.inr hR), by rw [farEnd, if_neg hne, e1]⟩
theorem lonely_relint (D : Dissection N) {Q : Plane} (hQ : Q ∈ interior D.target.carrier) {e : Fin N × Fin 3}
    (he : e ∈ edgesAt D Q) (hlonely : ∀ e' ∈ edgesAt D Q, e' ≠ e → ¬ SameRayAt D Q e e') :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧ g (farEnd D Q e) = c ∧
      e ∈ D.lineChain g c ∧ ∃ e₂ ∈ D.lineChain (-g) (-c),
        Q ∈ openSegment ℝ ((D.tile e₂.1).pts e₂.2) ((D.tile e₂.1).pts (e₂.2 + 1)) := by
  set F := farEnd D Q e
  have hQF : Q ≠ F := (farEnd_ne D he).symm
  obtain ⟨g₀, c₀, hg₀, hQ₀, hF₀⟩ := ray_level (farEnd_ne D he)
  obtain ⟨g, c, hg, hgQ, hgF, hec⟩ : ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g Q = c ∧
      g F = c ∧ e ∈ D.lineChain g c := by
    rcases edgesAt_chain D he hQ₀ hF₀ with h' | h'
    · exact ⟨g₀, c₀, hg₀, hQ₀, hF₀, h'⟩
    · exact ⟨-g₀, -c₀, neg_ne_zero.mpr hg₀, by simp [hQ₀],
        by simp only [LinearMap.neg_apply, F, hF₀], h'⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior Q hQ
  have hdQF : 0 < dist Q F := dist_pos.mpr hQF
  set τ := min (1 / 2) (r / (2 * dist Q F))
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hint : AffineMap.lineMap Q F τ ∈ interior D.target.carrier := by
    apply hball
    rw [Metric.mem_ball, dist_lineMap_left, Real.norm_eq_abs, abs_of_pos hτ0]
    have : τ ≤ r / (2 * dist Q F) := min_le_right _ _
    calc τ * dist Q F ≤ r / (2 * dist Q F) * dist Q F :=
          mul_le_mul_of_nonneg_right this hdQF.le
      _ = r / 2 := by field_simp
      _ < r := by linarith
  exact ⟨g, c, hg, hgQ, hgF, hec, lonely_openSegment D he hg hgQ hgF hec hlonely ⟨hτ0, hτ1⟩ hint⟩
namespace LinkData
variable {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
theorem start_vertex (h : LinkData D isθ Q R g c) : ∃ i k, (D.tile i).pts k = Q := by
  obtain ⟨e, he, hlo, hhi⟩ := exists_interval_right (D.lineChain g c)
    (fun x => edgeLo Q R (D.tile x.1) x.2) (fun x => edgeHi Q R (D.tile x.1) x.2) 0
    one_pos Set.finite_empty (fun y hy _ => by
      rw [zero_add] at hy
      obtain ⟨e, he, hye⟩ := h.cov _ (openSegment_param.mpr ⟨y, hy, rfl⟩)
      exact ⟨e, he, (h.mem_edge_iff he y).mp hye⟩)
  have hm : 0 < min (edgeHi Q R (D.tile e.1) e.2) 1 := lt_min hhi one_pos
  have hmeet : ((D.tile e.1).edge e.2 ∩ openSegment ℝ Q R).Nonempty := by
    refine ⟨AffineMap.lineMap Q R (min (edgeHi Q R (D.tile e.1) e.2) 1 / 2),
      (h.mem_edge_iff he _).mpr ⟨?_, ?_⟩, openSegment_param.mpr ⟨_, ⟨?_, ?_⟩, rfl⟩⟩
    · linarith
    · linarith [min_le_left (edgeHi Q R (D.tile e.1) e.2) 1]
    · linarith
    · linarith [min_le_right (edgeHi Q R (D.tile e.1) e.2) 1]
  obtain ⟨hsub, -⟩ := h.inner e he hmeet
  have h0 := (h.params_of_inner he hsub).1
  obtain ⟨k, hk⟩ := exists_pts_eq_lo D h.hg h.ne h.hQ h.hR he
  exact ⟨e.1, k, by rw [hk, le_antisymm hlo h0, AffineMap.lineMap_apply_zero]⟩
theorem tiles_side (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    {i : Fin N} (hi : i ≠ ε.1) (hRi : R ∈ (D.tile i).carrier) :
    ∀ z ∈ (D.tile i).carrier, g z ≤ c := by
  intro z hz
  have h1 := tile_side_of_openSegment D hRε hi hRi z hz
  obtain ⟨hpos, hcoord⟩ := chain_coord h.hg hε
  have := hcoord z
  nlinarith
theorem end_param (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3} (he : e ∈ edgesAt D R) :
    edgeLo Q R (D.tile e.1) e.2 = 1 ∨ edgeHi Q R (D.tile e.1) e.2 = 1 := by
  rw [← AffineMap.lineMap_apply_one (k := ℝ) Q R] at he
  exact end_param_at D h.ne he
end LinkData
theorem edgesAt_params' {Q W R : Plane} (hQW : Q ≠ W) {e : Fin N × Fin 3}
    (he : e ∈ edgesAt D R) {r p : ℝ} (hR : R = AffineMap.lineMap Q W r)
    (hfar : farEnd D R e = AffineMap.lineMap Q W p) :
    edgeLo Q W (D.tile e.1) e.2 = min r p ∧ edgeHi Q W (D.tile e.1) e.2 = max r p := by
  have hr : lineParam Q W R = r := by rw [hR, lineParam_lineMap hQW]
  have hp : lineParam Q W (farEnd D R e) = p := by rw [hfar, lineParam_lineMap hQW]
  rw [edgeLo, edgeHi]
  rcases edgesAt_ends D he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hr, hp]; exact ⟨rfl, rfl⟩
  · rw [h1, h2, hr, hp, min_comm, max_comm]; exact ⟨rfl, rfl⟩
namespace LinkData
variable {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ}
theorem eps_params (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1))) :
    edgeLo Q R (D.tile ε.1) ε.2 < 1 ∧ 1 < edgeHi Q R (D.tile ε.1) ε.2 := by
  have hng : -g ≠ 0 := neg_ne_zero.mpr h.hg
  have hnQ : (-g) Q = -c := by simp [h.hQ]
  have hnR : (-g) R = -c := by simp [h.hR]
  obtain ⟨b1, b2⟩ := lineChain_ends D hε
  have h1 : AffineMap.lineMap Q R (1 : ℝ) ∈
      openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)) := by
    rw [AffineMap.lineMap_apply_one]; exact hRε
  exact (lineMap_mem_openSegment_iff hng h.ne hnQ hnR _ _ b1 b2 1).mp h1
theorem not_side2 (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    {z : Fin N × Fin 3} (hz : z ∈ edgesAt D R) : z ∉ D.lineChain (-g) (-c) := by
  intro hz2
  have hng : -g ≠ 0 := neg_ne_zero.mpr h.hg
  have hnQ : (-g) Q = -c := by simp [h.hQ]
  have hnR : (-g) R = -c := by simp [h.hR]
  obtain ⟨hε1, hε2⟩ := h.eps_params hε hRε
  have hlt := chain_lo_lt_hi D hng h.ne hnQ hnR hz2
  rcases h.end_param hz with h1 | h1
  · have := lineChain_eq_of_overlap D hng h.ne hnQ hnR hz2 hε
      (lt_of_le_of_lt (max_le h1.le hε1.le) (lt_min (h1 ▸ hlt) hε2))
    rw [this] at h1
    linarith
  · have := lineChain_eq_of_overlap D hng h.ne hnQ hnR hz2 hε
      (lt_of_lt_of_le (max_lt (h1 ▸ hlt) hε1) (le_min h1.ge hε2.le))
    rw [this] at h1
    linarith
theorem far_le (h : LinkData D isθ Q R g c) {ε : Fin N × Fin 3}
    (hε : ε ∈ D.lineChain (-g) (-c))
    (hRε : R ∈ openSegment ℝ ((D.tile ε.1).pts ε.2) ((D.tile ε.1).pts (ε.2 + 1)))
    {x : Fin N × Fin 3} (hx : x ∈ edgesAt D R) : g (farEnd D R x) ≤ c := by
  have hRx : R ∈ (D.tile x.1).carrier := by
    have : R ∈ (D.tile x.1).edge x.2 := by rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
    exact (D.tile x.1).edge_subset_carrier x.2 this
  have hFx : farEnd D R x ∈ (D.tile x.1).carrier := by
    have : farEnd D R x ∈ (D.tile x.1).edge x.2 := by
      rw [edgesAt_edge D hx]; exact right_mem_segment ℝ _ _
    exact (D.tile x.1).edge_subset_carrier x.2 this
  have hne : x.1 ≠ ε.1 := by
    intro hxε
    rcases (mem_edgesAt D).mp hx with h1 | h1
    · have h2 : (D.tile ε.1).pts x.2 = R := by rw [← hxε]; exact h1
      exact Tri.vertex_not_mem_openSegment (D.tile ε.1) x.2 ε.2 (by rw [h2]; exact hRε)
    · have h2 : (D.tile ε.1).pts (x.2 + 1) = R := by rw [← hxε]; exact h1
      exact Tri.vertex_not_mem_openSegment (D.tile ε.1) (x.2 + 1) ε.2 (by rw [h2]; exact hRε)
  exact h.tiles_side hε hRε hne hRx _ hFx
theorem far_lt_of_partner (h : LinkData D isθ Q R g c) {x y : Fin N × Fin 3}
    (hx : x ∈ edgesAt D R) (hy : y ∈ edgesAt D R) (hxy : x ≠ y) (hray : SameRayAt D R x y) :
    g (farEnd D R x) < c := by
  obtain ⟨ε, hε, hRε⟩ := h.across
  rcases (h.far_le hε hRε hx).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨t, ht, hFy⟩ := hray
    set F := farEnd D R x
    have hgy : g (farEnd D R y) = c := by rw [hFy]; exact level_lineMap h.hR heq t
    have cx := edgesAt_chain D hx h.hR heq
    have cy := edgesAt_chain D hy h.hR hgy
    have nx := h.not_side2 hε hRε hx
    have ny := h.not_side2 hε hRε hy
    have cx' : x ∈ D.lineChain g c := cx.resolve_right nx
    have cy' : y ∈ D.lineChain g c := cy.resolve_right ny
    have hRF : R ≠ F := (farEnd_ne D hx).symm
    have hs : 0 < min 1 t := lt_min one_pos ht
    have hm1 := mem_edge_of_ray D hx (t := 1) (AffineMap.lineMap_apply_one R F).symm hs.le
      (min_le_left _ _)
    have hm2 := mem_edge_of_ray D hy hFy hs.le (min_le_right _ _)
    have hR1 : R ∈ (D.tile x.1).edge x.2 := by rw [edgesAt_edge D hx]; exact left_mem_segment ℝ _ _
    have hR2 : R ∈ (D.tile y.1).edge y.2 := by rw [edgesAt_edge D hy]; exact left_mem_segment ℝ _ _
    have hneq : R ≠ AffineMap.lineMap R F (min 1 t) := by
      intro h'
      have : AffineMap.lineMap R F (0 : ℝ) = AffineMap.lineMap R F (min 1 t) := by
        rw [AffineMap.lineMap_apply_zero]; exact h'
      exact hs.ne (AffineMap.lineMap_injective ℝ hRF this)
    exact hxy (lineChain_eq_of_two D h.hg cx' cy' hneq ⟨hR1, hR2⟩ ⟨hm1, hm2⟩)
theorem back_of_partner (h : LinkData D isθ Q R g c) {x y : Fin N × Fin 3}
    (hx : x ∈ edgesAt D R) (hy : y ∈ edgesAt D R) (hxy : x ≠ y) (hray : SameRayAt D R x y) :
    ∀ e : Fin N × Fin 3, R ∈ (D.tile e.1).edge e.2 →
      ∀ z ∈ (D.tile e.1).edge e.2, R ∉ openSegment ℝ z (farEnd D R x) := by
  intro e hRe z hz hRz
  obtain ⟨ε, hε, hRε⟩ := h.across
  have hlt := h.far_lt_of_partner hx hy hxy hray
  have hgz : c < g z := by
    obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hRz
    have hR := h.hR
    rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hR
    have key : a * (g z - c) = b * (c - g (farEnd D R x)) := by
      linear_combination hR - c * hab
    have := mul_pos hb (sub_pos.mpr hlt)
    by_contra hc
    push Not at hc
    nlinarith
  obtain ⟨hκ, hcoord⟩ := chain_coord h.hg hε
  have hcz : 0 < (D.tile ε.1).basis.coord (ε.2 + 2) z := by
    have := hcoord z
    by_contra hc
    push Not at hc
    nlinarith
  obtain ⟨τ0, hτ0, hint⟩ := Tri.lineMap_mem_interior (D.tile ε.1) ε.2 hRε hcz
  set τ := min τ0 1 / 2
  have hτ : 0 < τ := by have := lt_min hτ0 one_pos; simp only [τ]; linarith
  have hττ : τ < τ0 := by have := min_le_left τ0 1; simp only [τ]; linarith
  have hτ1 : τ ≤ 1 := by have := min_le_right τ0 1; simp only [τ]; linarith
  have hmem : AffineMap.lineMap R z τ ∈ (D.tile e.1).edge e.2 := by
    rw [Tri.edge] at hRe hz ⊢
    refine (convex_segment (𝕜 := ℝ) _ _).segment_subset hRe hz ?_
    rw [segment_eq_image_lineMap]
    exact ⟨τ, ⟨hτ.le, hτ1⟩, rfl⟩
  exact D.edge_point_not_interior hmem _ (hint τ hτ hττ)
theorem arrive_at (h : LinkData D isθ Q R g c) {e : Fin N × Fin 3} (he : e ∈ D.lineChain g c)
    (hhi : edgeHi Q R (D.tile e.1) e.2 = 1) :
    e ∈ edgesAt D R ∧ farEnd D R e = AffineMap.lineMap Q R (edgeLo Q R (D.tile e.1) e.2) := by
  have := edgesAt_of_hi D h.hg h.ne h.hQ h.hR he hhi
  rwa [AffineMap.lineMap_apply_one] at this
theorem lonely_marked (h : LinkData D isθ Q R g c) :
    ∃ e₀ ∈ edgesAt D R, isθ e₀ ∧
      (∀ e' ∈ edgesAt D R, ¬ (e₀ ≠ e' ∧ SameRayAt D R e₀ e')) ∧
      ∀ e ∈ edgesAt D R, isθ e → (∀ e' ∈ edgesAt D R, ¬ (e ≠ e' ∧ SameRayAt D R e e')) →
        e = e₀ := by
  obtain ⟨e₀, he₀, hθ₀, -, hlo₀, hhi₀⟩ := h.arrive
  obtain ⟨he₀R, hfar₀⟩ := h.arrive_at he₀ hhi₀
  obtain ⟨ε, hε, hRε⟩ := h.across
  obtain ⟨hε1, hε2⟩ := h.eps_params hε hRε
  obtain ⟨eo, heo, hθo, hloo, hhio⟩ := h.leave
  have hR1 : R = AffineMap.lineMap Q R (1 : ℝ) := (AffineMap.lineMap_apply_one Q R).symm
  refine ⟨e₀, he₀R, hθ₀, ?_, ?_⟩
  · 
    rintro e' he' ⟨hne, t, ht, hFt⟩
    set lo₀ := edgeLo Q R (D.tile e₀.1) e₀.2
    have hfar' : farEnd D R e' = AffineMap.lineMap Q R (1 + t * (lo₀ - 1)) := by
      rw [hFt, hfar₀]
      calc AffineMap.lineMap R (AffineMap.lineMap Q R lo₀) t
          = AffineMap.lineMap (AffineMap.lineMap Q R (1 : ℝ)) (AffineMap.lineMap Q R lo₀) t := by
            rw [AffineMap.lineMap_apply_one]
        _ = _ := lineMap_params 1 lo₀ t
    obtain ⟨plo, phi⟩ := edgesAt_params' h.ne he' hR1 hfar'
    have hp : 1 + t * (lo₀ - 1) < 1 := by nlinarith
    rw [min_eq_right hp.le] at plo
    rw [max_eq_left hp.le] at phi
    have hg' : g (farEnd D R e') = c := by rw [hfar']; exact level_lineMap h.hQ h.hR _
    rcases edgesAt_chain D he' h.hR hg' with c1 | c2
    · apply hne
      refine (lineChain_eq_of_overlap D h.hg h.ne h.hQ h.hR c1 he₀ ?_).symm
      rw [plo, phi, hhi₀, min_self]
      exact max_lt hp hlo₀
    · exact h.not_side2 hε hRε he' c2
  · 
    intro e he hθ hlonely
    obtain ⟨g', c', hg', -, -, hec, e₂, he₂, hRe₂⟩ := lonely_relint D h.end_interior he
      (fun e' he' hne hray => hlonely e' he' ⟨hne.symm, hray⟩)
    obtain ⟨i, k, hik⟩ := h.end_vertex
    have hj : e₂.1 = ε.1 := openSegment_tile_unique D hik hRe₂ hRε
    have hm : e₂.2 = ε.2 := by
      have := hRe₂
      rw [hj] at this
      exact Tri.openSegment_edge_unique (D.tile ε.1) this hRε
    have heq : e₂ = ε := Prod.ext hj hm
    rw [heq] at he₂
    have he1 : e ∈ D.lineChain g c := (chain_iff hg' h.hg he₂ hε e).mp hec
    have hlt := chain_lo_lt_hi D h.hg h.ne h.hQ h.hR he1
    rcases h.end_param he with h1 | h1
    · exfalso
      have := lineChain_eq_of_overlap D h.hg h.ne h.hQ h.hR he1 heo
        (lt_of_le_of_lt (max_le h1.le hloo.le) (lt_min (h1 ▸ hlt) hhio))
      rw [this] at hθ
      exact hθo hθ
    · exact lineChain_eq_of_overlap D h.hg h.ne h.hQ h.hR he1 he₀
        (lt_of_lt_of_le (max_lt (h1 ▸ hlt) hlo₀) (le_min h1.ge hhi₀.ge))
end LinkData
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : Dissection N) (isθ : Fin N × Fin 3 → Prop)
def HasRelation : Prop :=
  ∃ s₁ s₂ : Finset (Fin N × Fin 3), (∀ e ∈ s₁, isθ e) ∧ (∃ e ∈ s₂, ¬ isθ e) ∧
    ∑ e ∈ s₁, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
      = ∑ e ∈ s₂, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
def Partners (V : Plane) (x y : Fin N × Fin 3) : Prop := x ≠ y ∧ SameRayAt D V x y
open Classical in
theorem mixed_of_parity {V : Plane} {e₀ : Fin N × Fin 3} (he₀ : e₀ ∈ edgesAt D V)
    (hθ₀ : isθ e₀) (hl₀ : ∀ e' ∈ edgesAt D V, ¬ Partners D V e₀ e')
    (huniq : ∀ e ∈ edgesAt D V, isθ e → (∀ e' ∈ edgesAt D V, ¬ Partners D V e e') → e = e₀)
    (heven : Even ((edgesAt D V).filter isθ).card) :
    ∃ x ∈ edgesAt D V, ∃ y ∈ edgesAt D V, Partners D V x y ∧ isθ x ∧ ¬ isθ y := by
  by_contra hno
  push Not at hno
  have hpar := card_filter_mod_two (edgesAt D V) (Partners D V) isθ
    (fun x _ y _ h => ⟨h.1.symm, sameRayAt_symm D h.2⟩) (fun x h => h.1 rfl)
    (fun x hx y hy z hz hxy hxz => by
      by_contra hyz
      exact sameRayAt_unique D hx hy hz hxy.1.symm hxz.1.symm hyz hxy.2 hxz.2)
    (fun x hx y hy hxy hθ => by
      exact hno x hx y hy hxy hθ) {e₀} (fun x => by
        rw [Finset.mem_singleton]
        constructor
        · rintro rfl
          exact ⟨he₀, hθ₀, hl₀⟩
        · rintro ⟨hx, hθ, hl⟩
          exact huniq x hx hθ hl)
  rw [Finset.card_singleton, Nat.even_iff.mp heven] at hpar
  exact absurd hpar (by norm_num)
open Classical in
theorem out_of_in_wall {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (h : LinkData D isθ Q R g c)
    (heven : Even ((edgesAt D R).filter isθ).card) (hnw : ¬ WallRel D isθ) :
    ∃ R', IsLink D isθ R R' := by
  obtain ⟨e₀, he₀, hθ₀, hl₀, huniq⟩ := h.lonely_marked
  obtain ⟨x, hx, y, hy, hxy, hθx, hθy⟩ := mixed_of_parity D isθ he₀ hθ₀
    (fun e' he' h' => hl₀ e' he' h') (fun e he hθ hl => huniq e he hθ (fun e' he' h' => hl e' he' h'))
    heven
  rcases extend_link_wall D isθ hx hy hxy.1.symm hxy.2 hθx hθy
    (h.back_of_partner hx hy hxy.1 hxy.2) with hlink | hw
  · exact hlink
  · exact absurd hw hnw
theorem hasRelation_of_wallRel (h : WallRel D isθ) : HasRelation D isθ :=
  relation_of_wallRel D isθ h
open Classical in
theorem out_of_in {Q R : Plane} {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (h : LinkData D isθ Q R g c)
    (heven : Even ((edgesAt D R).filter isθ).card) (hnorel : ¬ HasRelation D isθ) :
    ∃ R', IsLink D isθ R R' :=
  out_of_in_wall D isθ h heven fun hw => hnorel (hasRelation_of_wallRel D isθ hw)
open Classical in
theorem sum_out_eq_sum_in (V : Finset Plane) :
    ∑ v ∈ V, (V.filter fun w => IsLink D isθ v w).card
      = ∑ w ∈ V, (V.filter fun v => IsLink D isθ v w).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm
open Classical in
theorem in_le_one (V : Finset Plane) (w : Plane) :
    (V.filter fun v => IsLink D isθ v w).card ≤ 1 :=
  Finset.card_le_one.mpr fun _ ha _ hb =>
    link_unique D isθ (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
open Classical in
noncomputable def vertexFinset : Finset Plane :=
  Finset.univ.image fun p : Fin N × Fin 3 => (D.tile p.1).pts p.2
theorem link_mem_vertexFinset {u w : Plane} (h : IsLink D isθ u w) :
    u ∈ vertexFinset D ∧ w ∈ vertexFinset D := by
  classical
  obtain ⟨g, c, h⟩ := h
  obtain ⟨i, k, hik⟩ := h.start_vertex
  obtain ⟨i', k', hik'⟩ := h.end_vertex
  exact ⟨Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, hik⟩,
    Finset.mem_image.mpr ⟨(i', k'), Finset.mem_univ _, hik'⟩⟩
open Classical in
theorem relation_of_start
    (heven : ∀ Q R g c, LinkData D isθ Q R g c → Even ((edgesAt D R).filter isθ).card)
    (hstart : ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D isθ Q₀ R) :
    HasRelation D isθ := by
  by_contra hnorel
  obtain ⟨Q₀, hQ₀fr, R₀, hlink₀⟩ := hstart
  set V := vertexFinset D
  have hge : ∀ v ∈ V, (V.filter fun u => IsLink D isθ u v).card ≤
      (V.filter fun w => IsLink D isθ v w).card := by
    intro v _
    rcases Nat.eq_zero_or_pos (V.filter fun u => IsLink D isθ u v).card with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
      obtain ⟨-, g, c, hl⟩ := Finset.mem_filter.mp hu
      obtain ⟨R', hR'⟩ := out_of_in D isθ hl (heven _ _ _ _ hl) hnorel
      have : 1 ≤ (V.filter fun w => IsLink D isθ v w).card :=
        Finset.card_pos.mpr ⟨R', Finset.mem_filter.mpr ⟨(link_mem_vertexFinset D isθ hR').2, hR'⟩⟩
      linarith [in_le_one D isθ V v]
  have hin0 : (V.filter fun u => IsLink D isθ u Q₀).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro u - ⟨g, c, hl⟩
    exact hQ₀fr.2 hl.end_interior
  have hout : 0 < (V.filter fun w => IsLink D isθ Q₀ w).card :=
    Finset.card_pos.mpr ⟨R₀, Finset.mem_filter.mpr ⟨(link_mem_vertexFinset D isθ hlink₀).2,
      hlink₀⟩⟩
  have hlt := Finset.sum_lt_sum hge
    ⟨Q₀, (link_mem_vertexFinset D isθ hlink₀).1, by rw [hin0]; exact hout⟩
  rw [sum_out_eq_sum_in] at hlt
  exact lt_irrefl _ hlt
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : CongruentDissection N)
theorem vertex_counts_pos {P : Plane} {i : Fin N} {k : Fin 3} (hk : (D.tile i).pts k = P) :
    1 ≤ angleCount D P (tileα D) + angleCount D P (tileβ D) + angleCount D P (tileγ D) := by
  rcases localAngle_at_own_vertex_mem' D i k with h | h | h <;> rw [hk] at h
  · have := angleCount_pos D h; omega
  · have := angleCount_pos D h; omega
  · have := angleCount_pos D h; omega
variable (hγ : tileγ D = 2 * tileα D) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry Set
variable {N : ℕ} (D : Dissection N)
theorem side_level :
    ∃ (g : Plane →ₗ[ℝ] ℝ) (c : ℝ), g ≠ 0 ∧ g (D.target.pts 0) = c ∧ g (D.target.pts 1) = c ∧
      c < g (D.target.pts 2) ∧ ∀ y ∈ D.target.carrier, c ≤ g y := by
  obtain ⟨g, c, hg, hline, h2⟩ := edge_level_oriented D.target 0
  have h0 : g (D.target.pts 0) = c := hline _ (left_mem_segment _ _ _)
  have h1 : g (D.target.pts 1) = c := hline _ (right_mem_segment _ _ _)
  refine ⟨g, c, hg, h0, h1, h2, fun y hy => ?_⟩
  have := D.target.carrier_subset_halfplane (-g) (-c) (fun i => by
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    rcases fin3_cases3 i 0 with rfl | rfl | rfl
    · exact h0.ge
    · exact h1.ge
    · exact h2.le) y hy
  simpa using this
theorem side_chain {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hside : ∀ y ∈ D.target.carrier, c ≤ g y)
    {e : Fin N × Fin 3} (h1 : g ((D.tile e.1).pts e.2) = c)
    (h2 : g ((D.tile e.1).pts (e.2 + 1)) = c) : e ∈ D.lineChain (-g) (-c) := by
  refine Dissection.mem_lineChain.mpr ⟨by simp [h1], by simp [h2], fun i => ?_⟩
  have hmem : (D.tile e.1).pts i ∈ D.target.carrier := by
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨e.1, subset_convexHull ℝ _ ⟨i, rfl⟩⟩
  simpa using hside _ hmem
set_option maxHeartbeats 4000000 in
open Classical in
theorem side_start (isθ : Fin N × Fin 3 → Prop) (part : Finset (Fin N × Fin 3))
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 0) (D.target.pts 1))
    {ec en : Fin N × Fin 3} (hec : ec ∈ part) (hen : en ∈ part)
    (hθc : isθ ec) (hθn : ¬ isθ en)
    (hgood : ∀ Q ∈ openSegment ℝ (D.target.pts 0) (D.target.pts 1),
      (∃ i k, (D.tile i).pts k = Q) →
        (∀ j : Fin N, ∀ m : Fin 3, Q ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)))
          ∧ Even ((edgesAt D Q).filter isθ).card)
    (hnorel : ¬ HasRelation D isθ) :
    ∃ Q₀ ∈ frontier D.target.carrier, ∃ R, IsLink D isθ Q₀ R := by
  obtain ⟨g, c, hg, hT0, hT1, hT2, hside⟩ := side_level D
  set T0 := D.target.pts 0
  set T1 := D.target.pts 1
  have hT01 : T0 ≠ T1 := tri_pts_succ_ne D.target 0
  have hng : -g ≠ 0 := neg_ne_zero.mpr hg
  have hnT0 : (-g) T0 = -c := by simp [hT0]
  have hnT1 : (-g) T1 = -c := by simp [hT1]
  have hL0 : AffineMap.lineMap T0 T1 (0 : ℝ) = T0 := AffineMap.lineMap_apply_zero T0 T1
  have hsegI : segment ℝ T0 T1 = AffineMap.lineMap T0 T1 '' Icc (0 : ℝ) 1 := by
    rw [← segment_eq_Icc zero_le_one, image_segment, hL0, AffineMap.lineMap_apply_one]
  have hsub : ∀ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ T0 T1 := fun e he => by
    rw [← hcov]; exact Set.subset_biUnion_of_mem (u := fun e => (D.tile e.1).edge e.2) he
  have hline : ∀ y ∈ segment ℝ T0 T1, g y = c := by
    intro y hy
    rw [hsegI] at hy
    obtain ⟨t, -, rfl⟩ := hy
    exact level_lineMap hT0 hT1 t
  have hchain : ∀ e ∈ part, e ∈ D.lineChain (-g) (-c) := fun e he =>
    side_chain D hside (hline _ (hsub e he (left_mem_segment _ _ _)))
      (hline _ (hsub e he (right_mem_segment _ _ _)))
  have mem : ∀ e ∈ D.lineChain (-g) (-c), ∀ t,
      AffineMap.lineMap T0 T1 t ∈ (D.tile e.1).edge e.2 ↔
        t ∈ Icc (edgeLo T0 T1 (D.tile e.1) e.2) (edgeHi T0 T1 (D.tile e.1) e.2) :=
    fun e he t => chain_mem_edge_iff D hng hT01 hnT0 hnT1 he t
  have hlt : ∀ e ∈ D.lineChain (-g) (-c),
      edgeLo T0 T1 (D.tile e.1) e.2 < edgeHi T0 T1 (D.tile e.1) e.2 :=
    fun e he => chain_lo_lt_hi D hng hT01 hnT0 hnT1 he
  have ov : ∀ e ∈ D.lineChain (-g) (-c), ∀ e' ∈ D.lineChain (-g) (-c),
      max (edgeLo T0 T1 (D.tile e.1) e.2) (edgeLo T0 T1 (D.tile e'.1) e'.2)
        < min (edgeHi T0 T1 (D.tile e.1) e.2) (edgeHi T0 T1 (D.tile e'.1) e'.2) → e = e' :=
    fun e he e' he' h => lineChain_eq_of_overlap D hng hT01 hnT0 hnT1 he he' h
  have hI : ∀ e ∈ part, 0 ≤ edgeLo T0 T1 (D.tile e.1) e.2 ∧ edgeHi T0 T1 (D.tile e.1) e.2 ≤ 1 := by
    intro e he
    have key : ∀ t, t ∈ Icc (edgeLo T0 T1 (D.tile e.1) e.2) (edgeHi T0 T1 (D.tile e.1) e.2) →
        t ∈ Icc (0 : ℝ) 1 := by
      intro t ht
      have := hsub e he ((mem e (hchain e he) t).mpr ht)
      rw [hsegI] at this
      obtain ⟨s, hs, hst⟩ := this
      rwa [← AffineMap.lineMap_injective ℝ hT01 hst]
    have h := hlt e (hchain e he)
    exact ⟨(key _ ⟨le_rfl, h.le⟩).1, (key _ ⟨h.le, le_rfl⟩).2⟩
  set U := ⋃ e ∈ part.filter (isθ), (D.tile e.1).edge e.2
  set V := ⋃ e ∈ part.filter (fun e => ¬ isθ e), (D.tile e.1).edge e.2
  have hclosed : ∀ e : Fin N × Fin 3, IsClosed ((D.tile e.1).edge e.2) := fun e => by
    rw [Tri.edge, segment_eq_image_lineMap]
    exact (isCompact_Icc.image (AffineMap.lineMap_continuous)).isClosed
  have hU : IsClosed U := isClosed_biUnion_finset fun e _ => hclosed e
  have hV : IsClosed V := isClosed_biUnion_finset fun e _ => hclosed e
  have hUV : segment ℝ T0 T1 ⊆ U ∪ V := by
    rw [← hcov]
    intro y hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
    by_cases hθ : isθ e
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hθ⟩, hye⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hθ⟩, hye⟩)
  have hpt : ∀ e ∈ part, (D.tile e.1).pts e.2 ∈ segment ℝ T0 T1 ∩ (D.tile e.1).edge e.2 :=
    fun e he => ⟨hsub e he (left_mem_segment _ _ _), left_mem_segment _ _ _⟩
  obtain ⟨Q₀, hQ₀s, hQ₀U, hQ₀V⟩ := isPreconnected_closed_iff.mp
    (convex_segment T0 T1).isPreconnected U V hU hV hUV
    ⟨_, (hpt ec hec).1, Set.mem_iUnion₂.mpr ⟨ec, Finset.mem_filter.mpr ⟨hec, hθc⟩, (hpt ec hec).2⟩⟩
    ⟨_, (hpt en hen).1, Set.mem_iUnion₂.mpr ⟨en, Finset.mem_filter.mpr ⟨hen, hθn⟩, (hpt en hen).2⟩⟩
  obtain ⟨x, hx, hQx⟩ := Set.mem_iUnion₂.mp hQ₀U
  obtain ⟨y, hy, hQy⟩ := Set.mem_iUnion₂.mp hQ₀V
  obtain ⟨hxp, hθx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyp, hθy⟩ := Finset.mem_filter.mp hy
  have hxc := hchain x hxp
  have hyc := hchain y hyp
  have hxy : x ≠ y := fun h => hθy (h ▸ hθx)
  rw [hsegI] at hQ₀s
  obtain ⟨q, -, rfl⟩ := hQ₀s
  have hqx := (mem x hxc q).mp hQx
  have hqy := (mem y hyc q).mp hQy
  have hno := fun h => hxy (ov x hxc y hyc h)
  have hlx := hlt x hxc
  have hly := hlt y hyc
  have hsplit : (edgeHi T0 T1 (D.tile x.1) x.2 = q ∧ edgeLo T0 T1 (D.tile y.1) y.2 = q) ∨
      (edgeLo T0 T1 (D.tile x.1) x.2 = q ∧ edgeHi T0 T1 (D.tile y.1) y.2 = q) := by
    by_contra hc
    apply hno
    rcases le_total (edgeLo T0 T1 (D.tile x.1) x.2) (edgeLo T0 T1 (D.tile y.1) y.2) with h1 | h1 <;>
    rcases le_total (edgeHi T0 T1 (D.tile x.1) x.2) (edgeHi T0 T1 (D.tile y.1) y.2) with h2 | h2
    · rw [max_eq_right h1, min_eq_left h2]
      by_contra h; push Not at h
      exact hc (Or.inl ⟨by linarith [hqx.2, hqy.1], by linarith [hqx.2, hqy.1]⟩)
    · rw [max_eq_right h1, min_eq_right h2]; linarith
    · rw [max_eq_left h1, min_eq_left h2]; linarith
    · rw [max_eq_left h1, min_eq_right h2]
      by_contra h; push Not at h
      exact hc (Or.inr ⟨by linarith [hqx.1, hqy.2], by linarith [hqx.1, hqy.2]⟩)
  obtain ⟨hx0, hx1⟩ := hI x hxp
  obtain ⟨hy0, hy1⟩ := hI y hyp
  have hq0 : 0 < q := by rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hq1 : q < 1 := by rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  set Q₀ := AffineMap.lineMap T0 T1 q
  have hQ₀open : Q₀ ∈ openSegment ℝ T0 T1 := by
    rw [openSegment_eq_image_lineMap]; exact ⟨q, ⟨hq0, hq1⟩, rfl⟩
  have hgQ₀ : g Q₀ = c := level_lineMap hT0 hT1 q
  have hQ₀fr : Q₀ ∈ frontier D.target.carrier :=
    tri_side_subset_frontier D.target 0 (openSegment_subset_segment _ _ _ hQ₀open)
  have hQ₀nc : Q₀ ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    exact Tri.vertex_not_mem_openSegment D.target m 0 (hm ▸ hQ₀open)
  refine ⟨Q₀, hQ₀fr, ?_⟩
  have hxe : x ∈ edgesAt D Q₀ := by
    rcases hsplit with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact (edgesAt_of_hi D hng hT01 hnT0 hnT1 hxc h1).1
    · exact (edgesAt_of_lo D hng hT01 hnT0 hnT1 hxc h1).1
  have hye : y ∈ edgesAt D Q₀ := by
    rcases hsplit with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact (edgesAt_of_lo D hng hT01 hnT0 hnT1 hyc h2).1
    · exact (edgesAt_of_hi D hng hT01 hnT0 hnT1 hyc h2).1
  have honline : ∀ e ∈ edgesAt D Q₀, g (farEnd D Q₀ e) = c →
      e = x ∨ e = y := by
    intro e he hgF
    obtain ⟨n1, n2⟩ := level_far D he hgQ₀ hgF
    have hec' := side_chain D hside n1 n2
    have hle := hlt e hec'
    rcases end_param_at D hT01 he with hl | hh
    · have he1 : q < edgeHi T0 T1 (D.tile e.1) e.2 := by rw [← hl]; exact hle
      rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right; apply ov e hec' y hyc; rw [hl, h2, max_self]
        exact lt_min he1 (by rw [← h2]; exact hly)
      · left; apply ov e hec' x hxc; rw [hl, h1, max_self]
        exact lt_min he1 (by rw [← h1]; exact hlx)
    · have he1 : edgeLo T0 T1 (D.tile e.1) e.2 < q := by rw [← hh]; exact hle
      rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; apply ov e hec' x hxc; rw [hh, h1, min_self]
        exact max_lt he1 (by rw [← h1]; exact hlx)
      · right; apply ov e hec' y hyc; rw [hh, h2, min_self]
        exact max_lt he1 (by rw [← h2]; exact hly)
  have hcoord : ∀ z, g z - c = D.target.basis.coord (0 + 2) z * (g (D.target.pts (0 + 2)) - c) :=
    level_eq_coord D.target g c (0 + 2) (by rw [show (0 : Fin 3) + 2 + 1 = 0 from rfl]; exact hT0)
      (by rw [show (0 : Fin 3) + 2 + 2 = 0 + 1 from rfl]; exact hT1)
  have hinto : ∀ e ∈ edgesAt D Q₀, c < g (farEnd D Q₀ e) →
      ∃ τ ∈ Ioo (0 : ℝ) 1, AffineMap.lineMap Q₀ (farEnd D Q₀ e) τ ∈
        interior D.target.carrier := by
    intro e he hF
    have hpos : 0 < D.target.basis.coord (0 + 2) (farEnd D Q₀ e) := by
      have := hcoord (farEnd D Q₀ e)
      have h2 : 0 < g (D.target.pts (0 + 2)) - c := by
        rw [show (0 : Fin 3) + 2 = 2 from rfl]; linarith
      by_contra hc; push Not at hc; nlinarith
    obtain ⟨τ0, hτ0, hint⟩ := Tri.lineMap_mem_interior D.target 0 hQ₀open hpos
    refine ⟨min τ0 1 / 2, ⟨by have := lt_min hτ0 one_pos; linarith,
      by have := min_le_right τ0 1; linarith⟩, hint _ (by have := lt_min hτ0 one_pos; linarith)
      (by have := min_le_left τ0 1; linarith)⟩
  obtain ⟨hnrel, heven⟩ := hgood Q₀ hQ₀open (by
    rcases (mem_edgesAt _).mp hxe with h | h
    · exact ⟨_, _, h⟩
    · exact ⟨_, _, h⟩)
  have hlone_line : ∀ e ∈ edgesAt D Q₀,
      (∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ e e') →
        g (farEnd D Q₀ e) = c := by
    intro e he hl
    have hFt : farEnd D Q₀ e ∈ D.target.carrier := by
      rw [← D.covers]
      refine Set.mem_iUnion.mpr ⟨e.1, (D.tile e.1).edge_subset_carrier e.2 ?_⟩
      rw [edgesAt_edge _ he]; exact right_mem_segment _ _ _
    rcases (hside _ hFt).lt_or_eq with hlt' | heq
    · exfalso
      obtain ⟨τ, hτ, hint⟩ := hinto e he hlt'
      obtain ⟨g₀, c₀, hg₀, hQ₀', hF₀⟩ := ray_level (farEnd_ne _ he)
      obtain ⟨g', c', hg', hQ', hF', hec'⟩ : ∃ (g' : Plane →ₗ[ℝ] ℝ) (c' : ℝ), g' ≠ 0 ∧
          g' Q₀ = c' ∧ g' (farEnd D Q₀ e) = c' ∧ e ∈ D.lineChain g' c' := by
        rcases edgesAt_chain _ he hQ₀' hF₀ with h' | h'
        · exact ⟨g₀, c₀, hg₀, hQ₀', hF₀, h'⟩
        · exact ⟨-g₀, -c₀, neg_ne_zero.mpr hg₀, by simp [hQ₀'], by simp [hF₀], h'⟩
      obtain ⟨e₂, -, hQe₂⟩ := lonely_openSegment _ he hg' hQ' hF' hec'
        (fun e' he' hne hray => hl e' he' ⟨hne.symm, hray⟩) hτ hint
      exact hnrel _ _ hQe₂
    · exact heq.symm
  have hgx : g (farEnd D Q₀ x) = c := by
    rcases hsplit with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [(edgesAt_of_hi D hng hT01 hnT0 hnT1 hxc h1).2]
      exact level_lineMap hT0 hT1 _
    · rw [(edgesAt_of_lo D hng hT01 hnT0 hnT1 hxc h1).2]
      exact level_lineMap hT0 hT1 _
  have hnxy : ¬ SameRayAt D Q₀ x y := by
    rintro ⟨t, ht, hFt⟩
    rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have fx := (edgesAt_of_hi D hng hT01 hnT0 hnT1 hxc h1).2
      have fy := (edgesAt_of_lo D hng hT01 hnT0 hnT1 hyc h2).2
      rw [fx, fy, lineMap_params] at hFt
      have := AffineMap.lineMap_injective ℝ hT01 hFt
      nlinarith
    · have fx := (edgesAt_of_lo D hng hT01 hnT0 hnT1 hxc h1).2
      have fy := (edgesAt_of_hi D hng hT01 hnT0 hnT1 hyc h2).2
      rw [fx, fy, lineMap_params] at hFt
      have := AffineMap.lineMap_injective ℝ hT01 hFt
      nlinarith
  have hlone_xy : ∀ u ∈ ({x, y} : Finset (Fin N × Fin 3)),
      ∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ u e' := by
    intro u hu e' he' ⟨hne, hray⟩
    have hgu : g (farEnd D Q₀ u) = c := by
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hgx
      · rw [Finset.mem_singleton.mp hu]
        obtain ⟨n1, n2⟩ := lineChain_ends D hyc
        rcases (mem_edgesAt _).mp hye with h | h
        · rw [farEnd, if_pos h]; simpa using n2
        · have hne' : (D.tile y.1).pts y.2 ≠ Q₀ := fun h0 =>
            tri_pts_succ_ne (D.tile y.1) y.2 (h0.trans h.symm)
          rw [farEnd, if_neg hne']; simpa using n1
    obtain ⟨t, ht, hFt⟩ := hray
    have hge : g (farEnd D Q₀ e') = c := by
      rw [hFt]; exact level_lineMap hgQ₀ hgu t
    have hray' : SameRayAt D Q₀ u e' := ⟨t, ht, hFt⟩
    rcases Finset.mem_insert.mp hu with rfl | hu
    · rcases honline e' he' hge with h | h
      · exact hne h.symm
      · exact hnxy (h ▸ hray')
    · rw [Finset.mem_singleton.mp hu] at hne hray'
      rcases honline e' he' hge with h | h
      · exact hnxy (sameRayAt_symm _ (h ▸ hray'))
      · exact hne h.symm
  have hxlone : ∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ x e' :=
    hlone_xy x (by simp)
  have huniq : ∀ e ∈ edgesAt D Q₀, isθ e →
      (∀ e' ∈ edgesAt D Q₀, ¬ Partners D Q₀ e e') → e = x := by
    intro e he hθ hl
    rcases honline e he (hlone_line e he hl) with h | h
    · exact h
    · exact absurd (h ▸ hθ) hθy
  obtain ⟨x', hx', y', hy', hxy', hθx', hθy'⟩ := mixed_of_parity D
    (isθ) hxe hθx hxlone huniq heven
  have hgx' : c < g (farEnd D Q₀ x') := by
    have hFt : farEnd D Q₀ x' ∈ D.target.carrier := by
      rw [← D.covers]
      refine Set.mem_iUnion.mpr ⟨x'.1, (D.tile x'.1).edge_subset_carrier x'.2 ?_⟩
      rw [edgesAt_edge _ hx']; exact right_mem_segment _ _ _
    rcases (hside _ hFt).lt_or_eq with h | h
    · exact h
    · exfalso
      rcases honline x' hx' h.symm with rfl | rfl
      · exact hlone_xy _ (by simp) y' hy' hxy'
      · exact hlone_xy _ (by simp) y' hy' hxy'
  have hback : ∀ e : Fin N × Fin 3, Q₀ ∈ (D.tile e.1).edge e.2 →
      ∀ z ∈ (D.tile e.1).edge e.2, Q₀ ∉ openSegment ℝ z (farEnd D Q₀ x') := by
    intro e _ z hz hQz
    have hzt : z ∈ D.target.carrier := by
      rw [← D.covers]
      exact Set.mem_iUnion.mpr ⟨e.1, (D.tile e.1).edge_subset_carrier e.2 hz⟩
    obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hQz
    have h1 := hgQ₀
    rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h1
    have h3 := mul_le_mul_of_nonneg_left (hside z hzt) ha.le
    have h4 := mul_lt_mul_of_pos_left hgx' hb
    have h5 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    linarith
  rcases extend_link D (isθ) hx' hy' hxy'.1.symm hxy'.2 hθx' hθy'
    hback with h | h
  · exact h
  · exact absurd h hnorel
section Specific
variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * tileα D)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr
end Specific
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
theorem model_sides_pos :
    0 < dist (D.model.pts 1) (D.model.pts 2) ∧ 0 < dist (D.model.pts 2) (D.model.pts 0) ∧
      0 < dist (D.model.pts 0) (D.model.pts 1) := by
  have hne : ∀ i j : Fin 3, i ≠ j → D.model.pts i ≠ D.model.pts j :=
    fun i j h e => h (D.model.indep.injective e)
  exact ⟨dist_pos.mpr (hne 1 2 (by decide)), dist_pos.mpr (hne 2 0 (by decide)),
    dist_pos.mpr (hne 0 1 (by decide))⟩
variable (hsep : AnglesSep D)
include hsep
open Classical in
theorem relation_counts {φ : ℝ} (h : HasRelation D.toDissection (edgeType D φ)) :
    ∃ (s₁ s₂ : Finset (Fin N × Fin 3)), (∀ e ∈ s₁, edgeType D φ e) ∧
      (∃ e ∈ s₂, ¬ edgeType D φ e) ∧
      ((s₁.filter (edgeType D (tileα D))).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
        + ((s₁.filter (edgeType D (tileβ D))).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
        + ((s₁.filter (edgeType D (tileγ D))).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      = ((s₂.filter (edgeType D (tileα D))).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
        + ((s₂.filter (edgeType D (tileβ D))).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
        + ((s₂.filter (edgeType D (tileγ D))).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨s₁, s₂, h1, h2, hsum⟩ := h
  refine ⟨s₁, s₂, h1, h2, ?_⟩
  have w1 := side_walk_counts_sep D hsep s₁ _ rfl
  have w2 := side_walk_counts_sep D hsep s₂ _ rfl
  unfold edgeType
  rw [← w1, ← w2]
  exact hsum
theorem types_ne : tileα D ≠ tileβ D ∧ tileα D ≠ tileγ D ∧ tileβ D ≠ tileγ D := by
  have hinj := hsep.2
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  exact ⟨ne 0 1 (by decide), ne 0 2 (by decide), ne 1 2 (by decide)⟩
open Classical in
theorem c_relation_of_edges (h : HasRelation D.toDissection (edgeType D (tileγ D))) :
    ∃ J p q : ℕ, 0 < J ∧
    (J : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
      = p * dist (D.model.pts 1) (D.model.pts 2) + q * dist (D.model.pts 2) (D.model.pts 0) := by
  obtain ⟨hαβ, hαγ, hβγ⟩ := types_ne D hsep
  obtain ⟨ha, hb, hc⟩ := model_sides_pos D
  obtain ⟨s₁, s₂, h1, ⟨e, he, hne⟩, hrel⟩ :=
    relation_counts D hsep h
  have f1 : s₁.filter (edgeType D (tileα D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hαγ (h'.symm.trans (h1 x hx))
  have f2 : s₁.filter (edgeType D (tileβ D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hβγ (h'.symm.trans (h1 x hx))
  have f3 : s₁.filter (edgeType D (tileγ D)) = s₁ := Finset.filter_true_of_mem h1
  rw [f1, f2, f3, Finset.card_empty, Nat.cast_zero, zero_mul, zero_mul, zero_add, zero_add] at hrel
  set pα := (s₂.filter (edgeType D (tileα D))).card
  set pβ := (s₂.filter (edgeType D (tileβ D))).card
  set pγ := (s₂.filter (edgeType D (tileγ D))).card
  have hpos : 1 ≤ pα + pβ := by
    rcases localAngle_at_own_vertex_mem' D e.1 (e.2 + 2) with h | h | h
    · have : 1 ≤ pα := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
    · have : 1 ≤ pβ := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
    · exact absurd h hne
  have hlt : pγ < s₁.card := by
    by_contra hle
    push Not at hle
    have h3 : (s₁.card : ℝ) ≤ pγ := by exact_mod_cast hle
    have h4 : (1 : ℝ) ≤ pα + pβ := by exact_mod_cast hpos
    have h5 : (0 : ℝ) < pα * dist (D.model.pts 1) (D.model.pts 2)
        + pβ * dist (D.model.pts 2) (D.model.pts 0) := by
      rcases Nat.eq_zero_or_pos pα with h0 | h0
      · have : (1 : ℝ) ≤ pβ := by rw [h0] at hpos; exact_mod_cast (by omega : 1 ≤ pβ)
        rw [h0, Nat.cast_zero, zero_mul, zero_add]; nlinarith
      · have : (1 : ℝ) ≤ pα := by exact_mod_cast h0
        have : (0 : ℝ) ≤ pβ := Nat.cast_nonneg _
        nlinarith
    nlinarith
  refine ⟨s₁.card - pγ, pα, pβ, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le]
  linarith
end TriangleTiling
end

section
namespace TriangleTiling.DirClass
open Complex
variable (θ : ℝ)
noncomputable def ω : ℂ := Complex.exp (θ * Complex.I)
def Orbit (z : ℂ) : Set ℂ := {w | ∃ i j : ℤ, w = ω θ ^ i * (-1) ^ j * z}
noncomputable def rep (z : ℂ) : ℂ := Classical.epsilon (· ∈ Orbit θ z)
def Cls (z : ℂ) : Prop := ∃ i j : ℤ, Even j ∧ z = ω θ ^ i * (-1) ^ j * rep θ z
theorem ω_ne : ω θ ≠ 0 := Complex.exp_ne_zero _
theorem neg_one_ne : (-1 : ℂ) ≠ 0 := neg_ne_zero.mpr one_ne_zero
theorem mem_orbit_self (z : ℂ) : z ∈ Orbit θ z := ⟨0, 0, by simp⟩
theorem orbit_eq {z w : ℂ} (h : w ∈ Orbit θ z) : Orbit θ w = Orbit θ z := by
  obtain ⟨i, j, rfl⟩ := h
  ext v
  constructor
  · rintro ⟨i', j', rfl⟩
    refine ⟨i' + i, j' + j, ?_⟩
    rw [zpow_add₀ (ω_ne θ), zpow_add₀ neg_one_ne]; ring
  · rintro ⟨i', j', rfl⟩
    refine ⟨i' - i, j' - j, ?_⟩
    rw [zpow_sub₀ (ω_ne θ), zpow_sub₀ neg_one_ne]
    field_simp [ω_ne θ, neg_one_ne]
theorem rep_mem (z : ℂ) : rep θ z ∈ Orbit θ z :=
  Classical.epsilon_spec (p := (· ∈ Orbit θ z)) ⟨z, mem_orbit_self θ z⟩
theorem rep_eq {z w : ℂ} (h : w ∈ Orbit θ z) : rep θ w = rep θ z := by
  unfold rep; rw [orbit_eq θ h]
theorem exists_rep (z : ℂ) : ∃ i j : ℤ, z = ω θ ^ i * (-1) ^ j * rep θ z := by
  obtain ⟨i, j, h⟩ := rep_mem θ z
  refine ⟨-i, -j, ?_⟩
  rw [h, zpow_neg, zpow_neg]
  field_simp [zpow_ne_zero i (ω_ne θ), zpow_ne_zero j neg_one_ne]
theorem rep_ne {z : ℂ} (hz : z ≠ 0) : rep θ z ≠ 0 := by
  obtain ⟨i, j, h⟩ := rep_mem θ z
  rw [h]
  exact mul_ne_zero (mul_ne_zero (zpow_ne_zero i (ω_ne θ)) (zpow_ne_zero j neg_one_ne)) hz
theorem parity_unique (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) {i j i' j' : ℤ}
    (h : ω θ ^ i * (-1) ^ j * z = ω θ ^ i' * (-1) ^ j' * z) : Even (j - j') := by
  have h1 : ω θ ^ (i - i') = (-1) ^ (j' - j) := by
    rw [zpow_sub₀ (ω_ne θ), zpow_sub₀ neg_one_ne]
    have h2 := mul_right_cancel₀ hz h
    field_simp [zpow_ne_zero i' (ω_ne θ), zpow_ne_zero j neg_one_ne]
    linear_combination h2
  have hm1 : (-1 : ℂ) = Complex.exp (Real.pi * Complex.I) := by
    rw [Complex.exp_pi_mul_I]
  rw [ω, ← Complex.exp_int_mul, hm1, ← Complex.exp_int_mul,
    Complex.exp_eq_exp_iff_exists_int] at h1
  obtain ⟨k, hk⟩ := h1
  have hk' : ((i - i' : ℤ) : ℝ) * θ = ((j' - j : ℤ) + 2 * k : ℝ) * Real.pi := by
    have := congrArg Complex.im hk
    simp at this
    push_cast
    linarith
  by_cases hi : i - i' = 0
  · rw [hi] at hk'
    simp at hk'
    have : (j' - j : ℤ) + 2 * k = 0 := by exact_mod_cast hk'.symm.symm
    exact ⟨k, by omega⟩
  · exfalso
    apply hθ
    refine ⟨((j' - j : ℤ) + 2 * k : ℚ) / (i - i' : ℤ), ?_⟩
    have hi' : ((i - i' : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi
    push_cast at hk' hi' ⊢
    field_simp
    linarith
theorem cls_iff (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) {i j : ℤ}
    (h : z = ω θ ^ i * (-1) ^ j * rep θ z) : Cls θ z ↔ Even j := by
  constructor
  · rintro ⟨i1, j1, hj1, h1⟩
    have := parity_unique θ hθ (rep_ne θ hz) (h1.symm.trans h)
    have : j = j1 - (j1 - j) := by ring
    rw [this]; exact hj1.sub ‹_›
  · exact fun hj => ⟨i, j, hj, h⟩
theorem cls_mul (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) (i j : ℤ) :
    Cls θ (ω θ ^ i * (-1) ^ j * z) ↔ (Cls θ z ↔ Even j) := by
  have hw : ω θ ^ i * (-1) ^ j * z ∈ Orbit θ z := ⟨i, j, rfl⟩
  have hw0 : ω θ ^ i * (-1) ^ j * z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zpow_ne_zero i (ω_ne θ)) (zpow_ne_zero j neg_one_ne)) hz
  obtain ⟨i0, j0, h0⟩ := exists_rep θ z
  have hw' : ω θ ^ i * (-1) ^ j * z =
      ω θ ^ (i + i0) * (-1) ^ (j + j0) * rep θ (ω θ ^ i * (-1) ^ j * z) := by
    rw [rep_eq θ hw, zpow_add₀ (ω_ne θ), zpow_add₀ neg_one_ne]
    conv_lhs => rw [h0]
    ring
  rw [cls_iff θ hθ hw0 hw', cls_iff θ hθ hz h0, Int.even_add]
  tauto
theorem cls_neg (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) :
    Cls θ (-z) ↔ ¬ Cls θ z := by
  have := cls_mul θ hθ hz 0 1
  simp only [zpow_zero, zpow_one, one_mul, neg_one_mul] at this
  rw [this]
  simp
theorem cls_mul_ω (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) :
    Cls θ (ω θ * z) ↔ Cls θ z := by
  have := cls_mul θ hθ hz 1 0
  simp only [zpow_one, zpow_zero, mul_one] at this
  rw [this]
  simp
theorem cls_mul_ω_inv (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) {z : ℂ} (hz : z ≠ 0) :
    Cls θ ((ω θ)⁻¹ * z) ↔ Cls θ z := by
  have := cls_mul θ hθ hz (-1) 0
  simp only [zpow_neg, zpow_one, zpow_zero, mul_one] at this
  rw [this]
  simp
end TriangleTiling.DirClass
end

section
namespace TriangleTiling
open Erdos634.Geometry Complex ComplexConjugate
def toC (v : Plane) : ℂ := ⟨v 0, v 1⟩
@[simp] theorem toC_re (v : Plane) : (toC v).re = v 0 := rfl
@[simp] theorem toC_im (v : Plane) : (toC v).im = v 1 := rfl
theorem toC_ne {v : Plane} (hv : v ≠ 0) : toC v ≠ 0 := by
  intro h
  apply hv
  have h0 : v 0 = 0 := by simpa using congrArg Complex.re h
  have h1 : v 1 = 0 := by simpa using congrArg Complex.im h
  ext i; fin_cases i <;> simp [h0, h1]
theorem conj_toC_ne {v : Plane} (hv : v ≠ 0) : conj (toC v) ≠ 0 :=
  (map_ne_zero _).mpr (toC_ne hv)
noncomputable def dirC (v : Plane) : ℂ := toC v / conj (toC v)
theorem dirC_ne {v : Plane} (hv : v ≠ 0) : dirC v ≠ 0 :=
  div_ne_zero (toC_ne hv) (conj_toC_ne hv)
theorem inner_coords (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
theorem norm_sq_coords (u : Plane) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coords]; ring
theorem dirC_neg (v : Plane) : dirC (-v) = dirC v := by
  unfold dirC toC
  by_cases h : (⟨v 0, v 1⟩ : ℂ) = 0
  · have h' : (⟨(-v) 0, (-v) 1⟩ : ℂ) = 0 := by
      have h0 := congrArg Complex.re h; have h1 := congrArg Complex.im h
      simp at h0 h1; apply Complex.ext <;> simp [h0, h1]
    rw [h, h']
  · have hc : conj (⟨v 0, v 1⟩ : ℂ) ≠ 0 := (map_ne_zero _).mpr h
    have e : (⟨(-v) 0, (-v) 1⟩ : ℂ) = -⟨v 0, v 1⟩ := by apply Complex.ext <;> simp
    rw [e, map_neg, neg_div_neg_eq]
theorem dirC_of_cross {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) (h : cross u v = 0) :
    dirC v = dirC u := by
  unfold dirC
  rw [div_eq_div_iff (conj_toC_ne hv) (conj_toC_ne hu)]
  simp only [cross] at h
  apply Complex.ext <;> simp <;> linarith
theorem dirC_of_inner {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) (h : inner ℝ u v = 0) :
    dirC v = -dirC u := by
  unfold dirC
  rw [← neg_div, div_eq_div_iff (conj_toC_ne hv) (conj_toC_ne hu)]
  rw [inner_coords] at h
  apply Complex.ext <;> simp <;> linarith
theorem dirC_of_angle {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) :
    dirC v = Complex.exp (2 * InnerProductGeometry.angle u v * Complex.I) * dirC u ∨
      dirC v = Complex.exp (-(2 * InnerProductGeometry.angle u v) * Complex.I) * dirC u := by
  set φ := InnerProductGeometry.angle u v
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hcos : inner ℝ u v = ‖u‖ * ‖v‖ * Real.cos φ := by
    rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm]; ring
  have hsin0 : 0 ≤ Real.sin φ := Real.sin_nonneg_of_nonneg_of_le_pi
    (InnerProductGeometry.angle_nonneg u v) (InnerProductGeometry.angle_le_pi u v)
  have hlag : inner ℝ u v ^ 2 + cross u v ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
    rw [inner_coords, norm_sq_coords, norm_sq_coords]; simp only [cross]; ring
  have hcr : cross u v = ‖u‖ * ‖v‖ * Real.sin φ ∨ cross u v = -(‖u‖ * ‖v‖ * Real.sin φ) := by
    have : cross u v ^ 2 = (‖u‖ * ‖v‖ * Real.sin φ) ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ
      rw [hcos] at hlag
      linear_combination hlag - (‖u‖ ^ 2 * ‖v‖ ^ 2) * this
    exact sq_eq_sq_iff_eq_or_eq_neg.mp this
  have hw : toC v * conj (toC u) = (inner ℝ u v : ℂ) + (cross u v : ℂ) * Complex.I := by
    rw [inner_coords]; simp only [cross]; apply Complex.ext <;> simp <;> ring
  have key : ∀ ψ : ℝ, cross u v = ‖u‖ * ‖v‖ * Real.sin ψ → Real.cos ψ = Real.cos φ →
      dirC v = Complex.exp (2 * ψ * Complex.I) * dirC u := by
    intro ψ hs hc
    have hw' : toC v * conj (toC u) = ((‖u‖ * ‖v‖ : ℝ) : ℂ) * Complex.exp (ψ * Complex.I) := by
      rw [hw, hcos, hs, ← hc, Complex.exp_mul_I]
      push_cast; ring
    have hwc : conj (toC v) * toC u = ((‖u‖ * ‖v‖ : ℝ) : ℂ) * Complex.exp (-(ψ * Complex.I)) := by
      have := congrArg conj hw'
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at this
      rw [this]; congr 1; rw [← Complex.exp_conj]; congr 1; simp
    have hr : ((‖u‖ * ‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mul_pos hnu hnv).ne'
    unfold dirC
    rw [div_eq_iff (conj_toC_ne hv)]
    have e2 : Complex.exp (2 * ψ * Complex.I) =
        Complex.exp (ψ * Complex.I) / Complex.exp (-(ψ * Complex.I)) := by
      rw [← Complex.exp_sub]; ring_nf
    rw [e2]
    field_simp [conj_toC_ne hu, Complex.exp_ne_zero]
    linear_combination Complex.exp (-(ψ * Complex.I)) * hw' - Complex.exp (ψ * Complex.I) * hwc
  rcases hcr with h | h
  · exact Or.inl (key φ h rfl)
  · right
    have := key (-φ) (by rw [Real.sin_neg]; linarith) (Real.cos_neg φ)
    rw [this]; push_cast; ring_nf
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry MeasureTheory
theorem cross_apply (u v : Plane) : cross u v = u 0 * v 1 - u 1 * v 0 := rfl
theorem coords_ne {v : Plane} (hv : v ≠ 0) : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  ext i; fin_cases i <;> simp [h.1, h.2]
theorem cross_trans {v w x : Plane} (hv : v ≠ 0) (hw : cross v w = 0) (hx : cross v x = 0) :
    cross w x = 0 := by
  rw [cross_apply] at *
  have e0 : v 0 * (w 0 * x 1 - w 1 * x 0) = 0 := by linear_combination w 0 * hx - x 0 * hw
  have e1 : v 1 * (w 0 * x 1 - w 1 * x 0) = 0 := by linear_combination w 1 * hx - x 1 * hw
  rcases coords_ne hv with h | h
  · exact (mul_eq_zero.mp e0).resolve_left h
  · exact (mul_eq_zero.mp e1).resolve_left h
theorem cross_comm_zero {v w : Plane} (h : cross v w = 0) : cross w v = 0 := by
  rw [cross_apply] at *; linarith
theorem cross_sub_eq (v x y z : Plane) : cross v (x - z) = cross v (x - y) + cross v (y - z) := by
  simp only [cross_apply, PiLp.sub_apply]; ring
theorem eq_smul_of_cross {v w : Plane} (hv : v ≠ 0) (h : cross v w = 0) :
    ∃ t : ℝ, w = t • v := by
  rw [cross_apply] at h
  rcases coords_ne hv with h0 | h1
  · refine ⟨w 0 / v 0, ?_⟩
    ext i; fin_cases i
    · simp [div_mul_cancel₀ _ h0]
    · simp; field_simp; linarith
  · refine ⟨w 1 / v 1, ?_⟩
    ext i; fin_cases i
    · simp; field_simp; linarith
    · simp [div_mul_cancel₀ _ h1]
def lineSet (P Q : Plane) : Set Plane := {y | cross (Q - P) y = cross (Q - P) P}
theorem mem_lineSet_iff {P Q y : Plane} : y ∈ lineSet P Q ↔ cross (Q - P) (y - P) = 0 := by
  simp only [lineSet, Set.mem_setOf_eq, cross_apply, PiLp.sub_apply]
  constructor <;> intro h <;> linarith
theorem left_mem_lineSet (P Q : Plane) : P ∈ lineSet P Q := by
  rw [mem_lineSet_iff, sub_self]; exact cross_zero_right _
theorem right_mem_lineSet (P Q : Plane) : Q ∈ lineSet P Q := by
  rw [mem_lineSet_iff]; exact cross_self _
theorem segment_subset_lineSet (P Q : Plane) : segment ℝ P Q ⊆ lineSet P Q := by
  intro y hy
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  rw [mem_lineSet_iff]
  simp only [cross_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have : a = 1 - b := by linarith
  subst this; ring
theorem lineSet_eq {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hP'Q' : P' ≠ Q')
    (hP' : P' ∈ lineSet P Q) (hQ' : Q' ∈ lineSet P Q) : lineSet P' Q' = lineSet P Q := by
  rw [mem_lineSet_iff] at hP' hQ'
  have hv : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have hv' : Q' - P' ≠ 0 := sub_ne_zero.mpr hP'Q'.symm
  have hvv : cross (Q - P) (Q' - P') = 0 := by
    rw [cross_sub_eq _ Q' P P']
    have : cross (Q - P) (P - P') = - cross (Q - P) (P' - P) := by
      simp only [cross_apply, PiLp.sub_apply]; ring
    rw [this, hP', hQ']; ring
  ext y
  rw [mem_lineSet_iff, mem_lineSet_iff]
  constructor
  · intro h
    have h1 := cross_trans hv' (cross_comm_zero hvv) h
    rw [cross_sub_eq _ y P' P, h1, hP', add_zero]
  · intro h
    have h1 : cross (Q - P) (y - P') = 0 := by
      have := cross_sub_eq (Q - P) y P' P
      rw [h, hP'] at this; linarith
    exact cross_trans hv hvv h1
theorem dirC_lineSet {P Q P' Q' : Plane} (hPQ : P ≠ Q) (hP'Q' : P' ≠ Q')
    (hP' : P' ∈ lineSet P Q) (hQ' : Q' ∈ lineSet P Q) : dirC (Q' - P') = dirC (Q - P) := by
  rw [mem_lineSet_iff] at hP' hQ'
  have hv : Q - P ≠ 0 := sub_ne_zero.mpr hPQ.symm
  have hv' : Q' - P' ≠ 0 := sub_ne_zero.mpr hP'Q'.symm
  apply dirC_of_cross hv hv'
  rw [cross_sub_eq _ Q' P P']
  have : cross (Q - P) (P - P') = - cross (Q - P) (P' - P) := by
    simp only [cross_apply, PiLp.sub_apply]; ring
  rw [this, hP', hQ']; ring
theorem eq_lineMap_of_mem_lineSet {P Q y : Plane} (hPQ : P ≠ Q) (hy : y ∈ lineSet P Q) :
    ∃ t : ℝ, y = P + t • (Q - P) := by
  rw [mem_lineSet_iff] at hy
  obtain ⟨t, ht⟩ := eq_smul_of_cross (sub_ne_zero.mpr hPQ.symm) hy
  exact ⟨t, by rw [← ht]; abel⟩
variable {N : ℕ} (D : Dissection N)
theorem tile_pts_ne (i : Fin N) (k : Fin 3) : (D.tile i).pts k ≠ (D.tile i).pts (k + 1) := by
  intro h
  have h1 := (D.tile i).indep.injective h
  have h2 : ∀ m : Fin 3, m ≠ m + 1 := by decide
  exact h2 k h1
def edgeLine (e : Fin N × Fin 3) : Set Plane :=
  lineSet ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
theorem edge_subset_target (e : Fin N × Fin 3) : (D.tile e.1).edge e.2 ⊆ D.target.carrier :=
  ((D.tile e.1).edge_subset_carrier e.2).trans (tile_subset_target D e.1)
theorem segment_subset_side_of_mem {P Q y : Plane} {i : Fin 3} (hP : P ∈ D.target.carrier)
    (hQ : Q ∈ D.target.carrier) (hy : y ∈ openSegment ℝ P Q)
    (hyi : y ∈ segment ℝ (D.target.pts i) (D.target.pts (i + 1))) :
    segment ℝ P Q ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
  obtain ⟨f, c, -, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  have hS := target_contact_side D.target f c hle hi hi1 hi2
  rw [← hS] at hyi ⊢
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have hfy := hyi.2
  simp only [map_add, map_smul, smul_eq_mul] at hfy
  have hfP := hle P hP
  have hfQ := hle Q hQ
  have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
  have h1 : a * f P ≤ a * c := mul_le_mul_of_nonneg_left hfP ha.le
  have h2 : b * f Q ≤ b * c := mul_le_mul_of_nonneg_left hfQ hb.le
  have e1 : f P = c := by
    by_contra h
    have := mul_lt_mul_of_pos_left (lt_of_le_of_ne hfP h) ha
    linarith
  have e2 : f Q = c := by
    by_contra h
    have := mul_lt_mul_of_pos_left (lt_of_le_of_ne hfQ h) hb
    linarith
  exact (Convex.segment_subset (by
    intro x hx z hz s t hs ht hst
    refine ⟨D.target.convex hx.1 hz.1 hs ht hst, ?_⟩
    simp only [map_add, map_smul, smul_eq_mul, hx.2, hz.2]
    rw [← add_mul, hst, one_mul]) ⟨hP, e1⟩ ⟨hQ, e2⟩)
theorem edge_internal_or_side (e : Fin N × Fin 3) :
    openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ⊆
        interior D.target.carrier ∨
      ∃ i : Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨hni, hside⟩ := h
  obtain ⟨y, hy, hyint⟩ := Set.not_subset.mp hni
  have hP := edge_subset_target D e (left_mem_segment ℝ _ _)
  have hQ := edge_subset_target D e (right_mem_segment ℝ _ _)
  have hyc : y ∈ D.target.carrier :=
    edge_subset_target D e (openSegment_subset_segment ℝ _ _ hy)
  have hfr : y ∈ frontier D.target.carrier := ⟨subset_closure hyc, hyint⟩
  rcases tri_frontier_subset_sides D.target hfr with h0 | h1 | h2
  · exact hside 0 (segment_subset_side_of_mem D hP hQ hy h0)
  · exact hside 1 (segment_subset_side_of_mem D hP hQ hy h1)
  · exact hside 2 (segment_subset_side_of_mem D (i := 2) hP hQ hy h2)
theorem line_balance (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0)
    (hint : ∀ e ∈ D.lineChain f c ∪ D.lineChain (-f) (-c),
      openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ⊆
        interior D.target.carrier) :
    ∑ e ∈ D.lineChain f c, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      ∑ e ∈ D.lineChain (-f) (-c), dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := by
  set μ := (Measure.hausdorffMeasure 1 : Measure Plane)
  set near := D.lineChain f c
  set far := D.lineChain (-f) (-c)
  have hnear : ∀ e ∈ near, ∑ e' ∈ far, μ ((D.tile e'.1).edge e'.2 ∩ (D.tile e.1).edge e.2) =
      μ ((D.tile e.1).edge e.2) := by
    intro e he
    have hE := D.lineChain_edge_subset he
    exact D.wall_partition (-f) (-c) (neg_ne_zero.mpr hf) (tile_pts_ne D e.1 e.2)
      (fun y hy => by simp [hE y hy]) (hint e (Finset.mem_union_left _ he))
      (fun y hy => D.edge_point_not_interior (openSegment_subset_segment ℝ _ _ hy))
  have hfar : ∀ e ∈ far, ∑ e' ∈ near, μ ((D.tile e'.1).edge e'.2 ∩ (D.tile e.1).edge e.2) =
      μ ((D.tile e.1).edge e.2) := by
    intro e he
    have hE := D.lineChain_edge_subset he
    exact D.wall_partition f c hf (tile_pts_ne D e.1 e.2)
      (fun y hy => by have := hE y hy; simp at this; simpa using this)
      (hint e (Finset.mem_union_right _ he))
      (fun y hy => D.edge_point_not_interior (openSegment_subset_segment ℝ _ _ hy))
  have hμ : ∑ e ∈ near, μ ((D.tile e.1).edge e.2) = ∑ e ∈ far, μ ((D.tile e.1).edge e.2) := by
    calc ∑ e ∈ near, μ ((D.tile e.1).edge e.2)
        = ∑ e ∈ near, ∑ e' ∈ far, μ ((D.tile e'.1).edge e'.2 ∩ (D.tile e.1).edge e.2) :=
          Finset.sum_congr rfl fun e he => (hnear e he).symm
      _ = ∑ e' ∈ far, ∑ e ∈ near, μ ((D.tile e.1).edge e.2 ∩ (D.tile e'.1).edge e'.2) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
            rw [Set.inter_comm]
      _ = ∑ e ∈ far, μ ((D.tile e.1).edge e.2) := Finset.sum_congr rfl fun e he => hfar e he
  have hconv : ∀ s : Finset (Fin N × Fin 3), ∑ e ∈ s, μ ((D.tile e.1).edge e.2) =
      ENNReal.ofReal (∑ e ∈ s, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) := by
    intro s
    rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg)]
    exact Finset.sum_congr rfl fun e _ => by rw [Tri.hausdorff_edge, edist_dist]
  rw [hconv, hconv] at hμ
  exact (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun _ _ => dist_nonneg)
    (Finset.sum_nonneg fun _ _ => dist_nonneg)).mp hμ
open Classical in
theorem side_sum (i : Fin 3) :
    ∑ e ∈ Finset.univ.filter (fun e : Fin N × Fin 3 =>
        (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1))),
      dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      dist (D.target.pts i) (D.target.pts (i + 1)) := by
  set Pt := Finset.univ.filter (fun e : Fin N × Fin 3 =>
    (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
  obtain ⟨f, c, hf, hle, hi, hi1, hi2⟩ := exists_supporting D.target i
  have hS := target_contact_side D.target f c hle hi hi1 hi2
  obtain ⟨part, hcov, -, -⟩ := D.side_walk i
  have hline : ∀ e ∈ Pt, ∀ y ∈ (D.tile e.1).edge e.2, f y = c := by
    intro e he y hy
    have h1 := (Finset.mem_filter.mp he).2 hy
    rw [← hS] at h1
    exact h1.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, f y ≤ c :=
    fun e y hy => hle y (tile_subset_target D e.1 hy)
  have hsum := sum_hausdorff_of_partition Pt (fun e => (D.tile e.1).edge e.2)
    (segment ℝ (D.target.pts i) (D.target.pts (i + 1))) ∅ Set.finite_empty
    (fun e _ => ((D.tile e.1).isClosed_edge e.2).measurableSet)
    (fun e₁ h₁ e₂ h₂ hne => D.sameside_edges_subsingleton f c hf hne (hleT e₁) (hleT e₂)
      (hline e₁ h₁) (hline e₂ h₂))
    (fun e he => (Finset.mem_filter.mp he).2)
    (by
      intro y hy
      rw [Set.diff_empty, ← hcov] at hy
      obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
      refine Set.mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hye⟩
      intro z hz
      rw [← hcov]
      exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩)
  rw [MeasureTheory.hausdorffMeasure_segment] at hsum
  have h1 : ENNReal.ofReal
      (∑ e ∈ Pt, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) =
      ENNReal.ofReal (dist (D.target.pts i) (D.target.pts (i + 1))) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => dist_nonneg), ← edist_dist, ← hsum]
    exact Finset.sum_congr rfl fun e _ => by rw [Tri.hausdorff_edge, edist_dist]
  exact (ENNReal.ofReal_eq_ofReal_iff (Finset.sum_nonneg fun _ _ => dist_nonneg)
    dist_nonneg).mp h1
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem right_area_core {N : ℕ} (D : CongruentDissection N) {a b c X Y : ℝ}
    (ha : dist (D.model.pts 1) (D.model.pts 2) = a)
    (hb : dist (D.model.pts 2) (D.model.pts 0) = b)
    (hc : dist (D.model.pts 0) (D.model.pts 1) = c)
    (hX : dist (D.target.pts 0) (D.target.pts 1) = X)
    (hY : dist (D.target.pts 2) (D.target.pts 0) = Y)
    (hright : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) =
      ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0))
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) =
      ∠ (D.model.pts 2) (D.model.pts 1) (D.model.pts 0)) :
    dist (D.target.pts 1) (D.target.pts 2) = X ∧ c * Y = 2 * a * X ∧
      2 * X ^ 2 = N * c ^ 2 := by
  set M := D.model.pts with hM
  set T := D.target.pts with hT
  set X' := dist (T 1) (T 2) with hX'
  set k := Real.cos (∠ (M 2) (M 1) (M 0)) with hk
  obtain ⟨m1, m2, m3⟩ := strict_triangle_ineqs (tri_indep D.model)
  rw [ha, hb, hc] at m1 m2 m3
  obtain ⟨t1, t2, t3⟩ := strict_triangle_ineqs (tri_indep D.target)
  rw [hX, hY] at t1 t2 t3
  rw [← hX'] at t1 t2 t3
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hY0 : 0 < Y := by linarith
  have hpyth : c ^ 2 = a ^ 2 + b ^ 2 := by
    have := law_cos (M 0) (M 2) (M 1)
    rw [hright, Real.cos_pi_div_two, dist_comm (M 0) (M 2), hb, ha, hc] at this
    linear_combination this
  have hak : a = c * k := by
    have := law_cos (M 2) (M 1) (M 0)
    rw [← hk, dist_comm (M 2) (M 1), ha, hc, hb] at this
    have h : 2 * a * (a - c * k) = 0 := by linear_combination -this - hpyth
    have := (mul_eq_zero.mp h).resolve_left (by positivity)
    linarith
  have eA : X' ^ 2 = X ^ 2 + Y ^ 2 - 2 * X * Y * k := by
    have := law_cos (T 1) (T 0) (T 2)
    rw [hA, ← hk, dist_comm (T 1) (T 0), hX, hY] at this
    linear_combination this
  have eC : X ^ 2 = X' ^ 2 + Y ^ 2 - 2 * X' * Y * k := by
    have := law_cos (T 1) (T 2) (T 0)
    rw [hC, ← hk, dist_comm (T 1) (T 0), hX, dist_comm (T 0) (T 2), hY] at this
    linear_combination this
  have hk0 : 0 < k := by
    have : 0 < c * k := hak ▸ ha0
    exact pos_of_mul_pos_right this hc0.le
  have hXX : X' = X := by
    have h0 : (X' - X) * (X' + X - Y * k) = 0 := by linear_combination (eA - eC) / 2
    have h1 : X' + X - Y * k ≠ 0 := by nlinarith
    have := (mul_eq_zero.mp h0).resolve_right h1
    linarith
  have hYk : Y = 2 * X * k := by
    rw [hXX] at eA
    have : Y * (Y - 2 * X * k) = 0 := by linear_combination -eA
    have := (mul_eq_zero.mp this).resolve_left hY0.ne'
    linarith
  refine ⟨hXX, by rw [hYk, hak]; ring, ?_⟩
  have hH := area_heron D
  rw [ha, hb, hc, ← hX', hXX, hY, hX] at hH
  have hH1 : heron16 a b c = 4 * a ^ 2 * b ^ 2 := by
    unfold heron16
    have h4 : c ^ 4 = (a ^ 2 + b ^ 2) ^ 2 := by rw [show c ^ 4 = (c ^ 2) ^ 2 by ring, hpyth]
    rw [h4, hpyth]; ring
  have hH2 : heron16 X Y X = 16 * X ^ 4 * k ^ 2 * (1 - k ^ 2) := by
    unfold heron16; rw [hYk]; ring
  rw [hH1, hH2] at hH
  have hk2 : c ^ 2 * (1 - k ^ 2) = b ^ 2 := by
    have : c ^ 2 * k ^ 2 = a ^ 2 := by rw [hak]; ring
    linarith
  have h4 : a ^ 2 * b ^ 2 * (((N : ℝ) * c ^ 2) ^ 2 - (2 * X ^ 2) ^ 2) = 0 := by
    have e : c ^ 4 * ((N : ℝ) ^ 2 * (4 * a ^ 2 * b ^ 2)) =
        c ^ 4 * (16 * X ^ 4 * k ^ 2 * (1 - k ^ 2)) := by rw [hH]
    have e2 : c ^ 4 * (16 * X ^ 4 * k ^ 2 * (1 - k ^ 2)) = 16 * X ^ 4 * a ^ 2 * b ^ 2 := by
      have : c ^ 4 * (k ^ 2 * (1 - k ^ 2)) = a ^ 2 * b ^ 2 := by
        rw [← hk2]; rw [hak]; ring
      linear_combination 16 * X ^ 4 * this
    linear_combination (e.trans e2) / 4
  have h5 := (mul_eq_zero.mp h4).resolve_left (by positivity)
  have h6 : ((N : ℝ) * c ^ 2 - 2 * X ^ 2) * ((N : ℝ) * c ^ 2 + 2 * X ^ 2) = 0 := by
    linear_combination h5
  have h7 : 0 < (N : ℝ) * c ^ 2 + 2 * X ^ 2 := by
    have : 0 < X := by linarith
    positivity
  have := (mul_eq_zero.mp h6).resolve_right h7.ne'
  linarith
end TriangleTiling
end

section
namespace TriangleTiling
open Polynomial
def InQ (l v : ℝ) : Prop := ∃ x y : ℚ, v = x * l + y
section
variable {l : ℝ} {d : ℚ} (hl : l ^ 2 = d) (hirr : ¬ ∃ q : ℚ, l = q)
theorem InQ.rat (q : ℚ) : InQ l q := ⟨0, q, by simp⟩
theorem InQ.self : InQ l l := ⟨1, 0, by simp⟩
theorem InQ.add {v w : ℝ} (hv : InQ l v) (hw : InQ l w) : InQ l (v + w) := by
  obtain ⟨x, y, rfl⟩ := hv
  obtain ⟨z, u, rfl⟩ := hw
  exact ⟨x + z, y + u, by push_cast; ring⟩
theorem InQ.neg {v : ℝ} (hv : InQ l v) : InQ l (-v) := by
  obtain ⟨x, y, rfl⟩ := hv
  exact ⟨-x, -y, by push_cast; ring⟩
theorem InQ.sub {v w : ℝ} (hv : InQ l v) (hw : InQ l w) : InQ l (v - w) := by
  rw [sub_eq_add_neg]; exact hv.add hw.neg
include hl in
theorem InQ.mul {v w : ℝ} (hv : InQ l v) (hw : InQ l w) : InQ l (v * w) := by
  obtain ⟨x, y, rfl⟩ := hv
  obtain ⟨z, u, rfl⟩ := hw
  refine ⟨x * u + y * z, x * z * d + y * u, ?_⟩
  push_cast
  linear_combination (↑x * ↑z) * hl
include hirr in
theorem InQ.indep {x y : ℚ} (h : (x : ℝ) * l + y = 0) : x = 0 ∧ y = 0 := by
  by_cases hx : x = 0
  · subst hx
    simp at h
    exact ⟨rfl, by exact_mod_cast h⟩
  · exfalso
    apply hirr
    refine ⟨-y / x, ?_⟩
    have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    push_cast
    field_simp
    linarith
include hl hirr in
theorem InQ.inv {v : ℝ} (hv : InQ l v) (hv0 : v ≠ 0) : InQ l v⁻¹ := by
  obtain ⟨x, y, rfl⟩ := hv
  have hden : (y : ℝ) ^ 2 - (x : ℝ) ^ 2 * d ≠ 0 := by
    intro h
    have h1 : ((x : ℝ) * l + y) * (y - x * l) = 0 := by
      linear_combination h - (↑x ^ 2) * hl
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hv0 h2
    · obtain ⟨hx, hy⟩ := InQ.indep hirr (x := -x) (y := y) (by push_cast; linarith)
      apply hv0
      have : x = 0 := by simpa using hx
      rw [this, hy]; simp
  have hdenQ : y ^ 2 - x ^ 2 * d ≠ 0 := by exact_mod_cast hden
  refine ⟨-x / (y ^ 2 - x ^ 2 * d), y / (y ^ 2 - x ^ 2 * d), ?_⟩
  have hv0' : (x : ℝ) * l + y ≠ 0 := hv0
  push_cast
  field_simp
  linear_combination (↑x : ℝ) ^ 2 * hl
include hl hirr in
theorem InQ.div {v w : ℝ} (hv : InQ l v) (hw : InQ l w) (hw0 : w ≠ 0) : InQ l (v / w) := by
  rw [div_eq_mul_inv]; exact hv.mul hl (hw.inv hl hirr hw0)
include hl in
theorem InQ.quadratic {v : ℝ} (hv : InQ l v) :
    ∃ P : ℚ[X], P ≠ 0 ∧ P.natDegree ≤ 2 ∧ aeval v P = 0 := by
  obtain ⟨x, y, rfl⟩ := hv
  refine ⟨(X - C y) ^ 2 - C (x ^ 2 * d), ?_, ?_, ?_⟩
  · have hdeg : degree ((X - C y) ^ 2 : ℚ[X]) = 2 := by
      rw [degree_pow, degree_X_sub_C]; rfl
    have hm : ((X - C y) ^ 2 - C (x ^ 2 * d) : ℚ[X]).Monic :=
      ((monic_X_sub_C y).pow 2).sub_of_left (lt_of_le_of_lt degree_C_le (by rw [hdeg]; norm_num))
    exact hm.ne_zero
  · compute_degree
  · simp only [map_sub, map_pow, aeval_X, aeval_C, eq_ratCast]
    push_cast
    linear_combination (↑x ^ 2 : ℝ) * hl
end
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
variable {N : ℕ} (D : CongruentDissection N)
theorem right_beta (hright : tileγ D = Real.pi / 2) : tileβ D = Real.pi / 2 - tileα D := by
  have h : tileα D + tileβ D + tileγ D = Real.pi := cornerAngle_sum D.model
  linarith
variable (hright : tileγ D = Real.pi / 2) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hright hirr
theorem anglesSep_right : AnglesSep D := by
  have hβ := right_beta D hright
  have hq : ∀ q : ℚ, tileα D ≠ (q : ℝ) * Real.pi := fun q h => hirr ⟨q, h⟩
  have hpi := Real.pi_pos
  refine ⟨fun j => ?_, fun i j h => ?_⟩
  · fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ne_eq]
    · intro h; exact hq 0 (by push_cast; linarith)
    · intro h; exact hq (1 / 2) (by push_cast; linarith)
    · rw [hright]; positivity
    · positivity
    · positivity
  · fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h ⊢ <;>
      rw [hβ, hright] at * <;>
      first
      | rfl
      | (exfalso; linarith)
      | (exfalso; exact hq (1 / 4) (by push_cast; linarith))
      | (exfalso; exact hq (1 / 2) (by push_cast; linarith))
      | (exfalso; exact hq 1 (by push_cast; linarith))
      | (exfalso; exact hq 2 (by push_cast; linarith))
      | (exfalso; exact hq 0 (by push_cast; linarith))
      | (exfalso; exact hq (-1 / 2) (by push_cast; linarith))
      | (exfalso; exact hq (-3 / 2) (by push_cast; linarith))
theorem vertex_relations_right (P : Plane) (s t : ℤ)
    (hP : D.target.localAngle P = s * tileα D + t * (Real.pi / 2)) :
    (angleCount D P (tileα D) : ℤ) - angleCount D P (tileβ D) = s ∧
    (angleCount D P (tileβ D) : ℤ) + angleCount D P (tileγ D) + 2 * angleCount D P Real.pi
      + 4 * angleCount D P (2 * Real.pi) = t := by
  obtain ⟨hv0, hinj⟩ := anglesSep_right D hright hirr
  have hβ := right_beta D hright
  have hf : ∀ i, (∃ j, (D.tile i).localAngle P =
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j) ∨ (D.tile i).localAngle P = 0 := by
    intro i
    rcases localAngle_mem D P i with h | h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inl ⟨3, h⟩
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr h
  have hcount := sum_eq_counts (fun i => (D.tile i).localAngle P) _ hv0 hinj hf
  rw [D.toDissection.sum_localAngle_eq P, Fin.sum_univ_five, hP] at hcount
  have hcount' : (angleCount D P (tileα D) : ℝ) * tileα D
      + (angleCount D P (tileβ D) : ℝ) * tileβ D + (angleCount D P (tileγ D) : ℝ) * tileγ D
      + (angleCount D P Real.pi : ℝ) * Real.pi
      + (angleCount D P (2 * Real.pi) : ℝ) * (2 * Real.pi) = s * tileα D + t * (Real.pi / 2) :=
    hcount.symm
  have key : (((2 * ((angleCount D P (tileα D) : ℤ) - angleCount D P (tileβ D) - s)) : ℤ) : ℝ)
      * tileα D + ((((angleCount D P (tileβ D) : ℤ) + angleCount D P (tileγ D)
        + 2 * angleCount D P Real.pi + 4 * angleCount D P (2 * Real.pi) - t) : ℤ) : ℝ)
        * Real.pi = 0 := by
    push_cast
    linear_combination 2 * hcount' - 2 * (angleCount D P (tileβ D) : ℝ) * hβ
      - 2 * (angleCount D P (tileγ D) : ℝ) * hright
  obtain ⟨h1, h2⟩ := angle_indep hirr _ _ key
  omega
open Classical in
theorem right_c_even {P : Plane} {t : ℤ}
    (hP : D.target.localAngle P = (0 : ℤ) * tileα D + t * (Real.pi / 2)) :
    Even ((edgesAt D.toDissection P).filter (edgeType D (tileγ D))).card := by
  have hcm := card_marked D (anglesSep_right D hright hirr) P (φ := tileγ D) (Or.inr (Or.inr rfl))
  obtain ⟨h1, -⟩ := vertex_relations_right D hright hirr P 0 t hP
  exact ⟨angleCount D P (tileβ D), by omega⟩
theorem right_side_no_relint {Q : Plane} (hfr : Q ∈ frontier D.target.carrier)
    (hnc : Q ∉ Set.range D.target.pts) {i : Fin N} {k : Fin 3} (hik : (D.tile i).pts k = Q) :
    ∀ j : Fin N, ∀ m : Fin 3, Q ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)) := by
  intro j m hQ
  have hloc : D.target.localAngle Q = (0 : ℤ) * tileα D + (2 : ℤ) * (Real.pi / 2) := by
    rw [D.target.localAngle_frontier hfr hnc]; push_cast; ring
  obtain ⟨h1, h2⟩ := vertex_relations_right D hright hirr Q 0 2 hloc
  have hπ := angleCount_pos D (Tri.localAngle_openSegment _ m hQ)
  have hpos := vertex_counts_pos D hik
  omega
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry Set
variable {N : ℕ} (D : CongruentDissection N)
noncomputable def relabelTarget (σ : Equiv.Perm (Fin 3)) : CongruentDissection N where
  target := ⟨D.target.pts ∘ σ, D.target.indep.comp_embedding σ.toEmbedding⟩
  tile := D.tile
  covers := by
    rw [D.covers]
    show convexHull ℝ (Set.range D.target.pts) = convexHull ℝ (Set.range (D.target.pts ∘ σ))
    rw [Set.range_comp, σ.range_eq_univ, Set.image_univ]
  interiors_disjoint := D.interiors_disjoint
  model := D.model
  tiles_congruent := D.tiles_congruent
theorem relabelTarget_carrier (σ : Equiv.Perm (Fin 3)) :
    (relabelTarget D σ).target.carrier = D.target.carrier := by
  show convexHull ℝ (Set.range (D.target.pts ∘ σ)) = convexHull ℝ (Set.range D.target.pts)
  rw [Set.range_comp, σ.range_eq_univ, Set.image_univ]
theorem isLink_of_relabel (σ : Equiv.Perm (Fin 3)) {isθ : Fin N × Fin 3 → Prop} {Q R : Plane}
    (h : IsLink (relabelTarget D σ).toDissection isθ Q R) : IsLink D.toDissection isθ Q R := by
  obtain ⟨g, c, h⟩ := h
  exact ⟨g, c, ⟨h.ne, h.hg, h.hQ, h.hR, h.cov, h.inner, h.start, h.past, h.across⟩⟩
open Classical in
theorem side_cover (i : Fin 3) :
    (⋃ e ∈ Finset.univ.filter fun e : Fin N × Fin 3 =>
        (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)),
      (D.tile e.1).edge e.2) = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
  obtain ⟨part, hcov, -, -⟩ := D.toDissection.side_walk i
  apply Set.Subset.antisymm
  · intro y hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
    exact (Finset.mem_filter.mp he).2 hye
  · intro y hy
    rw [← hcov] at hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy
    have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)) := by
      rw [← hcov]
      intro z hz
      exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩
    exact Set.mem_iUnion₂.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub⟩, hye⟩
theorem sides_meet (T : Tri) (m : Fin 3) {x : Plane}
    (h1 : x ∈ segment ℝ (T.pts m) (T.pts (m + 1)))
    (h2 : x ∈ segment ℝ (T.pts (m + 2)) (T.pts (m + 2 + 1))) : x = T.pts m := by
  have c1 := T.coord_eq_zero_of_mem_edge m h1
  have c2 := T.coord_eq_zero_of_mem_edge (m + 2) h2
  have hsum := Tri.coord_sum T x
  rw [show m + 2 + 2 = m + 1 by fin_cases m <;> rfl] at c2
  apply T.basis.ext_elem
  intro j
  rw [Tri.coord_vertex]
  fin_cases m <;> fin_cases j <;> simp at c1 c2 hsum ⊢ <;> linarith
variable (hright : tileγ D = Real.pi / 2) (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hright hirr
open Classical in
theorem no_mixed_side (hnorel : ¬ HasRelation D.toDissection (edgeType D (tileγ D))) (i : Fin 3)
    {e e' : Fin N × Fin 3}
    (he : (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
    (he' : (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1)))
    (hθ : edgeType D (tileγ D) e) : edgeType D (tileγ D) e' := by
  by_contra hθ'
  set D' := relabelTarget D (Equiv.addRight i)
  have h0 : D'.target.pts 0 = D.target.pts i := by
    show D.target.pts (0 + i) = _; rw [zero_add]
  have h1 : D'.target.pts 1 = D.target.pts (i + 1) := by
    show D.target.pts (1 + i) = _; rw [add_comm]
  set part := Finset.univ.filter fun e : Fin N × Fin 3 =>
    (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts i) (D.target.pts (i + 1))
  have hcov : (⋃ e ∈ part, (D'.tile e.1).edge e.2) =
      segment ℝ (D'.target.pts 0) (D'.target.pts 1) := by
    rw [h0, h1]; exact side_cover D i
  have hgood : ∀ Q ∈ openSegment ℝ (D'.target.pts 0) (D'.target.pts 1),
      (∃ j k, (D'.tile j).pts k = Q) →
        (∀ j : Fin N, ∀ m : Fin 3,
          Q ∉ openSegment ℝ ((D'.tile j).pts m) ((D'.tile j).pts (m + 1)))
          ∧ Even ((edgesAt D'.toDissection Q).filter (edgeType D (tileγ D))).card := by
    intro Q hQ ⟨j, k, hjk⟩
    rw [h0, h1] at hQ
    have hfr : Q ∈ frontier D.target.carrier :=
      tri_side_subset_frontier D.target i (openSegment_subset_segment _ _ _ hQ)
    have hnc : Q ∉ Set.range D.target.pts := by
      rintro ⟨m, hm⟩
      exact Tri.vertex_not_mem_openSegment D.target m i (hm ▸ hQ)
    refine ⟨right_side_no_relint D hright hirr hfr hnc hjk, right_c_even D hright hirr (t := 2) ?_⟩
    rw [D.target.localAngle_frontier hfr hnc]; push_cast; ring
  obtain ⟨Q₀, hQ₀, R, hR⟩ := side_start D'.toDissection (edgeType D (tileγ D)) part hcov
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'⟩)
    hθ hθ' hgood hnorel
  rw [relabelTarget_carrier] at hQ₀
  exact hnorel (relation_of_start D.toDissection _
    (fun _ _ _ _ hl => right_c_even D hright hirr (t := 4) (by
      rw [Tri.localAngle_interior _ hl.end_interior]; push_cast; ring))
    ⟨Q₀, hQ₀, R, isLink_of_relabel D _ hR⟩)
open Classical in
theorem corner_edges (m : Fin 3) (hm : D.target.localAngle (D.target.pts m) = tileβ D) :
    ∃ e e' : Fin N × Fin 3,
      (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts m) (D.target.pts (m + 1)) ∧
      (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts (m + 2)) (D.target.pts (m + 2 + 1)) ∧
      ((edgeType D (tileγ D) e ∧ ¬ edgeType D (tileγ D) e') ∨
        (¬ edgeType D (tileγ D) e ∧ edgeType D (tileγ D) e')) := by
  set A := D.target.pts m
  have hsep := anglesSep_right D hright hirr
  have hβ := right_beta D hright
  have hloc : D.target.localAngle A = (-1 : ℤ) * tileα D + (1 : ℤ) * (Real.pi / 2) := by
    rw [hm, hβ]; push_cast; ring
  obtain ⟨h1, h2⟩ := vertex_relations_right D hright hirr A (-1) 1 hloc
  have hval : ∀ i, (D.tile i).localAngle A = tileβ D ∨ (D.tile i).localAngle A = 0 := by
    intro i
    rcases localAngle_mem D A i with h | h | h | h | h | h
    · exfalso; have := angleCount_pos D (show (D.tile i).localAngle A = tileα D from h); omega
    · exact Or.inl h
    · exfalso; have := angleCount_pos D (show (D.tile i).localAngle A = tileγ D from h); omega
    · exfalso; have := angleCount_pos D h; omega
    · exfalso; have := angleCount_pos D h; omega
    · exact Or.inr h
  have huniq : ∀ i i', (D.tile i).localAngle A = tileβ D → (D.tile i').localAngle A = tileβ D →
      i = i' := by
    intro i i' hi hi'
    have hle : angleCount D A (tileβ D) ≤ 1 := by omega
    exact Finset.card_le_one.mp hle i (by simp [hi]) i' (by simp [hi'])
  have hat : ∀ (j : Fin 3) (y : Plane), (y = D.target.pts (j + 1) ∧ A = D.target.pts j) ∨
      (y = D.target.pts j ∧ A = D.target.pts (j + 1)) →
      ∃ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts j) (D.target.pts (j + 1))
        ∧ e ∈ edgesAt D.toDissection A ∧ (D.tile e.1).localAngle A = tileβ D := by
    intro j y hy
    have hA : A ∈ segment ℝ (D.target.pts j) (D.target.pts (j + 1)) := by
      rcases hy with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h]; exact left_mem_segment _ _ _
      · rw [h]; exact right_mem_segment _ _ _
    rw [← side_cover D j] at hA
    obtain ⟨e, he, hAe⟩ := Set.mem_iUnion₂.mp hA
    have hsub := (Finset.mem_filter.mp he).2
    refine ⟨e, hsub, ?_, ?_⟩
    · have hu := hsub (left_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      have hv := hsub (right_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      rw [Tri.edge] at hAe
      rcases hy with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h] at hAe ⊢
        rcases eq_endpoint_of_mem_segment hu hv hAe with h' | h'
        · exact (mem_edgesAt _).mpr (Or.inl h'.symm)
        · exact (mem_edgesAt _).mpr (Or.inr h'.symm)
      · rw [segment_symm] at hu hv
        rw [h] at hAe ⊢
        rcases eq_endpoint_of_mem_segment hu hv hAe with h' | h'
        · exact (mem_edgesAt _).mpr (Or.inl h'.symm)
        · exact (mem_edgesAt _).mpr (Or.inr h'.symm)
    · rcases hval e.1 with h | h
      · exact h
      · exact absurd h (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _
          ((D.tile e.1).edge_subset_carrier e.2 hAe))
  obtain ⟨e, hes, heA, heβ⟩ := hat m (D.target.pts (m + 1)) (Or.inl ⟨rfl, rfl⟩)
  have hm2 : m + 2 + 1 = m := by fin_cases m <;> rfl
  obtain ⟨e', hes', heA', heβ'⟩ := hat (m + 2) (D.target.pts (m + 2))
    (Or.inr ⟨rfl, by rw [hm2]⟩)
  have hii : e'.1 = e.1 := huniq _ _ heβ' heβ
  refine ⟨e, e', hes, hes', ?_⟩
  obtain ⟨i, k⟩ := e
  obtain ⟨i', k'⟩ := e'
  simp only at hii
  rw [hii] at heA' hes' heβ' ⊢
  set T := D.tile i
  obtain ⟨k0, hk0⟩ : ∃ k0, T.pts k0 = A := by
    rcases (mem_edgesAt _).mp heA with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  have hinj := T.indep.injective
  have hidx : ∀ j : Fin 3, (i, j) ∈ edgesAt D.toDissection A → j = k0 ∨ j = k0 + 2 := by
    intro j hj
    rcases (mem_edgesAt _).mp hj with h | h
    · exact Or.inl (hinj (h.trans hk0.symm))
    · right
      have := hinj (h.trans hk0.symm)
      rw [← this]; fin_cases j <;> rfl
  have hne : k ≠ k' := by
    rintro rfl
    have hF : T.pts (k + 1) ∈ segment ℝ (D.target.pts m) (D.target.pts (m + 1)) :=
      hes (right_mem_segment _ _ _)
    have hF' : T.pts (k + 1) ∈ segment ℝ (D.target.pts (m + 2)) (D.target.pts (m + 2 + 1)) :=
      hes' (right_mem_segment _ _ _)
    have hE : T.pts k ∈ segment ℝ (D.target.pts m) (D.target.pts (m + 1)) :=
      hes (left_mem_segment _ _ _)
    have hE' : T.pts k ∈ segment ℝ (D.target.pts (m + 2)) (D.target.pts (m + 2 + 1)) :=
      hes' (left_mem_segment _ _ _)
    exact tri_pts_succ_ne T k ((sides_meet D.target m hE hE').trans
      (sides_meet D.target m hF hF').symm)
  have hcnt := (tile_angle_count_sep D hsep i).2.2
  simp only [← Tri.localAngle_vertex] at hcnt
  have h3 := card_three k0 (fun j => T.localAngle (T.pts j) = tileγ D)
  rw [hcnt] at h3
  have hk0γ : ¬ T.localAngle (T.pts k0) = tileγ D := by
    rw [hk0, heβ]
    have := hsep.2.ne (show (1 : Fin 5) ≠ 2 by decide)
    exact this
  rw [if_neg hk0γ] at h3
  have hk2 : k0 + 2 + 2 = k0 + 1 := by fin_cases k0 <;> rfl
  have ht : ∀ j, edgeType D (tileγ D) (i, j) ↔ T.localAngle (T.pts (j + 2)) = tileγ D :=
    fun j => Iff.rfl
  rcases hidx k heA with rfl | rfl <;> rcases hidx k' heA' with rfl | rfl
  · exact absurd rfl hne
  · rw [ht, ht, hk2]
    by_cases hc : T.localAngle (T.pts (k + 2)) = tileγ D
    · rw [if_pos hc] at h3
      have : ¬ T.localAngle (T.pts (k + 1)) = tileγ D := by
        intro h; rw [if_pos h] at h3; omega
      exact Or.inl ⟨hc, this⟩
    · rw [if_neg hc] at h3
      have : T.localAngle (T.pts (k + 1)) = tileγ D := by
        by_contra h; rw [if_neg h] at h3; omega
      exact Or.inr ⟨hc, this⟩
  · rw [ht, ht, hk2]
    by_cases hc : T.localAngle (T.pts (k' + 2)) = tileγ D
    · rw [if_pos hc] at h3
      have : ¬ T.localAngle (T.pts (k' + 1)) = tileγ D := by
        intro h; rw [if_pos h] at h3; omega
      exact Or.inr ⟨this, hc⟩
    · rw [if_neg hc] at h3
      have : T.localAngle (T.pts (k' + 1)) = tileγ D := by
        by_contra h; rw [if_neg h] at h3; omega
      exact Or.inl ⟨this, hc⟩
  · exact absurd rfl hne
variable (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
include hA hC
theorem allc (hnorel : ¬ ∃ j u v : ℕ, 0 < j ∧
      (j : ℝ) * dist (D.model.pts 0) (D.model.pts 1)
        = u * dist (D.model.pts 1) (D.model.pts 2) + v * dist (D.model.pts 2) (D.model.pts 0)) :
    ((∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
        edgeType D (tileγ D) e) ∧
      ∀ e : Fin N × Fin 3,
        ((D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) ∨
          (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2)) →
        ¬ edgeType D (tileγ D) e) ∨
    ((∀ e : Fin N × Fin 3,
        ((D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) ∨
          (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2)) →
        edgeType D (tileγ D) e) ∧
      ∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
        ¬ edgeType D (tileγ D) e) := by
  have hnorelE : ¬ HasRelation D.toDissection (edgeType D (tileγ D)) := fun h =>
    hnorel (c_relation_of_edges D (anglesSep_right D hright hirr) h)
  have mix := no_mixed_side D hright hirr hnorelE
  have m0 : ∀ {e e'}, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) →
      (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) →
        edgeType D (tileγ D) e → edgeType D (tileγ D) e' := fun he he' => mix 0 he he'
  have m1 : ∀ {e e'}, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2) →
      (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2) →
        edgeType D (tileγ D) e → edgeType D (tileγ D) e' := fun he he' => mix 1 he he'
  have m2 : ∀ {e e'}, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
      (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
        edgeType D (tileγ D) e → edgeType D (tileγ D) e' := fun he he' => mix 2 he he'
  have hmA : D.target.localAngle (D.target.pts 0) = tileβ D := by
    rw [Tri.localAngle_vertex]; exact hA
  have hmC : D.target.localAngle (D.target.pts 2) = tileβ D := by
    rw [Tri.localAngle_vertex]
    show ∠ (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = _
    rw [angle_comm]; exact hC
  obtain ⟨e, e', he, he', hA'⟩ := corner_edges D hright hirr 0 hmA
  obtain ⟨f, f', hf, hf', hC'⟩ := corner_edges D hright hirr 2 hmC
  change (D.tile e'.1).edge e'.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) at he'
  change (D.tile f.1).edge f.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) at hf
  change (D.tile f'.1).edge f'.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2) at hf'
  rcases hA' with ⟨hc, hnc⟩ | ⟨hnc, hc⟩
  · 
    have hAC : ∀ x, (D.tile x.1).edge x.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
        ¬ edgeType D (tileγ D) x := fun x hx hcx => hnc (m2 hx he' hcx)
    rcases hC' with ⟨hc2, -⟩ | ⟨-, hc1⟩
    · exact absurd hc2 (hAC f hf)
    · right
      refine ⟨fun x hx => ?_, hAC⟩
      rcases hx with hx | hx
      · exact m0 he hx hc
      · exact m1 hf' hx hc1
  · 
    have hAB : ∀ x, (D.tile x.1).edge x.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) →
        ¬ edgeType D (tileγ D) x := fun x hx hcx => hnc (m0 hx he hcx)
    rcases hC' with ⟨-, hn1⟩ | ⟨hn2, -⟩
    · left
      refine ⟨fun x hx => m2 he' hx hc, fun x hx => ?_⟩
      rcases hx with hx | hx
      · exact hAB x hx
      · exact fun hcx => hn1 (m1 hx hf' hcx)
    · exact absurd (m2 he' hf hc) hn2
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry Polynomial
variable {N : ℕ} (D : CongruentDissection N)
theorem right_trig (hright : tileγ D = Real.pi / 2) :
    dist (D.model.pts 1) (D.model.pts 2) =
        Real.cos (tileβ D) * dist (D.model.pts 0) (D.model.pts 1) ∧
      dist (D.model.pts 2) (D.model.pts 0) =
        Real.cos (tileα D) * dist (D.model.pts 0) (D.model.pts 1) := by
  have h1 : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = Real.pi / 2 := hright
  have h2 : ∠ (D.model.pts 1) (D.model.pts 2) (D.model.pts 0) = Real.pi / 2 := by
    rw [angle_comm]; exact h1
  constructor
  · exact (cos_angle_mul_dist_of_angle_eq_pi_div_two h1).symm
  · have := cos_angle_mul_dist_of_angle_eq_pi_div_two h2
    have e : ∠ (D.model.pts 2) (D.model.pts 0) (D.model.pts 1) = tileα D := angle_comm _ _ _
    rw [e, dist_comm (D.model.pts 1) (D.model.pts 0)] at this
    rw [dist_comm (D.model.pts 2) (D.model.pts 0)]
    exact this.symm
theorem tileα_pos : 0 < tileα D := Erdos634.MarchFlank.cornerAngle_pos D.model 0
theorem tileβ_pos : 0 < tileβ D := Erdos634.MarchFlank.cornerAngle_pos D.model 1
theorem anglesSep_right' (hright : tileγ D = Real.pi / 2) (hαβ : tileα D ≠ tileβ D) :
    AnglesSep D := by
  have hβ := right_beta D hright
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  have hpi := Real.pi_pos
  refine ⟨fun j => ?_, fun i j h => ?_⟩
  · fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ne_eq] <;>
      first | exact hα0.ne' | exact hβ0.ne' | (rw [hright]; positivity) | positivity
  · fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h ⊢ <;>
      first
      | rfl
      | exact absurd h hαβ
      | exact absurd h.symm hαβ
      | (exfalso; rw [hright] at h; linarith)
      | (exfalso; rw [hβ] at h; linarith)
      | (exfalso; linarith)
theorem legs_eq_iff (hright : tileγ D = Real.pi / 2) :
    dist (D.model.pts 1) (D.model.pts 2) = dist (D.model.pts 2) (D.model.pts 0) →
      tileα D = tileβ D := by
  intro h
  obtain ⟨ha, hb⟩ := right_trig D hright
  have hc : 0 < dist (D.model.pts 0) (D.model.pts 1) :=
    dist_pos.mpr fun e => by have := D.model.indep.injective e; exact absurd this (by decide)
  rw [ha, hb] at h
  have hcos := mul_right_cancel₀ hc.ne' h
  have hβ := right_beta D hright
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  exact (Real.injOn_cos ⟨hβ0.le, by linarith [Real.pi_pos]⟩
    ⟨hα0.le, by linarith [Real.pi_pos]⟩ hcos).symm
theorem corner_perm_dist {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), (∀ k : Fin 3,
      cornerAngle (U.pts (σ k + 1)) (U.pts (σ k)) (U.pts (σ k + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))) ∧
      ∀ j k, dist (T.pts j) (T.pts k) = dist (U.pts (σ j)) (U.pts (σ k)) := by
  obtain ⟨f, σ, hf⟩ := h
  refine ⟨σ, fun k => ?_, fun j k => by rw [← hf j, ← hf k, f.dist_eq]⟩
  have hmap : cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2)))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by
    rw [← hf (k + 1), ← hf k, ← hf (k + 2)]
    rw [Erdos634.Geometry.cornerAngle, Erdos634.Geometry.cornerAngle]
    rw [show (f : Plane → Plane) = f.toRealAffineIsometryEquiv from
      (IsometryEquiv.coeFn_toRealAffineIsometryEquiv f).symm]
    exact f.toRealAffineIsometryEquiv.toAffineIsometry.angle_map _ _ _
  have hidx : ∀ x y z : Fin 3, x ≠ y → x ≠ z → y ≠ z →
      (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by decide
  have hne : ∀ x : Fin 3, x ≠ x + 1 ∧ x ≠ x + 2 ∧ x + 1 ≠ x + 2 := by decide
  obtain ⟨h1, h2, h12⟩ := hne k
  rcases hidx (σ k) (σ (k + 1)) (σ (k + 2))
      (fun he => h1 (σ.injective he)) (fun he => h2 (σ.injective he))
      (fun he => h12 (σ.injective he)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [← ha, ← hb]; exact hmap
  · rw [← ha, ← hb]
    rw [Erdos634.Geometry.cornerAngle, EuclideanGeometry.angle_comm]
    exact hmap
theorem model_corner (k : Fin 3) :
    cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) =
      ![tileα D, tileβ D, tileγ D] k := by
  fin_cases k <;> rfl


theorem a_edge_end_angles (hab : dist (D.model.pts 1) (D.model.pts 2) =
      dist (D.model.pts 2) (D.model.pts 0) → tileα D = tileβ D)
    (hac : dist (D.model.pts 1) (D.model.pts 2) ≠ dist (D.model.pts 0) (D.model.pts 1))
    (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) =
      dist (D.model.pts 1) (D.model.pts 2)) (j : Fin 3) (hj : j = k ∨ j = k + 1) :
    (D.tile i).localAngle ((D.tile i).pts j) = tileβ D ∨
      (D.tile i).localAngle ((D.tile i).pts j) = tileγ D := by
  obtain ⟨σ, hang, hd⟩ := corner_perm_dist (D.tiles_congruent i)
  rw [Tri.localAngle_vertex, ← hang, model_corner]
  rw [hd] at hlen
  have hne : σ k ≠ σ (k + 1) := σ.injective.ne (by fin_cases k <;> decide)
  rcases hj with rfl | rfl
  · generalize σ (j + 1) = v at hne hlen ⊢
    generalize σ j = u at hne hlen ⊢
    fin_cases u <;> fin_cases v <;> simp at hne hlen ⊢ <;>
      first
      | exact Or.inl rfl | exact Or.inr rfl
      | exact absurd hlen.symm hac | exact absurd hlen hac
      | (rw [dist_comm] at hlen; exact absurd hlen.symm hac)
      | (rw [dist_comm] at hlen; exact absurd hlen hac)
      | (left; exact hab hlen.symm) | (left; exact hab hlen)
      | (rw [dist_comm] at hlen; left; exact hab hlen.symm)
      | (rw [dist_comm] at hlen; left; exact hab hlen)
  · generalize σ (k + 1) = v at hne hlen ⊢
    generalize σ k = u at hne hlen ⊢
    fin_cases u <;> fin_cases v <;> simp at hne hlen ⊢ <;>
      first
      | exact Or.inl rfl | exact Or.inr rfl
      | exact absurd hlen.symm hac | exact absurd hlen hac
      | (rw [dist_comm] at hlen; exact absurd hlen.symm hac)
      | (rw [dist_comm] at hlen; exact absurd hlen hac)
      | (left; exact hab hlen.symm) | (left; exact hab hlen)
      | (rw [dist_comm] at hlen; left; exact hab hlen.symm)
      | (rw [dist_comm] at hlen; left; exact hab hlen)
theorem cramer {l : ℝ} {d : ℚ} (hl : l ^ 2 = d) (hirr : ¬ ∃ q : ℚ, l = q) {a b : ℝ}
    {p q r s t u : ℕ} (h1 : l = p * a + q * b + r) (h2 : 2 * a * l = s * a + t * b + u) :
    (InQ l a ∧ InQ l b) ∨ (q = 0 ∧ r = 0 ∧ s = 0 ∧ t = 0 ∧ p ≠ 0 ∧ l = p * a) := by
  set Dt : ℝ := ((p * t - q * s : ℚ) : ℝ) + ((2 * q : ℚ) : ℝ) * l with hDt
  by_cases hD : Dt = 0
  · right
    obtain ⟨hq2, hpt⟩ := InQ.indep hirr (x := 2 * q) (y := p * t - q * s) (by rw [← hD]; ring)
    have hq : q = 0 := by
      have : (q : ℚ) = 0 := by linarith
      exact_mod_cast this
    subst hq
    simp only [Nat.cast_zero, zero_mul, add_zero, sub_zero] at hpt h1
    have hp : p ≠ 0 := by
      rintro rfl
      exact hirr ⟨r, by rw [h1]; simp⟩
    have ht : t = 0 := by
      have : (p : ℚ) * t = 0 := hpt
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (by exact_mod_cast h) hp
      · exact_mod_cast h
    subst ht
    simp only [Nat.cast_zero, zero_mul, add_zero] at h2
    have hpa : (p : ℝ) * a = l - r := by linarith
    have key : (((-(2 * r + s)) : ℚ) : ℝ) * l + ((2 * d + s * r - p * u : ℚ) : ℝ) = 0 := by
      have e : 2 * ((p : ℝ) * a) * l = s * ((p : ℝ) * a) + p * u := by
        linear_combination (p : ℝ) * h2
      rw [hpa] at e
      push_cast
      linear_combination e - 2 * hl
    obtain ⟨h3, -⟩ := InQ.indep hirr key
    have hrs : (2 * r + s : ℚ) = 0 := by linarith
    have hr : r = 0 := by
      have : (r : ℚ) = 0 := by
        have : (0 : ℚ) ≤ r := Nat.cast_nonneg r
        have : (0 : ℚ) ≤ s := Nat.cast_nonneg s
        linarith
      exact_mod_cast this
    have hs : s = 0 := by
      have : (s : ℚ) = 0 := by
        have : (0 : ℚ) ≤ r := Nat.cast_nonneg r
        have : (0 : ℚ) ≤ s := Nat.cast_nonneg s
        linarith
      exact_mod_cast this
    subst hr hs
    exact ⟨rfl, rfl, rfl, rfl, hp, by simpa using h1⟩
  · left
    have hDin : InQ l Dt := ⟨2 * q, p * t - q * s, by rw [hDt]; ring⟩
    have ea : a = (t * (l - r) + q * u) / Dt := by
      rw [eq_div_iff hD, hDt]; push_cast; linear_combination (-(t : ℝ)) * h1 + (q : ℝ) * h2
    have eb : b = (-(p * u) - (s - 2 * l) * (l - r)) / Dt := by
      rw [eq_div_iff hD, hDt]; push_cast
      linear_combination ((s : ℝ) - 2 * l) * h1 - (p : ℝ) * h2
    have hlr : InQ l (l - r) := InQ.self.sub (InQ.rat r)
    refine ⟨?_, ?_⟩
    · rw [ea]
      refine InQ.div hl hirr ?_ hDin hD
      have h := ((InQ.rat (t : ℚ)).mul hl hlr).add (InQ.rat (q * u : ℚ) (l := l))
      obtain ⟨x, y, hxy⟩ := h
      exact ⟨x, y, by rw [← hxy]; push_cast; ring⟩
    · rw [eb]
      refine InQ.div hl hirr ?_ hDin hD
      have h := (InQ.rat (-(p * u) : ℚ) (l := l)).sub
        (((InQ.rat (s : ℚ)).sub ((InQ.rat 2).mul hl InQ.self)).mul hl hlr)
      obtain ⟨x, y, hxy⟩ := h
      exact ⟨x, y, by rw [← hxy]; push_cast; ring⟩
open Classical in
theorem side_rel (i : Fin 3) : ∃ part : Finset (Fin N × Fin 3),
    (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) ∧
    ∃ P Q R : ℕ, dist (D.target.pts i) (D.target.pts (i + 1)) =
      P * dist (D.model.pts 1) (D.model.pts 2) + Q * dist (D.model.pts 2) (D.model.pts 0)
        + R * dist (D.model.pts 0) (D.model.pts 1) ∧
      (Q = 0 → R = 0 → ∀ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
        dist (D.model.pts 1) (D.model.pts 2)) := by
  obtain ⟨part, hcov, -, hsum⟩ := D.toDissection.side_walk i
  set a := dist (D.model.pts 1) (D.model.pts 2)
  set b := dist (D.model.pts 2) (D.model.pts 0)
  set c := dist (D.model.pts 0) (D.model.pts 1)
  set len := fun e : Fin N × Fin 3 => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
  set PA := part.filter fun e => len e = a
  set QB := part.filter fun e => len e ≠ a ∧ len e = b
  set RC := part.filter fun e => len e ≠ a ∧ len e ≠ b
  refine ⟨part, hcov, PA.card, QB.card, RC.card, ?_, ?_⟩
  · rw [← hsum]
    change ∑ e ∈ part, len e = _
    rw [← Finset.sum_filter_add_sum_filter_not part (fun e => len e = a)]
    rw [← Finset.sum_filter_add_sum_filter_not (part.filter fun e => ¬ len e = a)
      (fun e => len e = b), Finset.filter_filter, Finset.filter_filter]
    have h1 : ∑ e ∈ PA, len e = PA.card * a := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2), Finset.sum_const,
        nsmul_eq_mul]
    have h2 : ∑ e ∈ QB, len e = QB.card * b := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2.2), Finset.sum_const,
        nsmul_eq_mul]
    have h3 : ∑ e ∈ RC, len e = RC.card * c := by
      rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp he).2
      rcases edge_len_mem D e.1 e.2 with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact h
    rw [← h1, ← h2, ← h3]
    rw [add_assoc]
  · intro hQ hR e he
    by_contra hne
    rcases edge_len_mem D e.1 e.2 with h | h | h
    · exact hne h
    · have : e ∈ QB := Finset.mem_filter.mpr ⟨he, hne, h⟩
      rw [Finset.card_eq_zero.mp hQ] at this
      simp at this
    · by_cases hb : len e = b
      · have : e ∈ QB := Finset.mem_filter.mpr ⟨he, hne, hb⟩
        rw [Finset.card_eq_zero.mp hQ] at this
        simp at this
      · have : e ∈ RC := Finset.mem_filter.mpr ⟨he, hne, hb⟩
        rw [Finset.card_eq_zero.mp hR] at this
        simp at this


theorem a_edge_opp_alpha (hab : dist (D.model.pts 1) (D.model.pts 2) ≠
      dist (D.model.pts 2) (D.model.pts 0))
    (hac : dist (D.model.pts 1) (D.model.pts 2) ≠ dist (D.model.pts 0) (D.model.pts 1))
    (i : Fin N) (k : Fin 3)
    (hlen : dist ((D.tile i).pts k) ((D.tile i).pts (k + 1)) =
      dist (D.model.pts 1) (D.model.pts 2)) :
    (D.tile i).localAngle ((D.tile i).pts (k + 2)) = tileα D := by
  obtain ⟨σ, hang, hd⟩ := corner_perm_dist (D.tiles_congruent i)
  rw [Tri.localAngle_vertex, ← hang, model_corner]
  rw [hd] at hlen
  have h1 : σ (k + 2) ≠ σ k := σ.injective.ne (by fin_cases k <;> decide)
  have h2 : σ (k + 2) ≠ σ (k + 1) := σ.injective.ne (by fin_cases k <;> decide)
  have h3 : σ k ≠ σ (k + 1) := σ.injective.ne (by fin_cases k <;> decide)
  generalize σ (k + 2) = w at h1 h2 ⊢
  generalize σ (k + 1) = v at h2 h3 hlen
  generalize σ k = u at h1 h3 hlen
  fin_cases u <;> fin_cases v <;> fin_cases w <;> simp at h1 h2 h3 hlen ⊢ <;>
    first
    | exact absurd hlen.symm hac | exact absurd hlen hac
    | exact absurd hlen.symm hab | exact absurd hlen hab
    | (rw [dist_comm] at hlen; exact absurd hlen.symm hac)
    | (rw [dist_comm] at hlen; exact absurd hlen hac)
    | (rw [dist_comm] at hlen; exact absurd hlen.symm hab)
    | (rw [dist_comm] at hlen; exact absurd hlen hab)
theorem right_pyth (hright : tileγ D = Real.pi / 2) :
    dist (D.model.pts 0) (D.model.pts 1) ^ 2 =
      dist (D.model.pts 1) (D.model.pts 2) ^ 2 + dist (D.model.pts 2) (D.model.pts 0) ^ 2 := by
  have h1 : ∠ (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = Real.pi / 2 := hright
  have := law_cos (D.model.pts 0) (D.model.pts 2) (D.model.pts 1)
  rw [h1, Real.cos_pi_div_two, dist_comm (D.model.pts 0) (D.model.pts 2)] at this
  linear_combination this
open Classical in
theorem corner_B (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hαβ : tileα D ≠ tileβ D) {part0 part1 : Finset (Fin N × Fin 3)}
    (hcov0 : (⋃ e ∈ part0, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 0) (D.target.pts 1))
    (hcov1 : (⋃ e ∈ part1, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts 1) (D.target.pts 2))
    (ha0 : ∀ e ∈ part0, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      dist (D.model.pts 1) (D.model.pts 2))
    (ha1 : ∀ e ∈ part1, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      dist (D.model.pts 1) (D.model.pts 2)) :
    ∃ m : ℕ, 2 ≤ m ∧ 2 * tileα D = m * tileβ D := by
  have hsep := anglesSep_right' D hright hαβ
  have hβ := right_beta D hright
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  set B := D.target.pts 1
  have hab : dist (D.model.pts 1) (D.model.pts 2) ≠ dist (D.model.pts 2) (D.model.pts 0) :=
    fun h => hαβ (legs_eq_iff D hright h)
  have hpos : 0 < dist (D.model.pts 2) (D.model.pts 0) :=
    dist_pos.mpr fun e => by have := D.model.indep.injective e; exact absurd this (by decide)
  have hac : dist (D.model.pts 1) (D.model.pts 2) ≠ dist (D.model.pts 0) (D.model.pts 1) := by
    intro h
    have := right_pyth D hright
    rw [← h] at this
    nlinarith
  have hab' : dist (D.model.pts 1) (D.model.pts 2) = dist (D.model.pts 2) (D.model.pts 0) →
      tileα D = tileβ D := fun h => absurd h hab
  have hedge : ∀ (part : Finset (Fin N × Fin 3)) (P Q : Plane),
      (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ P Q → (B = P ∨ B = Q) →
      (∀ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
        dist (D.model.pts 1) (D.model.pts 2)) →
      ∃ e ∈ part, (D.tile e.1).edge e.2 ⊆ segment ℝ P Q ∧
        ((D.tile e.1).pts e.2 = B ∨ (D.tile e.1).pts (e.2 + 1) = B) ∧
        ((D.tile e.1).localAngle B = tileβ D ∨ (D.tile e.1).localAngle B = tileγ D) := by
    intro part P Q hcov hB hlen
    have hBs : B ∈ segment ℝ P Q := by
      rcases hB with h | h
      · rw [h]; exact left_mem_segment _ _ _
      · rw [h]; exact right_mem_segment _ _ _
    rw [← hcov] at hBs
    obtain ⟨e, he, hBe⟩ := Set.mem_iUnion₂.mp hBs
    have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ P Q := by
      rw [← hcov]; intro z hz; exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩
    have hu := hsub (left_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    have hv := hsub (right_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
    have hend : (D.tile e.1).pts e.2 = B ∨ (D.tile e.1).pts (e.2 + 1) = B := by
      rcases hB with h | h
      · rw [← h] at hu hv
        rcases eq_endpoint_of_mem_segment hu hv hBe with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      · rw [segment_symm] at hu hv
        rw [← h] at hu hv
        rcases eq_endpoint_of_mem_segment hu hv hBe with h' | h'
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
    refine ⟨e, he, hsub, hend, ?_⟩
    rcases hend with h | h
    · rw [← h]; exact a_edge_end_angles D hab' hac e.1 e.2 (hlen e he) e.2 (Or.inl rfl)
    · rw [← h]; exact a_edge_end_angles D hab' hac e.1 e.2 (hlen e he) (e.2 + 1) (Or.inr rfl)
  obtain ⟨e0, he0, hs0, hB0, hφ0⟩ := hedge part0 _ _ hcov0 (Or.inr rfl) ha0
  obtain ⟨e1, he1, hs1, hB1, hφ1⟩ := hedge part1 _ _ hcov1 (Or.inl rfl) ha1
  have hdiff : e0.1 ≠ e1.1 := by
    intro hsame
    have hα0' := a_edge_opp_alpha D hab hac e0.1 e0.2 (ha0 e0 he0)
    have hα1' := a_edge_opp_alpha D hab hac e1.1 e1.2 (ha1 e1 he1)
    rw [← hsame] at hα1'
    have hcnt := (tile_angle_count_sep D hsep e0.1).1
    simp only [← Tri.localAngle_vertex] at hcnt
    have hk : e0.2 + 2 = e1.2 + 2 :=
      Finset.card_le_one.mp hcnt.le _ (by simp [hα0']) _ (by simp [hα1'])
    have hk' : e0.2 = e1.2 := by simpa using hk
    have he : e0 = e1 := Prod.ext hsame hk'
    rw [← he] at hs1
    have m1 : ∀ x, x ∈ (D.tile e0.1).edge e0.2 → x = B := by
      intro x hx
      have h1 := hs1 hx
      have h0 := hs0 hx
      exact sides_meet D.target 1 h1 (by simpa using h0)
    exact tri_pts_succ_ne _ e0.2 ((m1 _ (left_mem_segment _ _ _)).trans
      (m1 _ (right_mem_segment _ _ _)).symm)
  have hloc : D.target.localAngle B = 2 * tileα D := by
    rw [Tri.localAngle_vertex]
    have hsum := cornerAngle_sum D.target
    have e1 : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileβ D := by
      rw [cornerAngle, angle_comm]; exact hC
    have e0 : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D := hA
    show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
    linarith
  obtain ⟨hv0, hinj⟩ := hsep
  have hf : ∀ i, (∃ j, (D.tile i).localAngle B =
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] j) ∨ (D.tile i).localAngle B = 0 := by
    intro i
    rcases localAngle_mem D B i with h | h | h | h | h | h
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inl ⟨3, h⟩
    · exact Or.inl ⟨4, h⟩
    · exact Or.inr h
  have hcount := sum_eq_counts (fun i => (D.tile i).localAngle B) _ hv0 hinj hf
  rw [D.toDissection.sum_localAngle_eq B, Fin.sum_univ_five, hloc] at hcount
  have hcount' : (angleCount D B (tileα D) : ℝ) * tileα D
      + (angleCount D B (tileβ D) : ℝ) * tileβ D + (angleCount D B (tileγ D) : ℝ) * tileγ D
      + (angleCount D B Real.pi : ℝ) * Real.pi
      + (angleCount D B (2 * Real.pi) : ℝ) * (2 * Real.pi) = 2 * tileα D := hcount.symm
  set nα := angleCount D B (tileα D)
  set nβ := angleCount D B (tileβ D)
  set nγ := angleCount D B (tileγ D)
  set nπ := angleCount D B Real.pi
  set n2 := angleCount D B (2 * Real.pi)
  rw [hright] at hcount'
  have key : ((nα + nγ + 2 * nπ + 4 * n2 : ℕ) : ℝ) * tileα D
      + ((nβ + nγ + 2 * nπ + 4 * n2 : ℕ) : ℝ) * tileβ D = 2 * tileα D := by
    push_cast
    have hpi : Real.pi = 2 * tileα D + 2 * tileβ D := by linarith
    rw [hpi] at hcount'
    linarith
  have hB1 : 1 ≤ nβ + nγ := by
    rcases hφ0 with h | h
    · have := angleCount_pos D h; omega
    · have := angleCount_pos D h; omega
  have hlt : nα + nγ + 2 * nπ + 4 * n2 < 2 := by
    by_contra h
    push Not at h
    have h1 : (2 : ℝ) ≤ ((nα + nγ + 2 * nπ + 4 * n2 : ℕ) : ℝ) := by exact_mod_cast h
    have h2 : (1 : ℝ) ≤ ((nβ + nγ + 2 * nπ + 4 * n2 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    nlinarith
  rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
  · 
    have hz : nα = 0 ∧ nγ = 0 ∧ nπ = 0 ∧ n2 = 0 := by omega
    obtain ⟨h1, h2, h3, h4⟩ := hz
    have hb0 : (D.tile e0.1).localAngle B = tileβ D := by
      rcases hφ0 with h | h
      · exact h
      · have := angleCount_pos D h; omega
    have hb1 : (D.tile e1.1).localAngle B = tileβ D := by
      rcases hφ1 with h | h
      · exact h
      · have := angleCount_pos D h; omega
    have h2le : 2 ≤ nβ := by
      have : ({e0.1, e1.1} : Finset (Fin N)) ⊆
          Finset.univ.filter fun i => (D.tile i).localAngle B = tileβ D := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [hb0, hb1]
      have := Finset.card_le_card this
      rw [Finset.card_pair hdiff] at this
      exact this
    refine ⟨nβ, h2le, ?_⟩
    rw [h1, h2, h3, h4] at key
    push_cast at key
    linarith
  · 
    have hz : nπ = 0 ∧ n2 = 0 ∧ nα + nγ = 1 := by omega
    refine ⟨2 * (nβ + nγ), by omega, ?_⟩
    obtain ⟨h3, h4, h5⟩ := hz
    have : ((nα + nγ + 2 * nπ + 4 * n2 : ℕ) : ℝ) = 1 := by rw [h3, h4]; exact_mod_cast h5
    rw [this, h3, h4] at key
    push_cast at key ⊢
    linarith
theorem sqrt5_of_cos {l : ℝ} {N P : ℕ} (hP : (P : ℝ) ≠ 0) (hl : l ^ 2 = (N : ℝ) / 2)
    (h : (1 + Real.sqrt 5) / 4 = l / P) : Real.sqrt 5 = ((4 * N / P ^ 2 - 3 : ℚ) : ℝ) := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h2 : ((1 + Real.sqrt 5) / 4) ^ 2 = l ^ 2 / (P : ℝ) ^ 2 := by rw [h, div_pow]
  rw [hl] at h2
  have h3 : (1 + Real.sqrt 5) ^ 2 = 8 * N / (P : ℝ) ^ 2 := by
    field_simp at h2 ⊢; linarith
  have h4 : (1 + Real.sqrt 5) ^ 2 = 6 + 2 * Real.sqrt 5 := by
    have : (1 + Real.sqrt 5) ^ 2 = 1 + 2 * Real.sqrt 5 + Real.sqrt 5 ^ 2 := by ring
    rw [this, hsq]; ring
  push_cast
  have h5 : 4 * (N : ℝ) / (P : ℝ) ^ 2 = (8 * N / (P : ℝ) ^ 2) / 2 := by ring
  rw [h5, ← h3, h4]
  ring
theorem isosceleshelper2 (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hβ6 : tileβ D ≠ Real.pi / 6) (hirrl : ¬ ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q) :
    InQ (Real.sqrt ((N : ℝ) / 2))
        (dist (D.model.pts 1) (D.model.pts 2) / dist (D.model.pts 0) (D.model.pts 1)) ∧
      InQ (Real.sqrt ((N : ℝ) / 2))
        (dist (D.model.pts 2) (D.model.pts 0) / dist (D.model.pts 0) (D.model.pts 1)) := by
  set a := dist (D.model.pts 1) (D.model.pts 2) with hadef
  set b := dist (D.model.pts 2) (D.model.pts 0) with hbdef
  set c := dist (D.model.pts 0) (D.model.pts 1) with hcdef
  set l := Real.sqrt ((N : ℝ) / 2) with hldef
  have hl : l ^ 2 = (((N : ℚ) / 2 : ℚ) : ℝ) := by
    rw [hldef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hc0 : 0 < c := dist_pos.mpr fun e => by
    have := D.model.indep.injective e; exact absurd this (by decide)
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  obtain ⟨hXX, hcY, hN⟩ := right_area_core D rfl rfl rfl rfl rfl hright hA hC
  set X := dist (D.target.pts 0) (D.target.pts 1)
  set Y := dist (D.target.pts 2) (D.target.pts 0)
  have hXl : X = l * c := by
    have h1 : X ^ 2 = (l * c) ^ 2 := by
      rw [mul_pow, hl]; push_cast; linarith
    exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp h1
  have hYl : Y = 2 * a * l := by
    have : c * Y = c * (2 * a * l) := by rw [hcY, hXl]; ring
    exact mul_left_cancel₀ hc0.ne' this
  obtain ⟨part0, hcov0, P0, Q0, R0, hs0, hall0⟩ := side_rel D 0
  obtain ⟨part1, hcov1, P1, Q1, R1, hs1, hall1⟩ := side_rel D 1
  obtain ⟨part2, -, P2, Q2, R2, hs2, -⟩ := side_rel D 2
  have i01 : (0 : Fin 3) + 1 = 1 := rfl
  have i12 : (1 : Fin 3) + 1 = 2 := rfl
  have i20 : (2 : Fin 3) + 1 = 0 := rfl
  rw [i01] at hcov0 hs0
  rw [i12] at hcov1 hs1
  rw [i20] at hs2
  have e0 : l = P0 * (a / c) + Q0 * (b / c) + R0 := by
    field_simp; rw [← hXl]; linarith
  have e1 : l = P1 * (a / c) + Q1 * (b / c) + R1 := by
    field_simp; rw [← hXl, ← hXX]; linarith
  have e2 : 2 * (a / c) * l = P2 * (a / c) + Q2 * (b / c) + R2 := by
    field_simp; rw [← hs2.symm.trans hYl]; ring
  rcases cramer hl hirrl e0 e2 with h | ⟨hQ0, hR0, -, -, hP0, hlP⟩
  · exact h
  rcases cramer hl hirrl e1 e2 with h | ⟨hQ1, hR1, -, -, -, -⟩
  · exact h
  have hla : a / c = l / P0 := by
    have hP0' : (P0 : ℝ) ≠ 0 := by exact_mod_cast hP0
    rw [hlP, mul_div_cancel_left₀ _ hP0']
  have hina : InQ l (a / c) := ⟨1 / P0, 0, by rw [hla]; push_cast; ring⟩
  obtain ⟨hab, hbc⟩ := right_trig D hright
  change a = Real.cos (tileβ D) * c at hab
  change b = Real.cos (tileα D) * c at hbc
  by_cases hαβ : tileα D = tileβ D
  · 
    refine ⟨hina, ?_⟩
    have : b = a := by rw [hab, hbc, hαβ]
    rw [this]; exact hina
  exfalso
  obtain ⟨m, hm2, hmα⟩ := corner_B D hright hA hC hαβ hcov0 hcov1 (hall0 hQ0 hR0) (hall1 hQ1 hR1)
  have hβ := right_beta D hright
  have hβm : tileβ D = 2 * Real.pi * (1 : ℕ) / ((2 * m + 4 : ℕ) : ℝ) := by
    push_cast
    field_simp
    linarith
  have hcos : Real.cos (tileβ D) = a / c := by
    rw [hab]; field_simp
  obtain ⟨P, hP, hPdeg, hProot⟩ := hina.quadratic hl
  rw [← hcos, hβm] at hProot
  have hn := euler (by omega) (Nat.coprime_one_left _) hP hPdeg hProot
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  have hm : m = 2 ∨ m = 3 ∨ m = 4 := by omega
  rcases hm with rfl | rfl | rfl
  · 
    apply hαβ; push_cast at hmα; linarith
  · 
    have hβ5 : tileβ D = Real.pi / 5 := by rw [hβm]; push_cast; ring
    rw [hβ5, Real.cos_pi_div_five, hla] at hcos
    have hP0' : (P0 : ℝ) ≠ 0 := by exact_mod_cast hP0
    have hl' : l ^ 2 = (N : ℝ) / 2 := by rw [hl]; push_cast; ring
    have h5 := sqrt5_of_cos hP0' hl' hcos
    have hirr5 := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
    push_cast at hirr5
    exact hirr5 ⟨_, h5.symm⟩
  · 
    apply hβ6; rw [hβm]; push_cast; ring
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry Polynomial
variable {N : ℕ} (D : CongruentDissection N)
theorem right_sin (hright : tileγ D = Real.pi / 2) :
    dist (D.model.pts 2) (D.model.pts 0) =
      Real.sin (tileβ D) * dist (D.model.pts 0) (D.model.pts 1) := by
  rw [(right_trig D hright).2, ← Real.cos_pi_div_two_sub, right_beta D hright]
  ring_nf
theorem beta_irrational_of_quadratic (hright : tileγ D = Real.pi / 2) {l : ℝ} {d : ℚ}
    (hl : l ^ 2 = d) (hcos : InQ l (Real.cos (tileβ D))) (hsin : InQ l (Real.sin (tileβ D)))
    (hβ6 : tileβ D ≠ Real.pi / 6) (hβ4 : tileβ D ≠ Real.pi / 4)
    (hβ3 : tileβ D ≠ Real.pi / 3) : ¬ ∃ r : ℚ, tileβ D = r * Real.pi := by
  rintro ⟨r, hr⟩
  have hβ0 := tileβ_pos D
  have hβ := right_beta D hright
  have hα0 := tileα_pos D
  have hpi := Real.pi_pos
  set t : ℚ := r / 2
  have ht0 : 0 < t := by
    have : (0 : ℝ) < r := by
      by_contra h; push Not at h; nlinarith
    have : (0 : ℚ) < r := by exact_mod_cast this
    simp only [t]; linarith
  have hnum : 0 < t.num := Rat.num_pos.mpr ht0
  set m := t.num.natAbs
  have hm : ((m : ℕ) : ℝ) = (t.num : ℝ) := by
    simp only [m]; rw [Nat.cast_natAbs]; push_cast; rw [abs_of_pos (by exact_mod_cast hnum)]
  have hβmn : tileβ D = 2 * Real.pi * m / t.den := by
    rw [hr, hm]
    have : (r : ℝ) = 2 * ((t.num : ℝ) / t.den) := by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
      simp only [t]; push_cast; ring
    rw [this]; ring
  have hcop : m.Coprime t.den := t.reduced
  obtain ⟨P, hP, hPd, hPr⟩ := hcos.quadratic hl
  obtain ⟨R, hR, hRd, hRr⟩ := hsin.quadratic hl
  rw [hβmn] at hPr hRr
  have hn := euler_sin t.den_pos hcop hP hPd hPr hR hRd hRr
  have hm1 : 1 ≤ m := by simp only [m]; omega
  have hlt : 4 * m < t.den := by
    have h1 : tileβ D < Real.pi / 2 := by linarith
    rw [hβmn] at h1
    have hn0 : (0 : ℝ) < t.den := by exact_mod_cast t.den_pos
    have : (4 * m : ℝ) < t.den := by
      rw [div_lt_iff₀ hn0] at h1; nlinarith
    exact_mod_cast this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h | h <;> rw [h] at hlt hβmn hcop
  · omega
  · omega
  · omega
  · omega
  · have hm' : m = 1 := by omega
    rw [hm'] at hβmn
    exact hβ3 (by rw [hβmn]; push_cast; ring)
  · have hm' : m = 1 := by omega
    rw [hm'] at hβmn
    exact hβ4 (by rw [hβmn]; push_cast; ring)
  · have hm' : m = 1 ∨ m = 2 := by omega
    rcases hm' with hm' | hm'
    · rw [hm'] at hβmn; exact hβ6 (by rw [hβmn]; push_cast; ring)
    · rw [hm'] at hcop; exact absurd hcop (by decide)
theorem side_edge_at_end {part : Finset (Fin N × Fin 3)} {P Q V : Plane}
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ P Q) (hV : V = P ∨ V = Q) :
    ∃ e ∈ part, ((D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) := by
  have hVs : V ∈ segment ℝ P Q := by
    rcases hV with h | h
    · rw [h]; exact left_mem_segment _ _ _
    · rw [h]; exact right_mem_segment _ _ _
  rw [← hcov] at hVs
  obtain ⟨e, he, hVe⟩ := Set.mem_iUnion₂.mp hVs
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ P Q := by
    rw [← hcov]; intro z hz; exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩
  have hu := hsub (left_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
  have hv := hsub (right_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
  refine ⟨e, he, ?_⟩
  rcases hV with h | h
  · rw [← h] at hu hv
    rcases eq_endpoint_of_mem_segment hu hv hVe with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm
  · rw [segment_symm] at hu hv
    rw [← h] at hu hv
    rcases eq_endpoint_of_mem_segment hu hv hVe with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm
theorem edge_type_ne (hsep : AnglesSep D) {e : Fin N × Fin 3} {V : Plane}
    (hV : (D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) {φ : ℝ}
    (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) (hang : (D.tile e.1).localAngle V = φ) :
    ¬ edgeType D φ e := by
  intro hθ
  have hcnt := tile_angle_count_sep D hsep e.1
  simp only [← Tri.localAngle_vertex] at hcnt
  have h1 : (Finset.univ.filter fun k : Fin 3 =>
      (D.tile e.1).localAngle ((D.tile e.1).pts k) = φ).card = 1 := by
    rcases hφ with rfl | rfl | rfl
    · exact hcnt.1
    · exact hcnt.2.1
    · exact hcnt.2.2
  have n1 : ∀ k : Fin 3, k ≠ k + 2 := by decide
  have n2 : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide
  rcases hV with h | h
  · exact n1 e.2 (Finset.card_le_one.mp h1.le e.2 (by simp [h, hang]) (e.2 + 2)
      (by simpa [edgeType] using hθ))
  · exact n2 e.2 (Finset.card_le_one.mp h1.le (e.2 + 1) (by simp [h, hang]) (e.2 + 2)
      (by simpa [edgeType] using hθ))
theorem apex_angle (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) :
    D.target.localAngle (D.target.pts 1) = 2 * tileα D := by
  have hβ := right_beta D hright
  rw [Tri.localAngle_vertex]
  have hsum := cornerAngle_sum D.target
  have e1 : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileβ D := by
    rw [cornerAngle, angle_comm]; exact hC
  have e0 : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D := hA
  show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
  linarith
open Classical in
theorem typed_side (hsep : AnglesSep D) (i : Fin 3) : ∃ part : Finset (Fin N × Fin 3),
    (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) ∧
    dist (D.target.pts i) (D.target.pts (i + 1)) =
      ((part.filter (edgeType D (tileα D))).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      + ((part.filter (edgeType D (tileβ D))).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      + ((part.filter (edgeType D (tileγ D))).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨part, hcov, -, hsum⟩ := D.toDissection.side_walk i
  exact ⟨part, hcov, side_walk_counts_sep D hsep part _ hsum⟩
theorem angle_at_end {e : Fin N × Fin 3} {V : Plane}
    (hV : (D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) :
    (D.tile e.1).localAngle V = tileα D ∨ (D.tile e.1).localAngle V = tileβ D ∨
      (D.tile e.1).localAngle V = tileγ D := by
  rcases hV with h | h
  · rw [← h]; exact localAngle_at_own_vertex_mem' D e.1 e.2
  · rw [← h]; exact localAngle_at_own_vertex_mem' D e.1 (e.2 + 1)
theorem helper3_signs {l x y z w p q r : ℝ} (hl0 : 0 < l) (ha : 0 < x * l + y) (hb : 0 < z * l + w)
    (hxyzw : x * y + z * w = 0) (hxy : x * y ≠ 0) (hlin : p * y + q * w + r = 0)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : 1 ≤ q ∨ 1 ≤ r) : 0 < x ∧ 0 < z := by
  rcases lt_or_gt_of_ne hxy with hneg | hpos
  · have hzw : 0 < z * w := by linarith
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hzw with ⟨hz, hw⟩ | ⟨hz, hw⟩
    · have hqw : 0 < q * w + r := by
        rcases hqr with h | h
        · have : 0 < q * w := mul_pos (by linarith) hw
          linarith
        · have : 0 ≤ q * w := mul_nonneg hq hw.le
          linarith
      have hy : y < 0 := by
        by_contra h
        push Not at h
        have : 0 ≤ p * y := mul_nonneg hp h
        linarith
      refine ⟨?_, hz⟩
      by_contra hx
      push Not at hx
      have : 0 ≤ x * y := mul_nonneg_of_nonpos_of_nonpos hx hy.le
      linarith
    · exfalso
      have : z * l < 0 := mul_neg_of_neg_of_pos hz hl0
      linarith
  · rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hw : w < 0 := by
        by_contra h
        push Not at h
        have hpy : 0 ≤ p * y := mul_nonneg hp hy.le
        have hqw : 0 ≤ q * w := mul_nonneg hq h
        have hw0 : w ≠ 0 := by
          rintro rfl
          exact hxy (by linarith)
        have hw' : 0 < w := lt_of_le_of_ne h (Ne.symm hw0)
        rcases hqr with h' | h'
        · have : 0 < q * w := mul_pos (by linarith) hw'
          linarith
        · linarith
      refine ⟨hx, ?_⟩
      by_contra hz
      push Not at hz
      have : 0 ≤ z * w := mul_nonneg_of_nonpos_of_nonpos hz hw.le
      have : 0 < x * y := mul_pos hx hy
      linarith
    · exfalso
      have : x * l < 0 := mul_neg_of_neg_of_pos hx hl0
      linarith
theorem helper3_algebra {l : ℝ} {d : ℚ} (hl : l ^ 2 = d) (hirr : ¬ ∃ q : ℚ, l = q) (hl0 : 0 < l)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1)
    (hina : InQ l a) (hinb : InQ l b) {p q r s t u : ℕ}
    (h1 : l = p * a + q * b + r) (h2 : 2 * a * l = s * a + t * b + u)
    (hqr : 1 ≤ q + r) (hsu : 1 ≤ s + u)
    (hallc : (∀ j v v' : ℕ, 0 < j → (j : ℝ) ≠ v * a + v' * b) → r = 0 ∧ s = 0 ∧ t = 0) :
    ∃ x z : ℚ, a = x * l ∧ b = z * l := by
  obtain ⟨x, y, rfl⟩ := hina
  obtain ⟨z, w, rfl⟩ := hinb
  have hd : (0 : ℝ) < d := by rw [← hl]; positivity
  obtain ⟨-, hlin⟩ := InQ.indep hirr (x := p * x + q * z - 1) (y := p * y + q * w + r)
    (by push_cast; linear_combination -h1)
  obtain ⟨hpyth, -⟩ := InQ.indep hirr (x := 2 * (x * y + z * w))
    (y := (x ^ 2 + z ^ 2) * d + y ^ 2 + w ^ 2 - 1)
    (by push_cast; linear_combination hab - ((x : ℝ) ^ 2 + (z : ℝ) ^ 2) * hl)
  have hxyzw : x * y + z * w = 0 := by linarith
  have hlinR : (p : ℝ) * y + q * w + r = 0 := by exact_mod_cast hlin
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  by_cases hxy : x * y = 0
  · 
    have hzw : z * w = 0 := by linarith
    rcases mul_eq_zero.mp hxy with hx | hy
    · exfalso
      subst hx
      simp only [Rat.cast_zero, zero_mul, zero_add] at ha h1 h2
      rcases mul_eq_zero.mp hzw with hz | hw
      · subst hz
        simp only [Rat.cast_zero, zero_mul, zero_add] at hb
        have : (q : ℝ) * w = 0 ∧ (r : ℝ) = 0 := by
          constructor <;> nlinarith [mul_nonneg hp0 ha.le, mul_nonneg hq0 hb.le]
        have hq : q = 0 := by
          have := this.1
          rcases mul_eq_zero.mp this with h | h
          · exact_mod_cast h
          · exact absurd h hb.ne'
        have hr : r = 0 := by exact_mod_cast this.2
        omega
      · subst hw
        obtain ⟨-, h3⟩ := InQ.indep hirr (x := 2 * y - t * z) (y := -(s * y + u))
          (by push_cast; linear_combination h2)
        have hs : (s : ℝ) * y + u = 0 := by
          have : (s : ℚ) * y + u = 0 := by linarith
          exact_mod_cast this
        have h4 : (s : ℝ) = 0 ∧ (u : ℝ) = 0 := by
          constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) ha.le,
            (Nat.cast_nonneg u : (0 : ℝ) ≤ u)]
        have hs0 : s = 0 := by exact_mod_cast h4.1
        have hu0 : u = 0 := by exact_mod_cast h4.2
        omega
    · subst hy
      simp only [Rat.cast_zero] at hlinR
      have hw : w = 0 := by
        rcases mul_eq_zero.mp hzw with hz | hw
        · exfalso
          subst hz
          simp only [Rat.cast_zero, zero_mul, zero_add] at hb hlinR
          have : (q : ℝ) * w = 0 ∧ (r : ℝ) = 0 := by
            constructor <;> nlinarith [mul_nonneg hq0 hb.le]
          have hq : q = 0 := by
            rcases mul_eq_zero.mp this.1 with h | h
            · exact_mod_cast h
            · exact absurd h hb.ne'
          have hr : r = 0 := by exact_mod_cast this.2
          omega
        · exact hw
      subst hw
      exact ⟨x, z, by push_cast; ring, by push_cast; ring⟩
  · 
    have hxz : 0 < x ∧ 0 < z := by
      have hxyR : (x : ℝ) * y ≠ 0 := by exact_mod_cast hxy
      have hxyzwR : (x : ℝ) * y + z * w = 0 := by exact_mod_cast hxyzw
      have hqr' : 1 ≤ (q : ℝ) ∨ 1 ≤ (r : ℝ) := by
        rcases Nat.eq_zero_or_pos q with hq | hq
        · right; exact_mod_cast (show 1 ≤ r by omega)
        · left; exact_mod_cast hq
      have := helper3_signs hl0 ha hb hxyzwR hxyR hlinR hp0 hq0 hr0 hqr'
      exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
    obtain ⟨hx, hz⟩ := hxz
    have hnorel : ∀ j v v' : ℕ, 0 < j →
        (j : ℝ) ≠ v * ((x : ℝ) * l + y) + v' * ((z : ℝ) * l + w) := by
      intro j v v' hj he
      obtain ⟨h3, h4⟩ := InQ.indep hirr (x := v * x + v' * z) (y := v * y + v' * w - j)
        (by push_cast; linear_combination -he)
      have hv : v = 0 := by
        by_contra hv
        have : (0 : ℚ) < v * x := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hv) hx
        have : (0 : ℚ) ≤ v' * z := mul_nonneg (Nat.cast_nonneg _) hz.le
        linarith
      have hv' : v' = 0 := by
        by_contra hv'
        have : (0 : ℚ) < v' * z := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hv') hz
        have : (0 : ℚ) ≤ v * x := mul_nonneg (Nat.cast_nonneg _) hx.le
        linarith
      subst hv hv'
      simp at h4
      omega
    obtain ⟨hr, hs, ht⟩ := hallc hnorel
    subst hr hs ht
    simp only [Nat.cast_zero, zero_mul, zero_add, add_zero] at h1 h2
    have hq1 : 1 ≤ q := by omega
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hdR : (d : ℝ) ≠ 0 := hd.ne'
    have hl' : l ≠ 0 := hl0.ne'
    have ea : (x : ℝ) * l + y = (u : ℝ) / (2 * d) * l := by
      rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
      linear_combination (-2 * ((x : ℝ) * l + y)) * hl + l * h2
    have eb : (z : ℝ) * l + w = (1 - p * ((u : ℝ) / (2 * d))) / q * l := by
      rw [div_mul_eq_mul_div, eq_div_iff hqR]
      linear_combination -h1 - (p : ℝ) * ea
    exact ⟨u / (2 * d), (1 - p * (u / (2 * d))) / q, by push_cast; exact ea,
      by push_cast; exact eb⟩
open Classical in
theorem isosceleshelper3 (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hβ6 : tileβ D ≠ Real.pi / 6) (hβ4 : tileβ D ≠ Real.pi / 4) (hβ3 : tileβ D ≠ Real.pi / 3)
    (hirrl : ¬ ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q) :
    (∃ x z : ℚ,
      dist (D.model.pts 1) (D.model.pts 2) / dist (D.model.pts 0) (D.model.pts 1) =
        x * Real.sqrt ((N : ℝ) / 2) ∧
      dist (D.model.pts 2) (D.model.pts 0) / dist (D.model.pts 0) (D.model.pts 1) =
        z * Real.sqrt ((N : ℝ) / 2)) ∧
    (∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
        edgeType D (tileγ D) e) ∧
      ∀ e : Fin N × Fin 3,
        ((D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) ∨
          (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2)) →
        ¬ edgeType D (tileγ D) e := by
  obtain ⟨hina, hinb⟩ := isosceleshelper2 D hright hA hC hβ6 hirrl
  set a := dist (D.model.pts 1) (D.model.pts 2) with hadef
  set b := dist (D.model.pts 2) (D.model.pts 0) with hbdef
  set c := dist (D.model.pts 0) (D.model.pts 1) with hcdef
  set l := Real.sqrt ((N : ℝ) / 2) with hldef
  set T := D.target.pts with hT
  have hl : l ^ 2 = (((N : ℚ) / 2 : ℚ) : ℝ) := by
    rw [hldef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hc0 : 0 < c := dist_pos.mpr fun e => by
    have := D.model.indep.injective e; exact absurd this (by decide)
  have ha0 : 0 < a := dist_pos.mpr fun e => by
    have := D.model.indep.injective e; exact absurd this (by decide)
  have hb0 : 0 < b := dist_pos.mpr fun e => by
    have := D.model.indep.injective e; exact absurd this (by decide)
  have hl0 : 0 < l := by
    rcases (Real.sqrt_nonneg ((N : ℝ) / 2)).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨0, by rw [hldef, ← h]; simp⟩ hirrl
  have hβ := right_beta D hright
  obtain ⟨hab, -⟩ := right_trig D hright
  change a = Real.cos (tileβ D) * c at hab
  have hbs : b = Real.sin (tileβ D) * c := right_sin D hright
  have hcos : Real.cos (tileβ D) = a / c := by rw [hab]; field_simp
  have hsin : Real.sin (tileβ D) = b / c := by rw [hbs]; field_simp
  have hβirr := beta_irrational_of_quadratic D hright hl (hcos ▸ hina) (hsin ▸ hinb) hβ6 hβ4 hβ3
  have hαirr : ¬ ∃ r : ℚ, tileα D = r * Real.pi := by
    rintro ⟨r, hr⟩
    exact hβirr ⟨1 / 2 - r, by rw [hβ, hr]; push_cast; ring⟩
  have hsep := anglesSep_right D hright hαirr
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  have hαγ : tileα D ≠ tileγ D := by rw [hright]; linarith
  have hβγ : tileβ D ≠ tileγ D := by rw [hright]; linarith
  obtain ⟨-, hcY, hN⟩ := right_area_core D rfl rfl rfl rfl rfl hright hA hC
  set X := dist (T 0) (T 1)
  set Y := dist (T 2) (T 0)
  have hXl : X = l * c := by
    have h1 : X ^ 2 = (l * c) ^ 2 := by
      rw [mul_pow, hl]; push_cast; linarith
    exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp h1
  have hYl : Y = 2 * a * l := by
    have : c * Y = c * (2 * a * l) := by rw [hcY, hXl]; ring
    exact mul_left_cancel₀ hc0.ne' this
  obtain ⟨part0, hcov0, hs0⟩ := typed_side D hsep 0
  obtain ⟨part2, hcov2, hs2⟩ := typed_side D hsep 2
  have i01 : (0 : Fin 3) + 1 = 1 := rfl
  have i20 : (2 : Fin 3) + 1 = 0 := rfl
  rw [i01] at hcov0 hs0
  rw [i20] at hcov2 hs2
  have e1 : l = ((part0.filter (edgeType D (tileα D))).card : ℝ) * (a / c)
      + ((part0.filter (edgeType D (tileβ D))).card : ℝ) * (b / c)
      + ((part0.filter (edgeType D (tileγ D))).card : ℝ) := by
    field_simp; rw [← hXl]; linarith
  have e2 : 2 * (a / c) * l = ((part2.filter (edgeType D (tileα D))).card : ℝ) * (a / c)
      + ((part2.filter (edgeType D (tileβ D))).card : ℝ) * (b / c)
      + ((part2.filter (edgeType D (tileγ D))).card : ℝ) := by
    field_simp; rw [← hs2.symm.trans hYl]; ring
  have hsub0 : ∀ e ∈ part0, (D.tile e.1).edge e.2 ⊆ segment ℝ (T 0) (T 1) := by
    intro e he y hy; rw [← hcov0]; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  have hsub2 : ∀ e ∈ part2, (D.tile e.1).edge e.2 ⊆ segment ℝ (T 2) (T 0) := by
    intro e he y hy; rw [← hcov2]; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  have htype : ∀ e : Fin N × Fin 3, edgeType D (tileα D) e ∨ edgeType D (tileβ D) e ∨
      edgeType D (tileγ D) e := fun e => localAngle_at_own_vertex_mem' D e.1 (e.2 + 2)
  have hzero : ∀ (part : Finset (Fin N × Fin 3)) (φ : ℝ), φ ≠ tileγ D →
      (∀ e ∈ part, edgeType D (tileγ D) e) → (part.filter (edgeType D φ)).card = 0 := by
    intro part φ hφ hall
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hφe
    exact hφ (hφe.symm.trans (hall e he))
  have hpos : ∀ (part : Finset (Fin N × Fin 3)) (φ : ℝ) (e : Fin N × Fin 3), e ∈ part →
      edgeType D φ e → 1 ≤ (part.filter (edgeType D φ)).card := fun part φ e he h =>
    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩
  have hqr : 1 ≤ (part0.filter (edgeType D (tileβ D))).card +
      (part0.filter (edgeType D (tileγ D))).card := by
    obtain ⟨e, he, hV⟩ := side_edge_at_end D hcov0 (V := T 1) (Or.inr rfl)
    have hB := vertex_relations_right D hright hαirr (T 1) 2 0
      (by rw [apex_angle D hright hA hC]; push_cast; ring)
    have hnβ : angleCount D (T 1) (tileβ D) = 0 := by omega
    have hnγ : angleCount D (T 1) (tileγ D) = 0 := by omega
    have hang : (D.tile e.1).localAngle (T 1) = tileα D := by
      rcases angle_at_end D hV with h | h | h
      · exact h
      · exfalso
        have : 0 < angleCount D (T 1) (tileβ D) :=
          Finset.card_pos.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        omega
      · exfalso
        have : 0 < angleCount D (T 1) (tileγ D) :=
          Finset.card_pos.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        omega
    have hnot := edge_type_ne D hsep hV (Or.inl rfl) hang
    rcases htype e with h | h | h
    · exact absurd h hnot
    · have := hpos _ _ e he h; omega
    · have := hpos _ _ e he h; omega
  have hsu : 1 ≤ (part2.filter (edgeType D (tileα D))).card +
      (part2.filter (edgeType D (tileγ D))).card := by
    obtain ⟨e, he, hV⟩ := side_edge_at_end D hcov2 (V := T 0) (Or.inr rfl)
    have hA' := vertex_relations_right D hright hαirr (T 0) (-1) 1
      (by rw [Tri.localAngle_vertex]; change ∠ (T 1) (T 0) (T 2) = _; rw [hA, hβ]; push_cast; ring)
    have hnα : angleCount D (T 0) (tileα D) = 0 := by omega
    have hnγ : angleCount D (T 0) (tileγ D) = 0 := by omega
    have hang : (D.tile e.1).localAngle (T 0) = tileβ D := by
      rcases angle_at_end D hV with h | h | h
      · exfalso
        have : 0 < angleCount D (T 0) (tileα D) :=
          Finset.card_pos.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        omega
      · exact h
      · exfalso
        have : 0 < angleCount D (T 0) (tileγ D) :=
          Finset.card_pos.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        omega
    have hnot := edge_type_ne D hsep hV (Or.inr (Or.inl rfl)) hang
    rcases htype e with h | h | h
    · have := hpos _ _ e he h; omega
    · exact absurd h hnot
    · have := hpos _ _ e he h; omega
  have halt1 : (∀ j v v' : ℕ, 0 < j → (j : ℝ) ≠ v * (a / c) + v' * (b / c)) →
      (∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (T 2) (T 0) →
        edgeType D (tileγ D) e) ∧
      ∀ e : Fin N × Fin 3,
        ((D.tile e.1).edge e.2 ⊆ segment ℝ (T 0) (T 1) ∨
          (D.tile e.1).edge e.2 ⊆ segment ℝ (T 1) (T 2)) →
        ¬ edgeType D (tileγ D) e := by
    intro hno
    have hnorel : ¬ ∃ j u v : ℕ, 0 < j ∧ (j : ℝ) * c = u * a + v * b := by
      rintro ⟨j, u, v, hj, he⟩
      apply hno j u v hj
      rw [mul_div_assoc', mul_div_assoc', ← add_div, eq_div_iff hc0.ne']
      exact he
    rcases allc D hright hαirr hA hC hnorel with h | ⟨h0, -⟩
    · exact h
    · exfalso
      have hall : ∀ e ∈ part0, edgeType D (tileγ D) e := fun e he => h0 e (Or.inl (hsub0 e he))
      rw [hzero part0 _ hαγ hall, hzero part0 _ hβγ hall] at e1
      simp only [Nat.cast_zero, zero_mul, zero_add] at e1
      exact hirrl ⟨_, by rw [e1]; rfl⟩
  obtain ⟨x, z, hx, hz⟩ := helper3_algebra hl hirrl hl0 (div_pos ha0 hc0) (div_pos hb0 hc0)
    (by rw [← hcos, ← hsin]; exact Real.cos_sq_add_sin_sq _) hina hinb e1 e2 hqr hsu
    (fun hno => by
      obtain ⟨h1, h2⟩ := halt1 hno
      have hall2 : ∀ e ∈ part2, edgeType D (tileγ D) e := fun e he => h1 e (hsub2 e he)
      refine ⟨?_, hzero part2 _ hαγ hall2, hzero part2 _ hβγ hall2⟩
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun e he => h2 e (Or.inl (hsub0 e he)))
  refine ⟨⟨x, z, hx, hz⟩, halt1 ?_⟩
  intro j v v' hj he
  rw [hx, hz] at he
  have hx0 : 0 < x := by
    have : (0 : ℝ) < x * l := hx ▸ div_pos ha0 hc0
    exact_mod_cast pos_of_mul_pos_left this hl0.le
  have hz0 : 0 < z := by
    have : (0 : ℝ) < z * l := hz ▸ div_pos hb0 hc0
    exact_mod_cast pos_of_mul_pos_left this hl0.le
  have hS : (0 : ℚ) ≤ v * x + v' * z := by positivity
  have hS0 : (v * x + v' * z : ℚ) ≠ 0 := by
    intro h0
    have : ((v * x + v' * z : ℚ) : ℝ) = 0 := by exact_mod_cast h0
    have hj' : (j : ℝ) = 0 := by rw [he]; push_cast at this; linear_combination l * this
    exact absurd hj' (by exact_mod_cast hj.ne')
  apply hirrl
  refine ⟨j / (v * x + v' * z), ?_⟩
  have hS0' : ((v * x + v' * z : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hS0
  push_cast at hS0' ⊢
  rw [eq_div_iff hS0']
  linear_combination -he
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem xi_eq {a b c : ℝ} {p q na nb nc ma mb mc : ℕ} (ha : 0 < a) (hp : 0 < p)
    (hab : a * q = b * p) (hc : ¬ ∃ r : ℚ, c = r * a)
    (h : (na : ℝ) * a + nb * b + nc * c = ma * a + mb * b + mc * c) :
    na * p + nb * q = ma * p + mb * q := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have key : a * (((na * p + nb * q : ℕ) : ℝ) - ((ma * p + mb * q : ℕ) : ℝ)) =
      p * (((mc : ℝ) - nc) * c) := by
    push_cast; linear_combination (p : ℝ) * h + ((nb : ℝ) - mb) * hab
  by_cases hm : mc = nc
  · subst hm
    simp only [sub_self, zero_mul, mul_zero] at key
    have := (mul_eq_zero.mp key).resolve_left ha.ne'
    exact_mod_cast sub_eq_zero.mp this
  · exfalso
    apply hc
    have hmR : ((mc : ℝ) - nc) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hm)
    refine ⟨(((na * p + nb * q : ℕ) : ℚ) - ((ma * p + mb * q : ℕ) : ℚ)) / (p * ((mc : ℚ) - nc)), ?_⟩
    push_cast at key ⊢
    field_simp
    linear_combination -key
variable {N : ℕ}
def edgeVec (D : Dissection N) (e : Fin N × Fin 3) : Plane :=
  (D.tile e.1).pts (e.2 + 1) - (D.tile e.1).pts e.2
def Internal (D : Dissection N) (e : Fin N × Fin 3) : Prop :=
  openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ⊆ interior D.target.carrier
variable (D : CongruentDissection N)
open Classical in
noncomputable def legWeight (p q : ℕ) (e : Fin N × Fin 3) : ℕ :=
  if edgeType D (tileα D) e then p else if edgeType D (tileβ D) e then q else 0
theorem edgeType_unique {φ ψ : ℝ} {e : Fin N × Fin 3} (h1 : edgeType D φ e)
    (h2 : edgeType D ψ e) : φ = ψ := h1.symm.trans h2
theorem edgeType_cases (e : Fin N × Fin 3) :
    edgeType D (tileα D) e ∨ edgeType D (tileβ D) e ∨ edgeType D (tileγ D) e :=
  localAngle_at_own_vertex_mem' D e.1 (e.2 + 2)
open Classical in
theorem weight_sum (hαβ : tileα D ≠ tileβ D) (p q : ℕ) (part : Finset (Fin N × Fin 3)) :
    ∑ e ∈ part, legWeight D p q e =
      (part.filter (edgeType D (tileα D))).card * p +
        (part.filter (edgeType D (tileβ D))).card * q := by
  have h : ∀ e, legWeight D p q e = (if edgeType D (tileα D) e then p else 0) +
      (if edgeType D (tileβ D) e then q else 0) := by
    intro e
    unfold legWeight
    by_cases h1 : edgeType D (tileα D) e
    · have h2 : ¬ edgeType D (tileβ D) e := fun h2 => hαβ (edgeType_unique D h1 h2)
      simp [h1, h2]
    · simp [h1]
  rw [Finset.sum_congr rfl fun e _ => h e, Finset.sum_add_distrib, ← Finset.sum_filter,
    ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
theorem weight_gamma {p q : ℕ} (hαγ : tileα D ≠ tileγ D) (hβγ : tileβ D ≠ tileγ D)
    {e : Fin N × Fin 3} (h : edgeType D (tileγ D) e) : legWeight D p q e = 0 := by
  have h1 : ¬ edgeType D (tileα D) e := fun h1 => hαγ (edgeType_unique D h1 h)
  have h2 : ¬ edgeType D (tileβ D) e := fun h2 => hβγ (edgeType_unique D h2 h)
  simp [legWeight, h1, h2]
theorem weight_odd {p q : ℕ} (hp : Odd p) (hq : Odd q) {e : Fin N × Fin 3}
    (h : ¬ edgeType D (tileγ D) e) : ((legWeight D p q e : ℕ) : ZMod 2) = 1 := by
  unfold legWeight
  rcases edgeType_cases D e with h1 | h1 | h1
  · simp [h1, ZMod.natCast_eq_one_iff_odd.mpr hp]
  · by_cases h0 : edgeType D (tileα D) e
    · simp [h0, ZMod.natCast_eq_one_iff_odd.mpr hp]
    · simp [h0, h1, ZMod.natCast_eq_one_iff_odd.mpr hq]
  · exact absurd h1 h
open Classical in
theorem typed_lengths (hsep : AnglesSep D) (part : Finset (Fin N × Fin 3)) :
    ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      ((part.filter (edgeType D (tileα D))).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      + ((part.filter (edgeType D (tileβ D))).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      + ((part.filter (edgeType D (tileγ D))).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) :=
  side_walk_counts_sep D hsep part _ rfl
theorem fin3_sum (k : Fin 3) (g : Fin 3 → ZMod 2) : ∑ m, g m = g k + g (k + 1) + g (k + 2) := by
  fin_cases k <;> simp [Fin.sum_univ_three] <;> ring
open Classical in
theorem legs_one (hright : tileγ D = Real.pi / 2) (hsep : AnglesSep D) (θ : ℝ)
    (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) (i : Fin N) :
    (∑ m : Fin 3, if ¬ edgeType D (tileγ D) (i, m) ∧
        DirClass.Cls θ (dirC (edgeVec D.toDissection (i, m))) then (1 : ZMod 2) else 0) = 1 := by
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp (tile_angle_count_sep D hsep i).2.2
  have hkk : cornerAngle ((D.tile i).pts (k + 1)) ((D.tile i).pts k) ((D.tile i).pts (k + 2)) =
      tileγ D := by
    have : k ∈ ({k} : Finset (Fin 3)) := Finset.mem_singleton_self k
    rw [← hk] at this; exact (Finset.mem_filter.mp this).2
  have huniq : ∀ m : Fin 3, cornerAngle ((D.tile i).pts (m + 1)) ((D.tile i).pts m)
      ((D.tile i).pts (m + 2)) = tileγ D → m = k := by
    intro m hm
    have : m ∈ Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileγ D :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    rw [hk] at this; exact Finset.mem_singleton.mp this
  have htype : ∀ m : Fin 3, edgeType D (tileγ D) (i, m) ↔ m + 2 = k := by
    intro m
    unfold edgeType
    rw [Tri.localAngle_vertex]
    constructor
    · exact huniq (m + 2)
    · rintro rfl; exact hkk
  have hperp : inner ℝ ((D.tile i).pts (k + 1) - (D.tile i).pts k)
      ((D.tile i).pts (k + 2) - (D.tile i).pts k) = 0 := by
    rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    rw [← hright, ← hkk]; rfl
  have hu : (D.tile i).pts (k + 1) - (D.tile i).pts k ≠ 0 :=
    sub_ne_zero.mpr (tile_pts_ne D.toDissection i k).symm
  have hv : (D.tile i).pts (k + 2) - (D.tile i).pts k ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have := (D.tile i).indep.injective h
    have h2 : ∀ m : Fin 3, m + 2 ≠ m := by decide
    exact h2 k this
  have hd := dirC_of_inner hu hv hperp
  have e1 : edgeVec D.toDissection (i, k + 2) =
      -((D.tile i).pts (k + 2) - (D.tile i).pts k) := by
    unfold edgeVec
    have : k + 2 + 1 = k := by fin_cases k <;> rfl
    simp only [this]; abel
  have hcls : DirClass.Cls θ (dirC (edgeVec D.toDissection (i, k + 2))) ↔
      ¬ DirClass.Cls θ (dirC (edgeVec D.toDissection (i, k))) := by
    rw [e1, dirC_neg, hd]
    exact DirClass.cls_neg θ hθ (dirC_ne hu)
  have t0 : ¬ edgeType D (tileγ D) (i, k) := by
    rw [htype]; fin_cases k <;> decide
  have t1 : edgeType D (tileγ D) (i, k + 1) := by
    rw [htype]; fin_cases k <;> rfl
  have t2 : ¬ edgeType D (tileγ D) (i, k + 2) := by
    rw [htype]; fin_cases k <;> decide
  rw [fin3_sum k]
  simp only [t0, t1, t2, not_true_eq_false, not_false_eq_true, true_and, false_and, if_false,
    add_zero]
  by_cases h : DirClass.Cls θ (dirC (edgeVec D.toDissection (i, k)))
  · simp [h]
    simp [hcls, h]
  · simp [h, hcls.mpr h]
theorem lineChain_pair_iff (Dd : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (e : Fin N × Fin 3) :
    (e ∈ Dd.lineChain f c ∨ e ∈ Dd.lineChain (-f) (-c)) ↔
      f ((Dd.tile e.1).pts e.2) = c ∧ f ((Dd.tile e.1).pts (e.2 + 1)) = c := by
  constructor
  · rintro (h | h)
    · obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp h; exact ⟨h1, h2⟩
    · obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp h
      simp only [LinearMap.neg_apply, neg_inj] at h1 h2
      exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hall : ∀ i : Fin 3, i = e.2 ∨ i = e.2 + 1 ∨ i = e.2 + 2 := by
      have : ∀ k i : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := by decide
      exact fun i => this e.2 i
    by_cases hR : f ((Dd.tile e.1).pts (e.2 + 2)) ≤ c
    · left
      refine Dissection.mem_lineChain.mpr ⟨h1, h2, fun i => ?_⟩
      rcases hall i with rfl | rfl | rfl
      · exact h1.le
      · exact h2.le
      · exact hR
    · right
      refine Dissection.mem_lineChain.mpr ⟨by simp [h1], by simp [h2], fun i => ?_⟩
      rcases hall i with rfl | rfl | rfl
      · simp [h1]
      · simp [h2]
      · simp only [LinearMap.neg_apply, neg_le_neg_iff]; linarith
theorem chain_disjoint (Dd : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) :
    Disjoint (Dd.lineChain f c) (Dd.lineChain (-f) (-c)) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨-, -, hle⟩ := Dissection.mem_lineChain.mp h1
  obtain ⟨-, -, hge⟩ := Dissection.mem_lineChain.mp h2
  exact two_vertices_on_line (Dd.tile e.1) f c hf fun i =>
    le_antisymm (hle i) (by have := hge i; simp only [LinearMap.neg_apply, neg_le_neg_iff] at this; exact this)
theorem edgeLine_eq_iff (Dd : Dissection N) (e e1 : Fin N × Fin 3) :
    edgeLine Dd e = edgeLine Dd e1 ↔
      ((Dd.tile e.1).pts e.2 ∈ edgeLine Dd e1 ∧ (Dd.tile e.1).pts (e.2 + 1) ∈ edgeLine Dd e1) := by
  constructor
  · intro h
    rw [← h]
    exact ⟨left_mem_lineSet _ _, right_mem_lineSet _ _⟩
  · rintro ⟨h1, h2⟩
    exact lineSet_eq (tile_pts_ne Dd e1.1 e1.2) (tile_pts_ne Dd e.1 e.2) h1 h2
theorem not_internal_of_side (Dd : Dissection N) {e : Fin N × Fin 3} {i : Fin 3}
    (h : (Dd.tile e.1).edge e.2 ⊆ segment ℝ (Dd.target.pts i) (Dd.target.pts (i + 1))) :
    ¬ Internal Dd e := by
  intro hI
  have hmid : (1 / 2 : ℝ) • (Dd.tile e.1).pts e.2 + (1 / 2 : ℝ) • (Dd.tile e.1).pts (e.2 + 1) ∈
      openSegment ℝ ((Dd.tile e.1).pts e.2) ((Dd.tile e.1).pts (e.2 + 1)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hfr := tri_side_subset_frontier Dd.target i (h (openSegment_subset_segment ℝ _ _ hmid))
  exact hfr.2 (hI hmid)
theorem internal_of_line (Dd : Dissection N) {e e1 : Fin N × Fin 3} (h1 : Internal Dd e1)
    (hl : edgeLine Dd e = edgeLine Dd e1) : Internal Dd e := by
  rcases edge_internal_or_side Dd e with h | ⟨i, hi⟩
  · exact h
  · exfalso
    obtain ⟨f, c, -, hle, hfi, hfi1, hfi2⟩ := exists_supporting Dd.target i
    have hS := target_contact_side Dd.target f c hle hfi hfi1 hfi2
    have hTne : Dd.target.pts i ≠ Dd.target.pts (i + 1) := by
      intro h
      have := Dd.target.indep.injective h
      have h2 : ∀ m : Fin 3, m ≠ m + 1 := by decide
      exact h2 i this
    have hline : edgeLine Dd e = lineSet (Dd.target.pts i) (Dd.target.pts (i + 1)) :=
      lineSet_eq hTne (tile_pts_ne Dd e.1 e.2)
        (segment_subset_lineSet _ _ (hi (left_mem_segment ℝ _ _)))
        (segment_subset_lineSet _ _ (hi (right_mem_segment ℝ _ _)))
    have hfline : ∀ y ∈ lineSet (Dd.target.pts i) (Dd.target.pts (i + 1)), f y = c := by
      intro y hy
      obtain ⟨t, rfl⟩ := eq_lineMap_of_mem_lineSet hTne hy
      simp [map_add, map_smul, map_sub, hfi, hfi1]
    have hon : ∀ y ∈ edgeLine Dd e1, y ∈ Dd.target.carrier →
        y ∈ segment ℝ (Dd.target.pts i) (Dd.target.pts (i + 1)) := by
      intro y hy hyc
      rw [← hS]
      exact ⟨hyc, hfline y (by rw [← hline, hl]; exact hy)⟩
    have hP1 := hon _ (left_mem_lineSet _ _) (edge_subset_target Dd e1 (left_mem_segment ℝ _ _))
    have hQ1 := hon _ (right_mem_lineSet _ _) (edge_subset_target Dd e1 (right_mem_segment ℝ _ _))
    exact not_internal_of_side Dd (e := e1) (i := i)
      ((convex_segment _ _).segment_subset hP1 hQ1) h1
open Classical in
theorem interior_weight (hsep : AnglesSep D) (hαβ : tileα D ≠ tileβ D)
    (hαγ : tileα D ≠ tileγ D) (hβγ : tileβ D ≠ tileγ D) {p q : ℕ} (hp0 : 0 < p)
    (hratio : dist (D.model.pts 1) (D.model.pts 2) * q = dist (D.model.pts 2) (D.model.pts 0) * p)
    (hcirr : ¬ ∃ r : ℚ, dist (D.model.pts 0) (D.model.pts 1) = r * dist (D.model.pts 1) (D.model.pts 2))
    (θ : ℝ) :
    (∑ e, if Internal D.toDissection e ∧ ¬ edgeType D (tileγ D) e ∧
        DirClass.Cls θ (dirC (edgeVec D.toDissection e))
      then ((legWeight D p q e : ℕ) : ZMod 2) else 0) = 0 := by
  set Dd := D.toDissection
  have ha0 : 0 < dist (D.model.pts 1) (D.model.pts 2) := dist_pos.mpr fun h => by
    have := D.model.indep.injective h; exact absurd this (by decide)
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image (edgeLine Dd))
    (g := edgeLine Dd) (fun e _ => Finset.mem_image_of_mem _ (Finset.mem_univ e))]
  apply Finset.sum_eq_zero
  intro ℓ _
  by_cases hex : ∃ e1, edgeLine Dd e1 = ℓ ∧ Internal Dd e1 ∧
      DirClass.Cls θ (dirC (edgeVec Dd e1))
  swap
  · apply Finset.sum_eq_zero
    intro e he
    rw [if_neg]
    rintro ⟨hI, -, hCe⟩
    exact hex ⟨e, (Finset.mem_filter.mp he).2, hI, hCe⟩
  obtain ⟨e1, rfl, hI1, hC1⟩ := hex
  have hPQ1 := tile_pts_ne Dd e1.1 e1.2
  set P1 := (Dd.tile e1.1).pts e1.2
  set Q1 := (Dd.tile e1.1).pts (e1.2 + 1)
  set f := crossL (Q1 - P1)
  set c0 := cross (Q1 - P1) P1
  have hf : f ≠ 0 := crossL_ne_zero (sub_ne_zero.mpr hPQ1.symm)
  have hmem : ∀ e, edgeLine Dd e = edgeLine Dd e1 ↔
      (e ∈ Dd.lineChain f c0 ∨ e ∈ Dd.lineChain (-f) (-c0)) := by
    intro e
    rw [edgeLine_eq_iff, lineChain_pair_iff Dd f c0]
    rfl
  have hfib : (Finset.univ.filter fun e => edgeLine Dd e = edgeLine Dd e1) =
      Dd.lineChain f c0 ∪ Dd.lineChain (-f) (-c0) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact hmem e
  have hterm : ∀ e ∈ (Finset.univ.filter fun e => edgeLine Dd e = edgeLine Dd e1),
      (if Internal Dd e ∧ ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec Dd e))
        then ((legWeight D p q e : ℕ) : ZMod 2) else 0) = ((legWeight D p q e : ℕ) : ZMod 2) := by
    intro e he
    have hl := (Finset.mem_filter.mp he).2
    have hI := internal_of_line Dd hI1 hl
    have hon := (edgeLine_eq_iff Dd e e1).mp hl
    have hCe : DirClass.Cls θ (dirC (edgeVec Dd e)) ↔ DirClass.Cls θ (dirC (edgeVec Dd e1)) := by
      unfold edgeVec
      rw [dirC_lineSet hPQ1 (tile_pts_ne Dd e.1 e.2) hon.1 hon.2]
    by_cases hγ : edgeType D (tileγ D) e
    · rw [weight_gamma D hαγ hβγ hγ]; simp
    · rw [if_pos ⟨hI, hγ, hCe.mpr hC1⟩]
  rw [Finset.sum_congr rfl hterm, hfib, Finset.sum_union (chain_disjoint Dd f c0 hf)]
  have hint : ∀ e ∈ Dd.lineChain f c0 ∪ Dd.lineChain (-f) (-c0),
      openSegment ℝ ((Dd.tile e.1).pts e.2) ((Dd.tile e.1).pts (e.2 + 1)) ⊆
        interior Dd.target.carrier :=
    fun e he => internal_of_line Dd hI1 ((hmem e).mpr (Finset.mem_union.mp he))
  have hbal := line_balance Dd f c0 hf hint
  rw [typed_lengths D hsep, typed_lengths D hsep] at hbal
  have hxi := xi_eq ha0 hp0 hratio hcirr hbal
  rw [← Nat.cast_sum, ← Nat.cast_sum, weight_sum D hαβ, weight_sum D hαβ, ← Nat.cast_add, hxi,
    ZMod.natCast_eq_zero_iff_even]
  exact Even.add_self _
theorem apex_class (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hθ : ¬ ∃ r : ℚ, 4 * tileα D = r * Real.pi) :
    DirClass.Cls (4 * tileα D) (dirC (D.target.pts 1 - D.target.pts 0)) ↔
      DirClass.Cls (4 * tileα D) (dirC (D.target.pts 2 - D.target.pts 1)) := by
  set T := D.target.pts
  have hne : ∀ i j : Fin 3, i ≠ j → T i - T j ≠ 0 := fun i j hij h =>
    hij (D.target.indep.injective (sub_eq_zero.mp h))
  have hang : InnerProductGeometry.angle (T 2 - T 1) (T 0 - T 1) = 2 * tileα D := by
    have := apex_angle D hright hA hC
    rw [Tri.localAngle_vertex] at this
    exact this
  have e0 : dirC (T 1 - T 0) = dirC (T 0 - T 1) := by rw [← neg_sub, dirC_neg]
  rw [e0]
  rcases dirC_of_angle (hne 2 1 (by decide)) (hne 0 1 (by decide)) with h | h
  · rw [h, hang]
    have : Complex.exp (2 * ((2 * tileα D : ℝ) : ℂ) * Complex.I) = DirClass.ω (4 * tileα D) := by
      unfold DirClass.ω; congr 1; push_cast; ring
    rw [this]
    exact DirClass.cls_mul_ω _ hθ (dirC_ne (hne 2 1 (by decide)))
  · rw [h, hang]
    have : Complex.exp (-(2 * ((2 * tileα D : ℝ) : ℂ)) * Complex.I) =
        (DirClass.ω (4 * tileα D))⁻¹ := by
      unfold DirClass.ω; rw [← Complex.exp_neg]; congr 1; push_cast; ring
    rw [this]
    exact DirClass.cls_mul_ω_inv _ hθ (dirC_ne (hne 2 1 (by decide)))
theorem class_on_side {P Q : Plane} (hPQ : P ≠ Q) (θ : ℝ) {e : Fin N × Fin 3}
    (h : (D.tile e.1).edge e.2 ⊆ segment ℝ P Q) :
    DirClass.Cls θ (dirC (edgeVec D.toDissection e)) ↔ DirClass.Cls θ (dirC (Q - P)) := by
  unfold edgeVec
  rw [dirC_lineSet hPQ (tile_pts_ne D.toDissection e.1 e.2)
    (segment_subset_lineSet _ _ (h (left_mem_segment ℝ _ _)))
    (segment_subset_lineSet _ _ (h (right_mem_segment ℝ _ _)))]
open Classical in
theorem boundary_weight (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hsep : AnglesSep D) (hαβ : tileα D ≠ tileβ D)
    (hαγ : tileα D ≠ tileγ D) (hβγ : tileβ D ≠ tileγ D) {p q : ℕ} (hp0 : 0 < p)
    (hratio : dist (D.model.pts 1) (D.model.pts 2) * q = dist (D.model.pts 2) (D.model.pts 0) * p)
    (hcirr : ¬ ∃ r : ℚ, dist (D.model.pts 0) (D.model.pts 1) = r * dist (D.model.pts 1) (D.model.pts 2))
    (hθ : ¬ ∃ r : ℚ, 4 * tileα D = r * Real.pi)
    (hAC : ∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
      edgeType D (tileγ D) e) :
    (∑ e, if ¬ Internal D.toDissection e ∧ ¬ edgeType D (tileγ D) e ∧
        DirClass.Cls (4 * tileα D) (dirC (edgeVec D.toDissection e))
      then ((legWeight D p q e : ℕ) : ZMod 2) else 0) = 0 := by
  set Dd := D.toDissection
  set T := D.target.pts
  set θ := 4 * tileα D
  set w := fun e => ((legWeight D p q e : ℕ) : ZMod 2)
  have ha0 : 0 < dist (D.model.pts 1) (D.model.pts 2) := dist_pos.mpr fun h => by
    have := D.model.indep.injective h; exact absurd this (by decide)
  have hT : ∀ i j : Fin 3, i ≠ j → T i ≠ T j := fun i j hij h => hij (D.target.indep.injective h)
  set CAB := DirClass.Cls θ (dirC (T 1 - T 0))
  have hCBC : DirClass.Cls θ (dirC (T 2 - T 1)) ↔ CAB := (apex_class D hright hA hC hθ).symm
  set AB := segment ℝ (T 0) (T 1)
  set BC := segment ℝ (T 1) (T 2)
  have hdisj : ∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ AB → ¬ (D.tile e.1).edge e.2 ⊆ BC := by
    intro e h1 h2
    have hm : ∀ x ∈ (D.tile e.1).edge e.2, x = T 1 := fun x hx =>
      sides_meet D.target 1 (h2 hx) (h1 hx)
    exact tile_pts_ne Dd e.1 e.2 ((hm _ (left_mem_segment ℝ _ _)).trans
      (hm _ (right_mem_segment ℝ _ _)).symm)
  have hpt : ∀ e : Fin N × Fin 3,
      (if ¬ Internal Dd e ∧ ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec Dd e))
        then w e else 0) =
      (if (D.tile e.1).edge e.2 ⊆ AB ∧ CAB then w e else 0) +
        (if (D.tile e.1).edge e.2 ⊆ BC ∧ CAB then w e else 0) := by
    intro e
    by_cases hγ : edgeType D (tileγ D) e
    · have : w e = 0 := by simp only [w]; rw [weight_gamma D hαγ hβγ hγ]; simp
      simp [hγ, this]
    by_cases hab : (D.tile e.1).edge e.2 ⊆ AB
    · have hbc := hdisj e hab
      have hI : ¬ Internal Dd e := not_internal_of_side Dd (i := 0) hab
      have hc := class_on_side D (hT 0 1 (by decide)) θ hab
      simp only [hI, hγ, not_false_eq_true, true_and, hab, hbc, false_and, if_false, add_zero]
      rw [hc]
    by_cases hbc : (D.tile e.1).edge e.2 ⊆ BC
    · have hI : ¬ Internal Dd e := not_internal_of_side Dd (i := 1) hbc
      have hc := (class_on_side D (hT 1 2 (by decide)) θ hbc).trans hCBC
      simp only [hI, hγ, not_false_eq_true, true_and, hab, hbc, false_and, if_false, zero_add]
      rw [hc]
    simp only [hab, hbc, false_and, if_false, add_zero]
    rw [if_neg]
    rintro ⟨hI, -, -⟩
    rcases edge_internal_or_side Dd e with h | ⟨i, hi⟩
    · exact hI h
    · fin_cases i
      · exact hab hi
      · exact hbc hi
      · exact hγ (hAC e hi)
  rw [Finset.sum_congr rfl fun e _ => hpt e, Finset.sum_add_distrib]
  by_cases hc : CAB
  swap
  · simp [hc]
  simp only [hc, and_true]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  obtain ⟨hXX, -, -⟩ := right_area_core D rfl rfl rfl rfl rfl hright hA hC
  have s0 := side_sum Dd 0
  have s1 := side_sum Dd 1
  have i01 : (0 : Fin 3) + 1 = 1 := rfl
  have i12 : (1 : Fin 3) + 1 = 2 := rfl
  rw [i01] at s0
  rw [i12] at s1
  rw [typed_lengths D hsep] at s0 s1
  have hlen := s0.trans (hXX.symm.trans s1.symm)
  have hxi := xi_eq ha0 hp0 hratio hcirr hlen
  simp only [w]
  rw [← Nat.cast_sum, ← Nat.cast_sum, weight_sum D hαβ, weight_sum D hαβ, ← Nat.cast_add, hxi,
    ZMod.natCast_eq_zero_iff_even]
  exact Even.add_self _
open Classical in
theorem parity_even (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hαirr : ¬ ∃ r : ℚ, tileα D = r * Real.pi) {p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hratio : dist (D.model.pts 1) (D.model.pts 2) * q = dist (D.model.pts 2) (D.model.pts 0) * p)
    (hcirr : ¬ ∃ r : ℚ, dist (D.model.pts 0) (D.model.pts 1) = r * dist (D.model.pts 1) (D.model.pts 2))
    (hAC : ∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
      edgeType D (tileγ D) e) :
    Even N := by
  have hsep := anglesSep_right D hright hαirr
  have hβ := right_beta D hright
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  have hαβ : tileα D ≠ tileβ D := fun h => hαirr ⟨1 / 4, by push_cast; linarith⟩
  have hαγ : tileα D ≠ tileγ D := by rw [hright]; linarith
  have hβγ : tileβ D ≠ tileγ D := by rw [hright]; linarith
  have hθ : ¬ ∃ r : ℚ, 4 * tileα D = r * Real.pi := fun ⟨r, hr⟩ =>
    hαirr ⟨r / 4, by push_cast; linarith⟩
  have hp0 : 0 < p := hp.pos
  set θ := 4 * tileα D
  have hN : (∑ e, if ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e))
      then ((legWeight D p q e : ℕ) : ZMod 2) else 0) = N := by
    have h1 : ∀ e : Fin N × Fin 3, (if ¬ edgeType D (tileγ D) e ∧
        DirClass.Cls θ (dirC (edgeVec D.toDissection e)) then ((legWeight D p q e : ℕ) : ZMod 2) else 0) =
        if ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e)) then 1 else 0 := by
      intro e
      by_cases h : ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e))
      · rw [if_pos h, if_pos h, weight_odd D hp hq h.1]
      · rw [if_neg h, if_neg h]
    rw [Finset.sum_congr rfl fun e _ => h1 e, Fintype.sum_prod_type]
    simp only [legs_one D hright hsep θ hθ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hsplit : ∀ e : Fin N × Fin 3,
      (if ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e))
        then ((legWeight D p q e : ℕ) : ZMod 2) else 0) =
      (if Internal D.toDissection e ∧ ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e))
        then ((legWeight D p q e : ℕ) : ZMod 2) else 0) +
      (if ¬ Internal D.toDissection e ∧ ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e))
        then ((legWeight D p q e : ℕ) : ZMod 2) else 0) := by
    intro e
    by_cases hI : Internal D.toDissection e <;> simp [hI]
  rw [Finset.sum_congr rfl fun e _ => hsplit e, Finset.sum_add_distrib,
    interior_weight D hsep hαβ hαγ hβγ hp0 hratio hcirr θ,
    boundary_weight D hright hA hC hsep hαβ hαγ hβγ hp0 hratio hcirr hθ hAC, add_zero] at hN
  exact ZMod.natCast_eq_zero_iff_even.mp hN.symm
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem two_sq_of_sqrt_rat {N : ℕ} (h : ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q) :
    ∃ m : ℕ, N = 2 * m ^ 2 := by
  obtain ⟨q, hq⟩ := h
  have hsq : ¬ Irrational (Real.sqrt ((2 * N : ℕ) : ℝ)) := by
    intro hi
    apply hi
    refine ⟨2 * q, ?_⟩
    rw [show ((2 * N : ℕ) : ℝ) = (2 * Real.sqrt ((N : ℝ) / 2)) ^ 2 by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; push_cast; ring,
      Real.sqrt_sq (by positivity), hq]
    push_cast; ring
  rw [irrational_sqrt_natCast_iff, not_not] at hsq
  obtain ⟨m, hm⟩ := hsq
  have h2 : 2 ∣ m := by
    have : 2 ∣ m * m := ⟨N, hm.symm⟩
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with h | h <;> exact h
  obtain ⟨k, rfl⟩ := h2
  exact ⟨k, by ring_nf at hm; linarith⟩
theorem quad_split {s : ℝ} {d : ℕ} (hs : s ^ 2 = d) (hirr : Irrational s) {U V M : ℚ}
    (h : ((U : ℝ) + V * s) ^ 2 = M) : U * V = 0 := by
  by_contra hUV
  apply hirr
  have h2 : (2 : ℚ) * U * V ≠ 0 := by rw [mul_assoc]; exact mul_ne_zero two_ne_zero hUV
  refine ⟨(M - U ^ 2 - V ^ 2 * d) / (2 * U * V), ?_⟩
  have h2' : (2 : ℝ) * U * V ≠ 0 := by exact_mod_cast h2
  push_cast
  rw [div_eq_iff h2']
  linear_combination -h + (V : ℝ) ^ 2 * hs
theorem sq_of_sqrt2 {N m n : ℕ} {l : ℝ} (hl : l ^ 2 = (N : ℝ) / 2) (hirr : ¬ ∃ q : ℚ, l = q)
    (h : 2 * l = m * Real.sqrt 2 + n) : N = m ^ 2 := by
  have hs : Real.sqrt 2 ^ 2 = ((2 : ℕ) : ℝ) := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hsq : (((n : ℚ) : ℝ) + ((m : ℚ) : ℝ) * Real.sqrt 2) ^ 2 = ((2 * N : ℚ) : ℝ) := by
    push_cast; rw [add_comm, ← h]; linear_combination 4 * hl
  have h0 := quad_split hs irrational_sqrt_two hsq
  rcases mul_eq_zero.mp h0 with hn | hm
  · have hn : n = 0 := by exact_mod_cast hn
    subst hn
    simp only [Nat.cast_zero, Rat.cast_zero, zero_add] at hsq
    have : ((N : ℝ)) = (m : ℝ) ^ 2 := by
      rw [mul_pow, hs] at hsq; push_cast at hsq; linarith
    exact_mod_cast this
  · have hm : m = 0 := by exact_mod_cast hm
    subst hm
    simp only [Nat.cast_zero, zero_mul, zero_add] at h
    exact absurd ⟨n / 2, by push_cast; linarith⟩ hirr
theorem six_sq_of_sqrt3 {N m n : ℕ} {l : ℝ} (hl : l ^ 2 = (N : ℝ) / 2) (hirr : ¬ ∃ q : ℚ, l = q)
    (h : 2 * l = m * Real.sqrt 3 + n) : ∃ k : ℕ, N = 6 * k ^ 2 := by
  have hs : Real.sqrt 3 ^ 2 = ((3 : ℕ) : ℝ) := by rw [Real.sq_sqrt (by norm_num)]; norm_num
  have hsq : (((n : ℚ) : ℝ) + ((m : ℚ) : ℝ) * Real.sqrt 3) ^ 2 = ((2 * N : ℚ) : ℝ) := by
    push_cast; rw [add_comm, ← h]; linear_combination 4 * hl
  have hirr3 : Irrational (Real.sqrt 3) := by
    have := Nat.Prime.irrational_sqrt (show Nat.Prime 3 by norm_num)
    exact_mod_cast this
  have h0 := quad_split hs hirr3 hsq
  rcases mul_eq_zero.mp h0 with hn | hm
  · have hn : n = 0 := by exact_mod_cast hn
    subst hn
    simp only [Nat.cast_zero, Rat.cast_zero, zero_add] at hsq
    have hR : (2 * N : ℝ) = 3 * (m : ℝ) ^ 2 := by
      rw [mul_pow, hs] at hsq; push_cast at hsq; linarith
    have hN : 2 * N = 3 * m ^ 2 := by exact_mod_cast hR
    have h2 : 2 ∣ m := by
      have : 2 ∣ 3 * (m * m) := ⟨N, by rw [← sq]; exact hN.symm⟩
      have : 2 ∣ m * m := (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this)
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with h | h <;> exact h
    obtain ⟨k, rfl⟩ := h2
    exact ⟨k, by ring_nf at hN; linarith⟩
  · have hm : m = 0 := by exact_mod_cast hm
    subst hm
    simp only [Nat.cast_zero, zero_mul, zero_add] at h
    exact absurd ⟨n / 2, by push_cast; linarith⟩ hirr
theorem rationalisosceles {N : ℕ} (D : CongruentDissection N) (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hrat : ∃ r : ℚ, tileα D = r * Real.pi) :
    (∃ m : ℕ, N = 2 * m ^ 2) ∨
    ((∃ m : ℕ, N = m ^ 2) ∧ tileβ D = Real.pi / 4) ∨
    ((∃ m : ℕ, N = 6 * m ^ 2) ∧
      ((tileβ D = Real.pi / 6 ∧ tileα D = Real.pi / 3) ∨
        (tileβ D = Real.pi / 3 ∧ tileα D = Real.pi / 6))) := by
  by_cases hq : ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q
  · exact Or.inl (two_sq_of_sqrt_rat hq)
  set a := dist (D.model.pts 1) (D.model.pts 2) with hadef
  set b := dist (D.model.pts 2) (D.model.pts 0) with hbdef
  set c := dist (D.model.pts 0) (D.model.pts 1) with hcdef
  set l := Real.sqrt ((N : ℝ) / 2) with hldef
  have hlQ : l ^ 2 = (((N : ℚ) / 2 : ℚ) : ℝ) := by
    rw [hldef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hlR : l ^ 2 = (N : ℝ) / 2 := by rw [hlQ]; push_cast; ring
  have hc0 : 0 < c := dist_pos.mpr fun e => by
    have := D.model.indep.injective e; exact absurd this (by decide)
  have hβ := right_beta D hright
  obtain ⟨hab, -⟩ := right_trig D hright
  change a = Real.cos (tileβ D) * c at hab
  have hbs : b = Real.sin (tileβ D) * c := right_sin D hright
  have hcos : Real.cos (tileβ D) = a / c := by rw [hab]; field_simp
  have hsin : Real.sin (tileβ D) = b / c := by rw [hbs]; field_simp
  have hβcases : tileβ D = Real.pi / 6 ∨ tileβ D = Real.pi / 4 ∨ tileβ D = Real.pi / 3 := by
    by_cases h6 : tileβ D = Real.pi / 6
    · exact Or.inl h6
    obtain ⟨hina, hinb⟩ := isosceleshelper2 D hright hA hC h6 hq
    by_contra hne
    push Not at hne
    obtain ⟨r, hr⟩ := hrat
    exact beta_irrational_of_quadratic D hright hlQ (hcos ▸ hina) (hsin ▸ hinb) h6 hne.2.1
      hne.2.2 ⟨1 / 2 - r, by rw [hβ, hr]; push_cast; ring⟩
  obtain ⟨-, -, hN⟩ := right_area_core D rfl rfl rfl rfl rfl hright hA hC
  set X := dist (D.target.pts 0) (D.target.pts 1)
  have hXl : X = l * c := by
    have h1 : X ^ 2 = (l * c) ^ 2 := by
      rw [mul_pow, hlR]; linarith
    exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp h1
  obtain ⟨-, -, P, Q, R, hs0, -⟩ := side_rel D 0
  have i01 : (0 : Fin 3) + 1 = 1 := rfl
  rw [i01] at hs0
  have e0 : l = P * Real.cos (tileβ D) + Q * Real.sin (tileβ D) + R := by
    rw [hcos, hsin]; field_simp; rw [← hXl]; linarith
  rcases hβcases with h | h | h
  · 
    rw [h, Real.cos_pi_div_six, Real.sin_pi_div_six] at e0
    have e : 2 * l = (P : ℝ) * Real.sqrt 3 + ((Q + 2 * R : ℕ) : ℝ) := by
      rw [e0]; push_cast; ring
    exact Or.inr (Or.inr ⟨six_sq_of_sqrt3 hlR hq e, Or.inl ⟨h, by linarith⟩⟩)
  · 
    rw [h, Real.cos_pi_div_four, Real.sin_pi_div_four] at e0
    have e : 2 * l = ((P + Q : ℕ) : ℝ) * Real.sqrt 2 + ((2 * R : ℕ) : ℝ) := by
      rw [e0]; push_cast; ring
    exact Or.inr (Or.inl ⟨⟨_, sq_of_sqrt2 hlR hq e⟩, h⟩)
  · 
    rw [h, Real.cos_pi_div_three, Real.sin_pi_div_three] at e0
    have e : 2 * l = (Q : ℝ) * Real.sqrt 3 + ((P + 2 * R : ℕ) : ℝ) := by
      rw [e0]; push_cast; ring
    exact Or.inr (Or.inr ⟨six_sq_of_sqrt3 hlR hq e, Or.inr ⟨h, by linarith⟩⟩)
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem nat_sum_sq_of_rat {n : ℕ} {u v : ℚ} (h : (n : ℚ) = u ^ 2 + v ^ 2) :
    ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, rfl⟩
  set d := u.den * v.den with hd
  have hd0 : 0 < d := Nat.mul_pos u.den_pos v.den_pos
  have hA : (u.num * v.den : ℤ) = u * d := by
    rw [hd]; push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  have hB : (v.num * u.den : ℤ) = v * d := by
    rw [hd]; push_cast
    rw [mul_comm (u.den : ℚ), ← mul_assoc, Rat.mul_den_eq_num]
  have hnd : n * d ^ 2 = (u.num * v.den).natAbs ^ 2 + (v.num * u.den).natAbs ^ 2 := by
    have : ((n * d ^ 2 : ℕ) : ℤ) = (u.num * v.den) ^ 2 + (v.num * u.den) ^ 2 := by
      have hq : ((n * d ^ 2 : ℕ) : ℚ) = ((u.num * v.den : ℤ) : ℚ) ^ 2 + ((v.num * u.den : ℤ) : ℚ) ^ 2 := by
        rw [hA, hB]; push_cast; rw [h]; ring
      exact_mod_cast hq
    have h2 : ((n * d ^ 2 : ℕ) : ℤ) = (((u.num * v.den).natAbs ^ 2 +
        (v.num * u.den).natAbs ^ 2 : ℕ) : ℤ) := by
      rw [this]; push_cast; rw [sq_abs, sq_abs]
    exact_mod_cast h2
  have key := Nat.eq_sq_add_sq_iff.mp ⟨_, _, hnd⟩
  apply Nat.eq_sq_add_sq_iff.mpr
  intro q hq hq3
  have hqn : q ∈ (n * d ^ 2).primeFactors :=
    Nat.primeFactors_mono (dvd_mul_right n _) (by positivity) hq
  have hev := key q hqn hq3
  haveI := Fact.mk (Nat.prime_of_mem_primeFactors hq)
  rw [padicValNat.mul (by omega) (by positivity), padicValNat.pow] at hev
  obtain ⟨k, hk⟩ := hev
  exact ⟨k - padicValNat q d, by omega⟩
theorem odd_legs {N p q g h : ℕ} (hN : Odd N) (hpq : Nat.Coprime p q) (hgh : Nat.Coprime g h)
    (heq : g ^ 2 * (p ^ 2 + q ^ 2) * N = 2 * h ^ 2) : Odd p ∧ Odd q := by
  by_contra hn
  have hE : Even (g ^ 2 * (p ^ 2 + q ^ 2) * N) := ⟨h ^ 2, by rw [heq]; ring⟩
  rcases Nat.even_mul.mp hE with hE | hE
  swap
  · exact (Nat.not_even_iff_odd.mpr hN) hE
  rcases Nat.even_mul.mp hE with hg | hpq2
  · 
    have hg' : Even g := (Nat.even_pow' two_ne_zero).mp hg
    obtain ⟨g', rfl⟩ := hg'
    have hh : Even (h ^ 2) := ⟨g' ^ 2 * (p ^ 2 + q ^ 2) * N, by ring_nf at heq ⊢; linarith⟩
    have hh' : Even h := (Nat.even_pow' two_ne_zero).mp hh
    have h2 : 2 ∣ Nat.gcd (g' + g') h :=
      Nat.dvd_gcd ⟨g', by ring⟩ (even_iff_two_dvd.mp hh')
    rw [hgh] at h2
    exact absurd h2 (by norm_num)
  · 
    rw [Nat.even_add, Nat.even_pow' two_ne_zero, Nat.even_pow' two_ne_zero] at hpq2
    have hpe : Even p := by
      by_contra hp
      have hq : ¬ Even q := fun hq => hp (hpq2.mpr hq)
      exact hn ⟨Nat.not_even_iff_odd.mp hp, Nat.not_even_iff_odd.mp hq⟩
    have hqe : Even q := hpq2.mp hpe
    have h2 : 2 ∣ Nat.gcd p q := Nat.dvd_gcd (even_iff_two_dvd.mp hpe) (even_iff_two_dvd.mp hqe)
    rw [hpq] at h2
    exact absurd h2 (by norm_num)
variable {N : ℕ}
noncomputable def relabelModel (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) :
    CongruentDissection N where
  toDissection := D.toDissection
  model := D.model.relabel τ
  tiles_congruent := fun i => (D.tiles_congruent i).trans (D.model.congruent_relabel τ)
theorem swap_angles (D : CongruentDissection N) :
    tileα (relabelModel D (Equiv.swap 0 1)) = tileβ D ∧
      tileβ (relabelModel D (Equiv.swap 0 1)) = tileα D ∧
      tileγ (relabelModel D (Equiv.swap 0 1)) = tileγ D := by
  have e0 : (relabelModel D (Equiv.swap 0 1)).model.pts 0 = D.model.pts 1 := rfl
  have e1 : (relabelModel D (Equiv.swap 0 1)).model.pts 1 = D.model.pts 0 := rfl
  have e2 : (relabelModel D (Equiv.swap 0 1)).model.pts 2 = D.model.pts 2 := rfl
  simp only [tileα, tileβ, tileγ, e0, e1, e2]
  exact ⟨angle_comm _ _ _, angle_comm _ _ _, angle_comm _ _ _⟩
variable (D : CongruentDissection N)
theorem isosceles2_beta (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) :
    ((∃ m : ℕ, N = m ^ 2) ∧ tileα D = Real.pi / 4 ∧ tileβ D = Real.pi / 4) ∨
    (∃ m : ℕ, N = 2 * m ^ 2) ∨
    ((∃ k : ℕ, N = 6 * k ^ 2) ∧ (tileβ D = Real.pi / 6 ∨ tileα D = Real.pi / 6)) ∨
    (Even N ∧ (∃ x y : ℕ, N = x ^ 2 + y ^ 2) ∧ ∃ x y : ℕ, N / 2 = x ^ 2 + y ^ 2) := by
  have hβ := right_beta D hright
  by_cases hrat : ∃ r : ℚ, tileα D = r * Real.pi
  · rcases rationalisosceles D hright hA hC hrat with h | ⟨h, hβ4⟩ | ⟨h, hab⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨h, by linarith, hβ4⟩
    · refine Or.inr (Or.inr (Or.inl ⟨h, ?_⟩))
      rcases hab with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact Or.inl h1
      · exact Or.inr h2
  by_cases hq : ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q
  · exact Or.inr (Or.inl (two_sq_of_sqrt_rat hq))
  right; right; right
  have hβk : ∀ k : ℕ, tileβ D ≠ Real.pi / k := fun k h =>
    hrat ⟨1 / 2 - 1 / k, by
      push_cast
      rw [show ((1 : ℝ) / 2 - 1 / k) * Real.pi = Real.pi / 2 - Real.pi / k by ring, ← h]
      linarith⟩
  obtain ⟨⟨x, z, hx, hz⟩, hAC, -⟩ := isosceleshelper3 D hright hA hC
    (by exact_mod_cast hβk 6) (by exact_mod_cast hβk 4) (by exact_mod_cast hβk 3) hq
  set a := dist (D.model.pts 1) (D.model.pts 2) with hadef
  set b := dist (D.model.pts 2) (D.model.pts 0) with hbdef
  set c := dist (D.model.pts 0) (D.model.pts 1) with hcdef
  set l := Real.sqrt ((N : ℝ) / 2) with hldef
  have hl2 : l ^ 2 = (N : ℝ) / 2 := by rw [hldef, Real.sq_sqrt (by positivity)]
  have hpos : ∀ i j : Fin 3, i ≠ j → 0 < dist (D.model.pts i) (D.model.pts j) := fun i j hij =>
    dist_pos.mpr fun h => hij (D.model.indep.injective h)
  have ha0 : 0 < a := hpos 1 2 (by decide)
  have hb0 : 0 < b := hpos 2 0 (by decide)
  have hc0 : 0 < c := hpos 0 1 (by decide)
  have hl0 : 0 < l := by
    rcases (Real.sqrt_nonneg ((N : ℝ) / 2)).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨0, by rw [hldef, ← h]; simp⟩ hq
  have hx0 : (0 : ℚ) < x := by
    have : (0 : ℝ) < x * l := hx ▸ div_pos ha0 hc0
    exact_mod_cast pos_of_mul_pos_left this hl0.le
  have hz0 : (0 : ℚ) < z := by
    have : (0 : ℝ) < z * l := hz ▸ div_pos hb0 hc0
    exact_mod_cast pos_of_mul_pos_left this hl0.le
  have hxzR : ((x : ℝ) ^ 2 + (z : ℝ) ^ 2) * ((N : ℝ) / 2) = 1 := by
    have hp := right_pyth D hright
    rw [← hl2]
    have : (a / c) ^ 2 + (b / c) ^ 2 = 1 := by
      field_simp; linarith
    rw [hx, hz] at this
    linear_combination this
  have hxz : (x ^ 2 + z ^ 2) * ((N : ℚ) / 2) = 1 := by
    have : (((x ^ 2 + z ^ 2) * ((N : ℚ) / 2) : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by push_cast; exact hxzR
    exact Rat.cast_injective this
  set r : ℚ := x / z with hr
  have hr0 : 0 < r := div_pos hx0 hz0
  set p := r.num.natAbs
  set q := r.den
  have hpq : ((p : ℚ) / q) = r := by
    have h1 : (((p : ℤ) : ℚ)) = (r.num : ℚ) := by
      simp only [p, Int.natCast_natAbs, abs_of_pos (Rat.num_pos.mpr hr0)]
    rw [Int.cast_natCast] at h1
    rw [h1]; exact Rat.num_div_den r
  have hcop : Nat.Coprime p q := r.reduced
  have hq0 : (0 : ℚ) < q := by exact_mod_cast r.den_pos
  have hp0 : 0 < p := Int.natAbs_pos.mpr (Rat.num_pos.mpr hr0).ne'
  set s : ℚ := z / q
  have hs0 : 0 < s := div_pos hz0 hq0
  have hxs : x = p * s := by
    have : x = r * z := by rw [hr]; field_simp
    rw [this, ← hpq]; simp only [s]; field_simp
  have hzs : z = q * s := by simp only [s]; field_simp
  clear_value s
  have hratio : a * q = b * p := by
    have ha : a = c * (x * l) := by rw [← hx]; field_simp
    have hb : b = c * (z * l) := by rw [← hz]; field_simp
    rw [ha, hb, hxs, hzs]; push_cast; ring
  have hcirr : ¬ ∃ r' : ℚ, c = r' * a := by
    rintro ⟨r', hr'⟩
    have ha : a = c * (x * l) := by rw [← hx]; field_simp
    have h1 : (r' : ℝ) * x * l = 1 := by
      have : c * 1 = c * (r' * x * l) := by rw [mul_one]; nth_rewrite 1 [hr', ha]; ring
      exact (mul_left_cancel₀ hc0.ne' this).symm
    have hrx : (r' * x : ℚ) ≠ 0 := by
      intro h0
      have : ((r' * x : ℚ) : ℝ) = 0 := by exact_mod_cast h0
      push_cast at this; rw [this] at h1; simp at h1
    apply hq
    refine ⟨1 / (r' * x), ?_⟩
    have : ((r' * x : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hrx
    push_cast at this ⊢
    rw [eq_div_iff this]
    linear_combination h1
  have hsN : s ^ 2 * ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * N = 2 := by
    rw [hxs, hzs] at hxz; linear_combination 2 * hxz
  have hEven : Even N := by
    by_contra hodd
    have hN : Odd N := Nat.not_even_iff_odd.mp hodd
    set g := s.num.natAbs
    set h := s.den
    have hgs : ((g : ℚ) / h) = s := by
      have h1 : (((g : ℤ) : ℚ)) = (s.num : ℚ) := by
        simp only [g, Int.natCast_natAbs, abs_of_pos (Rat.num_pos.mpr hs0)]
      rw [Int.cast_natCast] at h1
      rw [h1]; exact Rat.num_div_den s
    have hh0 : (h : ℚ) ≠ 0 := by exact_mod_cast s.den_pos.ne'
    have heq : g ^ 2 * (p ^ 2 + q ^ 2) * N = 2 * h ^ 2 := by
      have : ((g : ℚ)) ^ 2 * ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * N = 2 * (h : ℚ) ^ 2 := by
        rw [← hgs] at hsN; field_simp at hsN; linear_combination hsN
      exact_mod_cast this
    obtain ⟨hpo, hqo⟩ := odd_legs hN hcop s.reduced heq
    exact hodd (parity_even D hright hA hC hrat hpo hqo hratio hcirr hAC)
  obtain ⟨M, hM⟩ := hEven
  have hM2 : N / 2 = M := by omega
  set t : ℚ := 1 / (((p : ℚ) ^ 2 + (q : ℚ) ^ 2) * s)
  have hpq2 : (0 : ℚ) < (p : ℚ) ^ 2 + (q : ℚ) ^ 2 := by positivity
  have hK : (M : ℚ) * (s ^ 2 * ((p : ℚ) ^ 2 + (q : ℚ) ^ 2)) = 1 := by
    have : (N : ℚ) = 2 * M := by rw [hM]; push_cast; ring
    rw [this] at hsN; linear_combination hsN / 2
  have hs2 : s ^ 2 * ((p : ℚ) ^ 2 + (q : ℚ) ^ 2) ≠ 0 := by positivity
  have hMt : (M : ℚ) = (p * t) ^ 2 + (q * t) ^ 2 := by
    have : (p * t) ^ 2 + (q * t) ^ 2 = 1 / (s ^ 2 * ((p : ℚ) ^ 2 + (q : ℚ) ^ 2)) := by
      have := hpq2.ne'; have := hs0.ne'
      simp only [t]; field_simp
    rw [this, eq_div_iff hs2, hK]
  obtain ⟨u, v, huv⟩ := nat_sum_sq_of_rat hMt
  refine ⟨⟨M, hM⟩, ⟨u + v, ((u : ℤ) - v).natAbs, ?_⟩, ⟨u, v, by rw [hM2, huv]⟩⟩
  have : (N : ℤ) = ((u + v : ℕ) : ℤ) ^ 2 + (((u : ℤ) - v).natAbs : ℤ) ^ 2 := by
    rw [Int.natAbs_sq, hM, huv]; push_cast; ring
  exact_mod_cast this
theorem isosceles2_of_baseangles (hright : tileγ D = Real.pi / 2)
    (hbase : (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) ∨
      (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)) :
    ((∃ m : ℕ, N = m ^ 2) ∧ tileα D = Real.pi / 4 ∧ tileβ D = Real.pi / 4) ∨
    (∃ m : ℕ, N = 2 * m ^ 2) ∨
    ((∃ k : ℕ, N = 6 * k ^ 2) ∧ (tileβ D = Real.pi / 6 ∨ tileα D = Real.pi / 6)) ∨
    (Even N ∧ (∃ x y : ℕ, N = x ^ 2 + y ^ 2) ∧ ∃ x y : ℕ, N / 2 = x ^ 2 + y ^ 2) := by
  rcases hbase with ⟨hA, hC⟩ | ⟨hA, hC⟩
  · exact isosceles2_beta D hright hA hC
  · obtain ⟨eα, eβ, eγ⟩ := swap_angles D
    have h := isosceles2_beta (relabelModel D (Equiv.swap 0 1)) (by rw [eγ]; exact hright)
      (by rw [eβ]; exact hA) (by rw [eβ]; exact hC)
    rw [eα, eβ] at h
    rcases h with ⟨h1, h2, h3⟩ | h | ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, h3, h2⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, h2.symm⟩))
    · exact Or.inr (Or.inr (Or.inr h))
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
theorem sum_sq_mod_four (x y : ℕ) : (x ^ 2 + y ^ 2) % 4 ≠ 3 := by
  have h : ∀ z : ℕ, z ^ 2 % 4 = 0 ∨ z ^ 2 % 4 = 1 := by
    intro z
    rcases Nat.even_or_odd z with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left; ring_nf; omega
    · right; ring_nf; omega
  rcases h x with hx | hx <;> rcases h y with hy | hy <;> omega
theorem not_prime_sq (m : ℕ) : ¬ (m ^ 2).Prime := by
  rw [sq]; intro h
  rcases Nat.prime_mul_iff.mp h with ⟨hm, rfl⟩ | ⟨hm, rfl⟩ <;> exact Nat.not_prime_one hm
theorem notprime_arith {N : ℕ} (hN2 : 2 < N)
    (h : (∃ m : ℕ, N = m ^ 2) ∨ (∃ m : ℕ, N = 2 * m ^ 2) ∨ (∃ k : ℕ, N = 6 * k ^ 2) ∨
      (Even N ∧ ∃ x y : ℕ, N / 2 = x ^ 2 + y ^ 2)) :
    ¬ N.Prime ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → N = 2 * p → N = 6 := by
  constructor
  · intro hp
    rcases h with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨k, rfl⟩ | ⟨he, -⟩
    · exact not_prime_sq m hp
    · have := (Nat.prime_mul_iff.mp hp)
      rcases this with ⟨-, h1⟩ | ⟨-, h1⟩
      · simp at h1; subst h1; norm_num at hN2
      · simp at h1
    · have := (Nat.prime_mul_iff.mp hp)
      rcases this with ⟨h6, -⟩ | ⟨-, h1⟩
      · norm_num at h6
      · omega
    · exact (Nat.Prime.even_iff hp).mp he ▸ hN2 |>.false
  · intro p hp hp3 hNp
    subst hNp
    rcases h with ⟨m, hm⟩ | ⟨m, hm⟩ | ⟨k, hk⟩ | ⟨-, x, y, hxy⟩
    · 
      exfalso
      have h2 : 2 ∣ m := (Nat.Prime.dvd_mul Nat.prime_two).mp ⟨p, by rw [← sq, ← hm]⟩ |>.elim id id
      obtain ⟨j, rfl⟩ := h2
      have hpj : p = 2 * j ^ 2 := by ring_nf at hm; omega
      rcases Nat.prime_mul_iff.mp (hpj ▸ hp) with ⟨-, hj⟩ | ⟨h2, -⟩
      · rw [hj] at hpj; omega
      · exact not_prime_sq j h2
    · 
      exfalso
      have : p = m ^ 2 := by omega
      exact not_prime_sq m (this ▸ hp)
    · 
      have : p = 3 * k ^ 2 := by omega
      have h1 := Nat.prime_mul_iff.mp (this ▸ hp)
      rcases h1 with ⟨-, hk1⟩ | ⟨h3, -⟩
      · rw [hk1] at this; omega
      · exact absurd h3 (not_prime_sq k)
    · exfalso
      have : (2 * p) / 2 = p := by omega
      rw [this] at hxy
      exact sum_sq_mod_four x y (by omega)
variable {N : ℕ} (D : CongruentDissection N)
theorem notprime_of_baseangles (hright : tileγ D = Real.pi / 2)
    (hbase : (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) ∨
      (∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D ∧
        ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D))
    (hN2 : 2 < N) :
    ¬ N.Prime ∧ ∀ p : ℕ, p.Prime → p % 4 = 3 → N = 2 * p → N = 6 := by
  apply notprime_arith hN2
  rcases isosceles2_of_baseangles D hright hbase with ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨he, -, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨he, h⟩))
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
variable {N : ℕ} (D : CongruentDissection N)
theorem model_angleAt_0 : D.model.angleAt 0 = tileα D := rfl
theorem model_angleAt_2 : D.model.angleAt 2 = tileγ D := rfl
theorem target_angleAt_0 :
    D.target.angleAt 0 = ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) := rfl
theorem target_angleAt_2 :
    D.target.angleAt 2 = ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) :=
  angle_comm _ _ _
end TriangleTiling
end

section
namespace TriangleTiling
open Erdos634.Geometry EuclideanGeometry
variable {N : ℕ} (D : CongruentDissection N)
theorem relabel_angleAt (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelModel D τ).model.angleAt k = D.model.angleAt (τ k) :=
  (Row2.angleAt_comp D.model (relabelModel D τ).model τ (fun _ => rfl) k).1
end TriangleTiling
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
variable {α β a b c : ℝ}
theorem others (x y z : Fin 3) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (y = x + 1 ∧ z = x + 2) ∨ (y = x + 2 ∧ z = x + 1) := by
  revert x y z; decide
section Relation
variable (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h
end Relation
section TQ
variable (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hrel : 3 * α + 2 * β = Real.pi)
  (h : D.model.ThreeAlphaData α β a b c)
include hirr hrel h
end TQ
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
section Normalize
theorem relabel_angleAt (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (relabelTarget D σ).target.angleAt k = D.target.angleAt (σ k) := by
  have d1 : σ k ≠ σ (k + 1) := σ.injective.ne (fin3_ne_add_one k)
  have d2 : σ k ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x ≠ x + 2) k)
  have d12 : σ (k + 1) ≠ σ (k + 2) := σ.injective.ne ((by decide : ∀ x : Fin 3, x + 1 ≠ x + 2) k)
  show cornerAngle (D.target.pts (σ (k + 1))) (D.target.pts (σ k)) (D.target.pts (σ (k + 2))) = _
  unfold Tri.angleAt cornerAngle
  rcases others _ _ _ d1 d2 d12 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
  exact EuclideanGeometry.angle_comm _ _ _
end Normalize
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.Prime
open Erdos634.Geometry EuclideanGeometry
variable {N : ℕ}
theorem exists_perm_02 : ∀ i j : Fin 3, i ≠ j → ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 2 = j := by
  decide
end TriangleTiling.Prime
end


/-! ## Bridge: cut data (Mathlib triangles) to a Bonfioli congruent dissection -/

namespace OMA.E634S

open Erdos634.Geometry

abbrev Tr := Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))

/-- The Bonfioli triangle with the same vertices as a Mathlib triangle. -/
def ofS (s : Tr) : Tri := ⟨s.points, s.independent⟩

theorem carrier_ofS (s : Tr) : (ofS s).carrier = s.closedInterior := by
  simp [Tri.carrier, ofS]

/-- The vertices of a triangle in the plane, as an affine basis. -/
noncomputable def basisOf (s : Tr) : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)) :=
  ⟨s.points, s.independent,
    s.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)⟩

theorem basisOf_coe (s : Tr) : ⇑(basisOf s) = s.points := rfl

theorem interior_carrier_subset (s : Tr) : interior (ofS s).carrier ⊆ s.interior := by
  intro x hx
  have hx' : x ∈ interior (convexHull ℝ (Set.range (basisOf s))) := by
    rw [basisOf_coe]; exact hx
  rw [AffineBasis.interior_convexHull] at hx'
  have hpos : ∀ i, 0 < (basisOf s).coord i x := hx'
  have hsum : ∑ i, (basisOf s).coord i x = 1 := (basisOf s).sum_coord_apply_eq_one x
  have hx_eq : Finset.univ.affineCombination ℝ s.points (fun i => (basisOf s).coord i x) = x := by
    have := (basisOf s).affineCombination_coord_eq_self x
    rwa [basisOf_coe] at this
  rw [← hx_eq, Affine.Simplex.affineCombination_mem_interior_iff hsum]
  intro i
  refine ⟨hpos i, ?_⟩
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  rw [Fin.sum_univ_three] at hsum
  fin_cases i <;> simp <;> linarith

theorem congruent_of_cong {s t : Tr} (h : Congruent s.points t.points) : (ofS s).Congruent (ofS t) := by
  apply Erdos634.SssCongruent.congruent_of_dist
  intro i j
  have := h i j
  simp only [edist_dist] at this
  exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg dist_nonneg).mp this

/-- The congruent dissection built from cut data, with model the tile t. -/
noncomputable def mk {p : ℕ} (T : Tr) (Ts : Fin p → Tr)
    (hc : ∀ i j, Congruent (Ts i).points (Ts j).points)
    (hd : Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior))
    (hu : ⋃ i, (Ts i).closedInterior = T.closedInterior) (t : Fin p) : CongruentDissection p :=
  { target := ofS T
    tile := fun i => ofS (Ts i)
    covers := by simp only [carrier_ofS]; exact hu
    interiors_disjoint := fun i j hij =>
      (hd hij).mono (interior_carrier_subset _) (interior_carrier_subset _)
    model := ofS (Ts t)
    tiles_congruent := fun i => congruent_of_cong (hc i t) }

theorem target_angleAt {p : ℕ} (T : Tr) (Ts : Fin p → Tr)
    (hc : ∀ i j, Congruent (Ts i).points (Ts j).points)
    (hd : Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior))
    (hu : ⋃ i, (Ts i).closedInterior = T.closedInterior) (t : Fin p) (k : Fin 3) :
    (mk T Ts hc hd hu t).target.angleAt k =
      EuclideanGeometry.angle (T.points (k + 1)) (T.points k) (T.points (k + 2)) := rfl

theorem model_angleAt {p : ℕ} (T : Tr) (Ts : Fin p → Tr)
    (hc : ∀ i j, Congruent (Ts i).points (Ts j).points)
    (hd : Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior))
    (hu : ⋃ i, (Ts i).closedInterior = T.closedInterior) (t : Fin p) (k : Fin 3) :
    (mk T Ts hc hd hu t).model.angleAt k =
      EuclideanGeometry.angle ((Ts t).points (k + 1)) ((Ts t).points k) ((Ts t).points (k + 2)) := rfl

end OMA.E634S



/-- The RightRow case (Beeson-Rosu, TriangleTiling RightTile, notprime_of_baseangles): the tile has a
right angle and the two base angles of T equal another angle of the tile. -/
theorem OMA.solution : OMA.R_erdos_634_R1_H2_R1.H3 := by
  intro p hp hp3 T Ts hc hd hu t A B hA hB _ hrr
  obtain ⟨k, l, hlk, hk, i, j, hij, hi, hj⟩ := hrr
  let D := OMA.E634S.mk T Ts hc hd hu t
  have hAD : ∀ m, D.target.angleAt m = A m := fun m =>
    (OMA.E634S.target_angleAt T Ts hc hd hu t m).trans (hA m).symm
  have hBD : ∀ m, D.model.angleAt m = B m := fun m =>
    (OMA.E634S.model_angleAt T Ts hc hd hu t m).trans (hB m).symm
  obtain ⟨σ, hσ0, hσ2⟩ := TriangleTiling.Prime.exists_perm_02 i j hij
  obtain ⟨τ, hτ0, hτ2⟩ := TriangleTiling.Prime.exists_perm_02 l k hlk
  let D₁ := TriangleTiling.relabelTarget D σ
  let D₂ := TriangleTiling.relabelModel D₁ τ
  have hm : ∀ m, D₂.model.angleAt m = B (τ m) := fun m => by
    rw [TriangleTiling.relabel_angleAt]
    exact hBD (τ m)
  have ht : ∀ m, D₂.target.angleAt m = A (σ m) := fun m => by
    show D₁.target.angleAt m = A (σ m)
    rw [TriangleTiling.ThreeAlpha.relabel_angleAt]
    exact hAD (σ m)
  have hright : TriangleTiling.tileγ D₂ = Real.pi / 2 := by
    rw [← TriangleTiling.model_angleAt_2 (D := D₂), hm, hτ2, hk]
  refine (TriangleTiling.notprime_of_baseangles D₂ hright (Or.inr ⟨?_, ?_⟩) (by omega)).1 hp
  · rw [← TriangleTiling.target_angleAt_0 (D := D₂), ← TriangleTiling.model_angleAt_0 (D := D₂), ht, hm,
      hσ0, hτ0, hi]
  · rw [← TriangleTiling.target_angleAt_2 (D := D₂), ← TriangleTiling.model_angleAt_0 (D := D₂), ht, hm,
      hσ2, hτ0, hj]

