import OMAReductions.R_erdos_634_R1

/-!
# Erdos 634, step erdos-634.R1.H1 (big triangle similar to the tile)

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
theorem volume_ne_top (T : Tri) : volume T.carrier ≠ ⊤ := T.isCompact.measure_lt_top.ne
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
def Dir : Type := {v : Plane // ‖v‖ = 1}
def Dir.neg (d : Dir) : Dir := ⟨-d.1, by rw [norm_neg]; exact d.2⟩
theorem Dir.neg_involutive : Function.Involutive Dir.neg := by
  intro d; apply Subtype.ext; simp [Dir.neg]
noncomputable def Tri.leftUnit (T : Tri) (k : Fin 3) : Dir :=
  ⟨‖T.leftDir k‖⁻¹ • T.leftDir k, by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (T.leftDir_ne_zero k))⟩
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
noncomputable def Dissection.dirSet {N : ℕ} (D : Dissection N) (d : Dir) : Set Plane :=
  (⋃ i : Fin N, ⋃ k : Fin 3, ⋃ (_ : (D.tile i).leftUnit k = d), (D.tile i).edge k)
    ∩ interior D.target.carrier
theorem Dissection.mem_dirSet {N : ℕ} (D : Dissection N) (d : Dir) {x : Plane}
    (hx : x ∈ D.dirSet d) :
    ∃ i k, (D.tile i).leftUnit k = d ∧ x ∈ (D.tile i).edge k := by
  obtain ⟨hu, -⟩ := hx
  simp only [Set.mem_iUnion] at hu
  obtain ⟨i, k, hik, hmem⟩ := hu
  exact ⟨i, k, hik, hmem⟩
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
theorem Tri.onEdge_data (T : Tri) {k : Fin 3} {x : Plane} (hx : x ∈ T.edge k)
    (hxv : ∀ m, x ≠ T.pts m) :
    T.basis.coord (k + 2) x = 0 ∧ ∀ j, j ≠ k + 2 → 0 < T.basis.coord j x := by
  refine ⟨T.coord_eq_zero_of_mem_edge k hx, fun j hj => ?_⟩
  have hnn : 0 ≤ T.basis.coord j x := by
    have := T.edge_subset_carrier k hx
    rw [T.carrier_eq_nonneg_coord] at this; exact this j
  refine lt_of_le_of_ne hnn (Ne.symm fun hzero => ?_)
  obtain ⟨m, hm⟩ := T.eq_vertex_of_two_coords_zero hj hzero (T.coord_eq_zero_of_mem_edge k hx)
  exact hxv m hm
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
theorem unit_smul_of_neg {u v : Plane} {c : ℝ} (hc : c < 0) (hu : u ≠ 0) (hv : v = c • u) :
    ‖v‖⁻¹ • v = -(‖u‖⁻¹ • u) := by
  have hun : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hcne : c ≠ 0 := ne_of_lt hc
  have hune : ‖u‖ ≠ 0 := ne_of_gt hun
  subst hv
  have hnv : ‖c • u‖ = -c * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_neg hc]
  rw [hnv, smul_smul, ← neg_smul]
  congr 1
  field_simp
theorem Dissection.leftUnit_neg {N : ℕ} (D : Dissection N)
    {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂) {x : Plane} {m₁ m₂ : Fin 3}
    (hm₁ : (D.tile i₁).basis.coord m₁ x = 0)
    (ho₁ : ∀ j, j ≠ m₁ → 0 < (D.tile i₁).basis.coord j x)
    (hm₂ : (D.tile i₂).basis.coord m₂ x = 0)
    (ho₂ : ∀ j, j ≠ m₂ → 0 < (D.tile i₂).basis.coord j x) :
    (D.tile i₂).leftUnit (m₂ + 1) = Dir.neg ((D.tile i₁).leftUnit (m₁ + 1)) := by
  obtain ⟨c, hcneg, hc⟩ := D.leftDir_antiparallel hne hm₁ ho₁ hm₂ ho₂
  apply Subtype.ext
  simpa [Tri.leftUnit, Dir.neg] using
    unit_smul_of_neg hcneg ((D.tile i₁).leftDir_ne_zero (m₁ + 1)) hc
def Dissection.vertexSet {N : ℕ} (D : Dissection N) : Set Plane :=
  ⋃ i : Fin N, ⋃ k : Fin 3, {(D.tile i).pts k}
theorem Dissection.vertexSet_finite {N : ℕ} (D : Dissection N) : D.vertexSet.Finite :=
  Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _
theorem Dissection.notMem_vertexSet {N : ℕ} (D : Dissection N) {x : Plane}
    (hx : x ∉ D.vertexSet) : ∀ i k, x ≠ (D.tile i).pts k := by
  intro i k h
  exact hx (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨k, by simp [h]⟩⟩)
theorem Dissection.dirSet_sub {N : ℕ} (D : Dissection N) (hN : 0 < N) (d : Dir) :
    D.dirSet d \ D.vertexSet ⊆ D.dirSet (Dir.neg d) \ D.vertexSet := by
  rintro x ⟨hxd, hxv⟩
  refine ⟨?_, hxv⟩
  have hxint : x ∈ interior D.target.carrier := hxd.2
  obtain ⟨i₀, k₀, hk₀, hmem⟩ := D.mem_dirSet d hxd
  have hnv := D.notMem_vertexSet hxv
  obtain ⟨hz₀, hp₀⟩ := (D.tile i₀).onEdge_data hmem (hnv i₀)
  obtain ⟨R, hR, hRt⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
  have hRt' : Metric.ball x R ⊆ D.target.carrier := hRt.trans interior_subset
  obtain ⟨i₁, hne, hi₁⟩ := D.second_tile_at_edge_point hN hnv hR hRt' ⟨k₀ + 2, hz₀, hp₀⟩
  obtain ⟨m₁, hz₁, hp₁⟩ := hi₁
  have hkey := D.leftUnit_neg (Ne.symm hne) hz₀ hp₀ hz₁ hp₁
  have hshift : (k₀ + 2 + 1 : Fin 3) = k₀ := by fin_cases k₀ <;> rfl
  rw [hshift, hk₀] at hkey
  refine ⟨?_, hxint⟩
  exact Set.mem_iUnion.mpr ⟨i₁, Set.mem_iUnion.mpr ⟨m₁ + 1, Set.mem_iUnion.mpr
    ⟨hkey, (D.tile i₁).mem_edge_of_coord_zero hz₁ hp₁⟩⟩⟩
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
theorem Tri.det_pos_or_neg (T : Tri) : 0 < T.det ∨ T.det < 0 :=
  (lt_or_gt_of_ne T.det_ne_zero).symm
noncomputable def Tri.relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : Tri where
  pts := T.pts ∘ τ
  indep := T.indep.comp_embedding τ.toEmbedding
theorem Tri.relabel_pts (T : Tri) (τ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.relabel τ).pts k = T.pts (τ k) := rfl
theorem Tri.congruent_relabel (T : Tri) (τ : Equiv.Perm (Fin 3)) : T.Congruent (T.relabel τ) := by
  refine ⟨IsometryEquiv.refl Plane, τ.symm, fun k => ?_⟩
  show T.pts k = (T.relabel τ).pts (τ.symm k)
  simp [Tri.relabel_pts]
theorem Tri.Congruent.relabel {T U : Tri} (h : T.Congruent U) (τ : Equiv.Perm (Fin 3)) :
    T.Congruent (U.relabel τ) :=
  h.trans (U.congruent_relabel τ)
structure CongruentDissection (N : ℕ) extends Dissection N where
  model : Tri
  tiles_congruent : ∀ i, (tile i).Congruent model
namespace CongruentDissection
variable {N : ℕ}
noncomputable def relabelModel (D : CongruentDissection N) (τ : Equiv.Perm (Fin 3)) :
    CongruentDissection N where
  toDissection := D.toDissection
  model := D.model.relabel τ
  tiles_congruent := fun i => (D.tiles_congruent i).relabel τ
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
end Erdos634.AreaDet
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
theorem congruent_edge_lengths {T U : Tri} (h : T.Congruent U) (j j' : Fin 3) (hjj : j ≠ j') :
    ∃ i i' : Fin 3, i ≠ i' ∧ dist (U.pts j) (U.pts j') = dist (T.pts i) (T.pts i') := by
  obtain ⟨σ, hd⟩ := h.dist_eq
  refine ⟨σ.symm j, σ.symm j', fun hh => hjj (σ.symm.injective hh), ?_⟩
  have := hd (σ.symm j) (σ.symm j')
  simpa using this.symm
end Erdos634.Geometry
end

section
namespace Erdos634.PinPlumbing
open Erdos634.Geometry
theorem pin_angle_sum {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts) :
    ∑ i, (D.tile i).localAngle p = Real.pi := by
  rw [D.sum_localAngle_eq p, D.target.localAngle_frontier hp hv]
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
theorem no_interior_tile_at_pin {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ frontier D.target.carrier) (hv : p ∉ Set.range D.target.pts)
    (i : Fin N) (hi : (D.tile i).localAngle p = 2 * Real.pi) : False := by
  have hsum := pin_angle_sum D hp hv
  have hle : (D.tile i).localAngle p ≤ ∑ j, (D.tile j).localAngle p :=
    Finset.single_le_sum (fun j _ => (D.tile j).localAngle_nonneg p) (Finset.mem_univ i)
  rw [hsum, hi] at hle
  nlinarith [Real.pi_pos]
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
end Erdos634.BaseSelection
end

section
open scoped Classical
namespace Erdos634.Geometry
open MeasureTheory Set
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
noncomputable def Tri.flux (T : Tri) (f : Dir → E) : E :=
  ∑ k : Fin 3, dist (T.pts k) (T.pts (k + 1)) • f (T.leftUnit k)
theorem Dir.neg_ne_self (d : Dir) : Dir.neg d ≠ d := by
  intro h
  have h1 : -d.1 = d.1 := congrArg Subtype.val h
  have h2 : (2:ℝ) • d.1 = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h1]
    exact neg_add_cancel _
  have h3 : d.1 = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact h
  have h4 := d.2
  rw [h3, norm_zero] at h4
  norm_num at h4
namespace Dissection
noncomputable def eLen (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))
noncomputable def eDir (D : Dissection N) (e : Fin N × Fin 3) : Dir := (D.tile e.1).leftUnit e.2
def eSet (D : Dissection N) (e : Fin N × Fin 3) : Set Plane := (D.tile e.1).edge e.2
noncomputable def sideEdges (D : Dissection N) (j : Fin 3) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => D.eSet e ⊆ D.target.edge j
noncomputable def intEdges (D : Dissection N) : Finset (Fin N × Fin 3) :=
  Finset.univ.filter fun e => ∀ j, ¬ D.eSet e ⊆ D.target.edge j
theorem flux_sum_eq (D : Dissection N) (f : Dir → E) :
    ∑ i, (D.tile i).flux f = ∑ e : Fin N × Fin 3, D.eLen e • f (D.eDir e) := by
  rw [Fintype.sum_prod_type]
  rfl
end Dissection
theorem Tri.notMem_interior_of_mem_edge (T : Tri) {j : Fin 3} {x : Plane}
    (hx : x ∈ T.edge j) : x ∉ interior T.carrier := by
  intro hint
  have h0 := T.coord_eq_zero_of_mem_edge j hx
  have hpos := T.interior_coord_pos hint (j + 2)
  rw [h0] at hpos
  exact lt_irrefl _ hpos
theorem Tri.coord_zero_mem_segment' (T : Tri) (k : Fin 3) (x : Plane)
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
theorem Tri.mem_edge_of_coord_zero_nonneg (T : Tri) {m : Fin 3} {x : Plane}
    (h0 : T.basis.coord m x = 0) (hnn : ∀ j, 0 ≤ T.basis.coord j x) :
    x ∈ T.edge (m + 1) := by
  have h := T.coord_zero_mem_segment' m x h0 hnn
  have hidx : m + 1 + 1 = m + 2 := by fin_cases m <;> rfl
  rw [Tri.edge, hidx]
  exact h
theorem Dissection.edge_interior_or_side (D : Dissection N) (e : Fin N × Fin 3) {x : Plane}
    (hx : x ∈ D.eSet e) (hx1 : x ≠ (D.tile e.1).pts e.2) (hx2 : x ≠ (D.tile e.1).pts (e.2 + 1)) :
    x ∈ interior D.target.carrier ∨ ∃ j, D.eSet e ⊆ D.target.edge j := by
  by_cases hint : x ∈ interior D.target.carrier
  · exact Or.inl hint
  right
  have hnnT : ∀ y ∈ (D.tile e.1).carrier, ∀ i, 0 ≤ D.target.basis.coord i y := by
    intro y hy i
    have := tile_subset_target D e.1 hy
    rw [D.target.carrier_eq_nonneg_coord] at this
    exact this i
  have haT : (D.tile e.1).pts e.2 ∈ (D.tile e.1).carrier := subset_convexHull ℝ _ ⟨e.2, rfl⟩
  have hbT : (D.tile e.1).pts (e.2 + 1) ∈ (D.tile e.1).carrier :=
    subset_convexHull ℝ _ ⟨e.2 + 1, rfl⟩
  have hxT : x ∈ (D.tile e.1).carrier := (D.tile e.1).edge_subset_carrier e.2 hx
  obtain ⟨m, hm⟩ : ∃ m, D.target.basis.coord m x = 0 := by
    by_contra hcon
    push Not at hcon
    apply hint
    have hpos : ∀ i, 0 < D.target.basis.coord i x := fun i =>
      lt_of_le_of_ne (hnnT x hxT i) (Ne.symm (hcon i))
    obtain ⟨r, hr, hsub⟩ := D.target.ball_subset_of_pos hpos
    exact mem_interior.mpr ⟨Metric.ball x r, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
  have hx' : x ∈ segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) := hx
  obtain ⟨s, t, hs, ht, hst, hxst⟩ := hx'
  have hspos : 0 < s := by
    rcases hs.lt_or_eq with h | h
    · exact h
    · exfalso; apply hx2
      have ht1 : t = 1 := by linarith
      rw [← hxst, ← h, ht1, zero_smul, one_smul, zero_add]
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h | h
    · exact h
    · exfalso; apply hx1
      have hs1 : s = 1 := by linarith
      rw [← hxst, ← h, hs1, zero_smul, one_smul, add_zero]
  have hcomb : D.target.basis.coord m x
      = s * D.target.basis.coord m ((D.tile e.1).pts e.2)
        + t * D.target.basis.coord m ((D.tile e.1).pts (e.2 + 1)) := by
    rw [← hxst, Convex.combo_affine_apply hst, smul_eq_mul, smul_eq_mul]
  have hga := hnnT _ haT m
  have hgb := hnnT _ hbT m
  have h1 : 0 ≤ s * D.target.basis.coord m ((D.tile e.1).pts e.2) := mul_nonneg hs hga
  have h2 : 0 ≤ t * D.target.basis.coord m ((D.tile e.1).pts (e.2 + 1)) := mul_nonneg ht hgb
  have h3 : s * D.target.basis.coord m ((D.tile e.1).pts e.2) = 0 := by linarith
  have h4 : t * D.target.basis.coord m ((D.tile e.1).pts (e.2 + 1)) = 0 := by linarith
  have hza := (mul_eq_zero.mp h3).resolve_left hspos.ne'
  have hzb := (mul_eq_zero.mp h4).resolve_left htpos.ne'
  have haE := D.target.mem_edge_of_coord_zero_nonneg hza (hnnT _ haT)
  have hbE := D.target.mem_edge_of_coord_zero_nonneg hzb (hnnT _ hbT)
  exact ⟨m + 1, (convex_segment _ _).segment_subset haE hbE⟩
theorem Dissection.mem_interior_of_mem_intEdges (D : Dissection N) {e : Fin N × Fin 3}
    (he : e ∈ D.intEdges) {x : Plane} (hx : x ∈ D.eSet e)
    (hx1 : x ≠ (D.tile e.1).pts e.2) (hx2 : x ≠ (D.tile e.1).pts (e.2 + 1)) :
    x ∈ interior D.target.carrier := by
  rcases D.edge_interior_or_side e hx hx1 hx2 with h | ⟨j, hj⟩
  · exact h
  · unfold Dissection.intEdges at he
    exact absurd hj ((Finset.mem_filter.mp he).2 j)
theorem Dissection.mem_intEdges_of_interior (D : Dissection N) {e : Fin N × Fin 3} {x : Plane}
    (hx : x ∈ D.eSet e) (hxi : x ∈ interior D.target.carrier) : e ∈ D.intEdges := by
  unfold Dissection.intEdges
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, fun j hj => D.target.notMem_interior_of_mem_edge (hj hx) hxi⟩
theorem Tri.edge_inter_edge_subsingleton (T : Tri) {j j' : Fin 3} (h : j ≠ j') :
    (T.edge j ∩ T.edge j').Subsingleton := by
  have h2 : j + 2 ≠ j' + 2 := fun h' => h (add_right_cancel h')
  have key : ∀ y ∈ T.edge j ∩ T.edge j', ∃ m, y = T.pts m ∧ m ≠ j + 2 ∧ m ≠ j' + 2 := by
    rintro y ⟨hy, hy'⟩
    have hz := T.coord_eq_zero_of_mem_edge j hy
    have hz' := T.coord_eq_zero_of_mem_edge j' hy'
    obtain ⟨m, rfl⟩ := T.eq_vertex_of_two_coords_zero h2 hz hz'
    have e1 : T.basis.coord m (T.pts m) = 1 := T.basis.coord_apply_eq m
    refine ⟨m, rfl, ?_, ?_⟩
    · intro hm; rw [← hm, e1] at hz; exact one_ne_zero hz
    · intro hm; rw [← hm, e1] at hz'; exact one_ne_zero hz'
  intro y hy z hz
  obtain ⟨m, rfl, hm1, hm2⟩ := key y hy
  obtain ⟨m', rfl, hm1', hm2'⟩ := key z hz
  have hall : ∀ a b c d : Fin 3, a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c = d := by decide
  rw [hall _ _ _ _ h2 hm1 hm2 hm1' hm2']
theorem Dissection.sideEdges_disjoint (D : Dissection N) {j j' : Fin 3} (h : j ≠ j') :
    Disjoint (D.sideEdges j) (D.sideEdges j') := by
  rw [Finset.disjoint_left]
  intro e he he'
  unfold Dissection.sideEdges at he he'
  have hj := (Finset.mem_filter.mp he).2
  have hj' := (Finset.mem_filter.mp he').2
  have ha : (D.tile e.1).pts e.2 ∈ D.eSet e := left_mem_segment ℝ _ _
  have hb : (D.tile e.1).pts (e.2 + 1) ∈ D.eSet e := right_mem_segment ℝ _ _
  have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hne : (D.tile e.1).pts e.2 ≠ (D.tile e.1).pts (e.2 + 1) := fun hh =>
    hsucc e.2 ((D.tile e.1).indep.injective hh)
  exact hne (D.target.edge_inter_edge_subsingleton h ⟨hj ha, hj' ha⟩ ⟨hj hb, hj' hb⟩)
theorem Dissection.sum_split (D : Dissection N) (g : Fin N × Fin 3 → E) :
    ∑ e, g e = ∑ e ∈ D.intEdges, g e + ∑ j : Fin 3, ∑ e ∈ D.sideEdges j, g e := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 3))) D.sideEdges :=
    fun j _ j' _ hjj' => D.sideEdges_disjoint hjj'
  rw [← Finset.sum_biUnion hdisj]
  have hunion : D.intEdges ∪ (Finset.univ : Finset (Fin 3)).biUnion D.sideEdges
      = Finset.univ := by
    ext e
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true,
      Dissection.intEdges, Dissection.sideEdges, Finset.mem_filter]
    by_cases h : ∀ j, ¬ D.eSet e ⊆ D.target.edge j
    · exact Or.inl h
    · push Not at h; exact Or.inr h
  have hdis2 : Disjoint D.intEdges ((Finset.univ : Finset (Fin 3)).biUnion D.sideEdges) := by
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Dissection.sideEdges,
      Finset.mem_filter] at he'
    simp only [Dissection.intEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    obtain ⟨j, hj⟩ := he'
    exact he j hj
  rw [← Finset.sum_union hdis2, hunion]
theorem Dissection.sameDir_subsingleton (D : Dissection N) {e₁ e₂ : Fin N × Fin 3}
    (hne : e₁ ≠ e₂) (hdir : D.eDir e₁ = D.eDir e₂) :
    (D.eSet e₁ ∩ D.eSet e₂).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨hm1, hn1A, hn1B⟩ := mem_ne_ends_of_avg hpq hp.1 hq.1
  obtain ⟨hm2, hn2A, hn2B⟩ := mem_ne_ends_of_avg hpq hp.2 hq.2
  obtain ⟨hz₁, hp₁⟩ := (D.tile e₁.1).onEdge_param (k := e₁.2) hm1 hn1A hn1B
  obtain ⟨hz₂, hp₂⟩ := (D.tile e₂.1).onEdge_param (k := e₂.2) hm2 hn2A hn2B
  have hshift : ∀ k : Fin 3, k + 2 + 1 = k := by decide
  by_cases hsame : e₁.1 = e₂.1
  · have hk : e₁.2 ≠ e₂.2 := fun h => hne (Prod.ext hsame h)
    have hk2 : e₁.2 + 2 ≠ e₂.2 + 2 := fun h => hk (add_right_cancel h)
    rw [hsame] at hz₁
    exact absurd hz₁ (ne_of_gt (hp₂ _ hk2))
  · have hkey := D.leftUnit_neg hsame hz₁ hp₁ hz₂ hp₂
    simp only [hshift] at hkey
    exact Dir.neg_ne_self _ (hkey.symm.trans hdir.symm)
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open MeasureTheory Set
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
theorem unit_smul_of_pos {u v : Plane} {c : ℝ} (hc : 0 < c) (hu : u ≠ 0) (hv : v = c • u) :
    ‖v‖⁻¹ • v = ‖u‖⁻¹ • u := by
  have hun : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hcne : c ≠ 0 := ne_of_gt hc
  have hune : ‖u‖ ≠ 0 := ne_of_gt hun
  subst hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
  congr 1
  field_simp
theorem Dissection.eDir_of_side (D : Dissection N) {e : Fin N × Fin 3} {j : Fin 3}
    (h : D.eSet e ⊆ D.target.edge j) : D.eDir e = D.target.leftUnit j := by
  have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
  have hshift : ∀ i : Fin 3, i + 2 + 1 = i := by decide
  have hab : (D.tile e.1).pts e.2 ≠ (D.tile e.1).pts (e.2 + 1) := fun hh =>
    hsucc e.2 ((D.tile e.1).indep.injective hh)
  have ha : (D.tile e.1).pts e.2 ∈ (D.tile e.1).edge e.2 := left_mem_segment ℝ _ _
  have hb : (D.tile e.1).pts (e.2 + 1) ∈ (D.tile e.1).edge e.2 := right_mem_segment ℝ _ _
  obtain ⟨hxT, hxa, hxb⟩ := mem_ne_ends_of_avg hab ha hb
  obtain ⟨hzT, hpT⟩ := (D.tile e.1).onEdge_param (k := e.2) hxT hxa hxb
  have haS : (D.tile e.1).pts e.2 ∈ D.target.edge j := h ha
  have hbS : (D.tile e.1).pts (e.2 + 1) ∈ D.target.edge j := h hb
  obtain ⟨hxS, hxA, hxB⟩ := mem_ne_ends_of_avg hab haS hbS
  obtain ⟨hzS, hpS⟩ := D.target.onEdge_param (k := j) hxS hxA hxB
  obtain ⟨g, c, hg, hle, hj, hj1, hj2⟩ := exists_supporting D.target j
  have hgx : g (((1:ℝ)/2) • (D.tile e.1).pts e.2 + ((1:ℝ)/2) • (D.tile e.1).pts (e.2 + 1))
      = c := by
    have hS := target_contact_side D.target g c hle hj hj1 hj2
    have hmem : ((1:ℝ)/2) • (D.tile e.1).pts e.2 + ((1:ℝ)/2) • (D.tile e.1).pts (e.2 + 1)
        ∈ {y ∈ D.target.carrier | g y = c} := by
      rw [hS]; exact hxS
    exact hmem.2
  have hleT : ∀ y ∈ (D.tile e.1).carrier, g y ≤ c := fun y hy =>
    hle y (tile_subset_target D e.1 hy)
  have hinT : ∀ v, g v < 0 → 0 < cross ((D.tile e.1).leftDir e.2) v := by
    intro v hv
    have := (D.tile e.1).edge_inward g c hg hleT hzT hpT hgx hv
    rwa [hshift] at this
  have hinS : ∀ v, g v < 0 → 0 < cross (D.target.leftDir j) v := by
    intro v hv
    have := D.target.edge_inward g c hg hle hzS hpS hgx hv
    rwa [hshift] at this
  have hnegcross : ∀ w v : Plane, cross w (-v) = - cross w v := by
    intro w v; simp only [cross, PiLp.neg_apply]; ring
  have hdisjT : ∀ v, ¬ (0 < crossL ((D.tile e.1).leftDir e.2) v ∧ 0 < g v) := by
    rintro v ⟨h1, h2⟩
    have h3 := hinT (-v) (by rw [map_neg]; linarith)
    rw [crossL_apply] at h1
    rw [hnegcross] at h3
    linarith
  have hdisjS : ∀ v, ¬ (0 < crossL (D.target.leftDir j) v ∧ 0 < g v) := by
    rintro v ⟨h1, h2⟩
    have h3 := hinS (-v) (by rw [map_neg]; linarith)
    rw [crossL_apply] at h1
    rw [hnegcross] at h3
    linarith
  obtain ⟨c₁, hc₁, hgT⟩ := proportional_of_disjoint_pos (crossL ((D.tile e.1).leftDir e.2)) g
    (crossL_ne_zero ((D.tile e.1).leftDir_ne_zero e.2)) hg hdisjT
  obtain ⟨c₂, hc₂, hgS⟩ := proportional_of_disjoint_pos (crossL (D.target.leftDir j)) g
    (crossL_ne_zero (D.target.leftDir_ne_zero j)) hg hdisjS
  have hc₂ne : c₂ ≠ 0 := ne_of_lt hc₂
  have hprop : D.target.leftDir j = (c₁ / c₂) • (D.tile e.1).leftDir e.2 := by
    have hzero : ∀ v, cross (D.target.leftDir j - (c₁ / c₂) • (D.tile e.1).leftDir e.2) v = 0 := by
      intro v
      have e1 := hgT v
      have e2 := hgS v
      rw [crossL_apply] at e1 e2
      have hrel : cross (D.target.leftDir j) v = (c₁ / c₂) * cross ((D.tile e.1).leftDir e.2) v := by
        rw [div_mul_eq_mul_div, eq_div_iff hc₂ne]
        linear_combination e1 - e2
      simp only [cross, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at hrel ⊢
      linear_combination hrel
    exact sub_eq_zero.mp (eq_zero_of_cross_eq_zero hzero)
  have hpos : 0 < c₁ / c₂ := div_pos_of_neg_of_neg hc₁ hc₂
  have hunit := unit_smul_of_pos hpos ((D.tile e.1).leftDir_ne_zero e.2) hprop
  apply Subtype.ext
  show ‖(D.tile e.1).leftDir e.2‖⁻¹ • (D.tile e.1).leftDir e.2
    = ‖D.target.leftDir j‖⁻¹ • D.target.leftDir j
  exact hunit.symm
theorem Dissection.side_len_sum (D : Dissection N) (j : Fin 3) :
    ∑ e ∈ D.sideEdges j, D.eLen e = dist (D.target.pts j) (D.target.pts (j + 1)) := by
  obtain ⟨g, c, hg, hle, hj, hj1, hj2⟩ := exists_supporting D.target j
  have hS : {x ∈ D.target.carrier | g x = c} = D.target.edge j :=
    target_contact_side D.target g c hle hj hj1 hj2
  have hmemS : ∀ e ∈ D.sideEdges j, D.eSet e ⊆ D.target.edge j := fun e he => by
    unfold Dissection.sideEdges at he
    exact (Finset.mem_filter.mp he).2
  have hon : ∀ e ∈ D.sideEdges j, ∀ y ∈ (D.tile e.1).edge e.2, g y = c := by
    intro e he y hy
    have hy' : y ∈ {x ∈ D.target.carrier | g x = c} := by rw [hS]; exact hmemS e he hy
    exact hy'.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, g y ≤ c :=
    fun e y hy => hle y (tile_subset_target D e.1 hy)
  have hcov : D.target.edge j \ ∅ ⊆ ⋃ e ∈ D.sideEdges j, D.eSet e := by
    rintro y ⟨hy, -⟩
    obtain ⟨part, hpart⟩ := hasEdgeChains_edge D j
    have hy' := (Set.ext_iff.mp hpart y).mpr hy
    obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy'
    refine Set.mem_iUnion₂.mpr ⟨e, ?_, hye⟩
    unfold Dissection.sideEdges
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun z hz => ?_⟩
    exact (Set.ext_iff.mp hpart z).mp (Set.mem_iUnion₂.mpr ⟨e, he, hz⟩)
  have hsum := sum_hausdorff_of_partition (D.sideEdges j) D.eSet (D.target.edge j) ∅
    Set.finite_empty
    (fun e _ => ((D.tile e.1).isClosed_edge e.2).measurableSet)
    (fun e₁ h₁ e₂ h₂ hne => D.sameside_edges_subsingleton g c hg hne (hleT e₁) (hleT e₂)
      (hon e₁ h₁) (hon e₂ h₂))
    hmemS hcov
  have hfin : ∀ e ∈ D.sideEdges j,
      (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e) ≠ ⊤ := by
    intro e _
    rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge]
    exact edist_ne_top _ _
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_sum hfin, Tri.hausdorff_edge, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg] at hreal
  rw [← hreal]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]
  rfl
theorem Dissection.side_flux (D : Dissection N) (f : Dir → E) :
    ∑ j : Fin 3, ∑ e ∈ D.sideEdges j, D.eLen e • f (D.eDir e) = D.target.flux f := by
  unfold Tri.flux
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∑ e ∈ D.sideEdges j, D.eLen e • f (D.eDir e)
      = ∑ e ∈ D.sideEdges j, D.eLen e • f (D.target.leftUnit j) := by
    refine Finset.sum_congr rfl fun e he => ?_
    unfold Dissection.sideEdges at he
    rw [D.eDir_of_side (Finset.mem_filter.mp he).2]
  rw [h1, ← Finset.sum_smul, D.side_len_sum j]
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
noncomputable def toC : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
theorem toC_apply (v : Plane) : toC v = (v 0 : ℂ) + (v 1 : ℂ) * Complex.I :=
  Complex.orthonormalBasisOneI_repr_symm_apply v
theorem toC_re (v : Plane) : (toC v).re = v 0 := by simp [toC_apply]
theorem toC_im (v : Plane) : (toC v).im = v 1 := by simp [toC_apply]
theorem toC_ne_zero {v : Plane} (hv : v ≠ 0) : toC v ≠ 0 := by
  intro h
  apply hv
  exact toC.injective (h.trans (map_zero toC).symm)
theorem toC_div_im (u v : Plane) :
    (toC v / toC u).im = cross u v / Complex.normSq (toC u) := by
  rw [Complex.div_im, toC_re, toC_re, toC_im, toC_im]
  unfold cross
  ring
theorem arg_turn {u v : Plane} (hu : u ≠ 0) (hv : v ≠ 0) (hc : 0 < cross u v) :
    ((Complex.arg (toC v) : ℝ) : Real.Angle)
      = (Complex.arg (toC u) : Real.Angle)
        + ((InnerProductGeometry.angle u v : ℝ) : Real.Angle) := by
  have hu' := toC_ne_zero hu
  have hv' := toC_ne_zero hv
  have him : 0 ≤ (toC v / toC u).im := by
    rw [toC_div_im]
    exact div_nonneg hc.le (Complex.normSq_nonneg _)
  have h1 : InnerProductGeometry.angle (toC u) (toC v) = InnerProductGeometry.angle u v :=
    toC.toLinearIsometry.angle_map u v
  have hang : InnerProductGeometry.angle u v = Complex.arg (toC v / toC u) := by
    rw [← h1, InnerProductGeometry.angle_comm, Complex.angle_eq_abs_arg hv' hu',
      abs_of_nonneg (Complex.arg_nonneg_iff.mpr him)]
  rw [hang, Complex.arg_div_coe_angle hv' hu']
  abel
noncomputable def Dir.angle (d : Dir) : Real.Angle := (Complex.arg (toC d.1) : Real.Angle)
theorem Dir.ne_zero (d : Dir) : d.1 ≠ 0 := by
  intro h
  have h2 := d.2
  rw [h, norm_zero] at h2
  norm_num at h2
theorem Dir.angle_neg (d : Dir) :
    (Dir.neg d).angle = d.angle + ((Real.pi : ℝ) : Real.Angle) := by
  unfold Dir.angle
  have h : toC (Dir.neg d).1 = - toC d.1 := map_neg toC d.1
  rw [h, Complex.arg_neg_coe_angle (toC_ne_zero d.ne_zero)]
theorem Tri.leftUnit_angle (T : Tri) (k : Fin 3) :
    (T.leftUnit k).angle = (Complex.arg (toC (T.leftDir k)) : Real.Angle) := by
  unfold Dir.angle
  show ((Complex.arg (toC (‖T.leftDir k‖⁻¹ • T.leftDir k)) : ℝ) : Real.Angle) = _
  rw [map_smul, Complex.real_smul,
    Complex.arg_real_mul _ (inv_pos.mpr (norm_pos_iff.mpr (T.leftDir_ne_zero k)))]
noncomputable def Tri.angleAt (T : Tri) (k : Fin 3) : ℝ :=
  cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
noncomputable def Tri.oppLen (T : Tri) (k : Fin 3) : ℝ := dist (T.pts (k + 1)) (T.pts (k + 2))
theorem Tri.angleAt_sum (T : Tri) : T.angleAt 0 + T.angleAt 1 + T.angleAt 2 = Real.pi := by
  have h := cornerAngle_sum T
  unfold Tri.angleAt
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  exact h
theorem Tri.pi_sub_angleAt (T : Tri) (k : Fin 3) :
    Real.pi - T.angleAt (k + 1)
      = InnerProductGeometry.angle (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts (k + 1)) := by
  have h1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have h2 : k + 1 + 2 = k := by fin_cases k <;> rfl
  unfold Tri.angleAt cornerAngle EuclideanGeometry.angle
  rw [h1, h2]
  simp only [vsub_eq_sub]
  rw [InnerProductGeometry.angle_comm,
    show T.pts k - T.pts (k + 1) = -(T.pts (k + 1) - T.pts k) by abel,
    InnerProductGeometry.angle_neg_left]
  ring
theorem Tri.cross_consecutive (T : Tri) (k : Fin 3) :
    cross (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts (k + 1)) = T.det := by
  have h := T.det_cyclic k
  have e : T.pts (k + 2) - T.pts (k + 1) = (T.pts (k + 2) - T.pts k) - (T.pts (k + 1) - T.pts k) := by
    abel
  rw [e, cross_sub_right, h, cross_self, sub_zero]
theorem Tri.leftUnit_turn_of_pos (T : Tri) (hT : 0 < T.det) (k : Fin 3) :
    (T.leftUnit (k + 1)).angle
      = (T.leftUnit k).angle + ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) := by
  have h1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have hk : T.leftDir k = T.pts (k + 1) - T.pts k := by unfold Tri.leftDir; rw [if_pos hT]
  have hk1 : T.leftDir (k + 1) = T.pts (k + 2) - T.pts (k + 1) := by
    unfold Tri.leftDir; rw [if_pos hT, h1]
  rw [Tri.leftUnit_angle, Tri.leftUnit_angle, T.pi_sub_angleAt k, hk, hk1]
  refine arg_turn ?_ ?_ ?_
  · rw [← hk]; exact T.leftDir_ne_zero k
  · rw [← hk1]; exact T.leftDir_ne_zero (k + 1)
  · rw [T.cross_consecutive k]; exact hT
theorem Tri.leftUnit_turn_of_neg (T : Tri) (hT : T.det < 0) (k : Fin 3) :
    (T.leftUnit k).angle
      = (T.leftUnit (k + 1)).angle + ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) := by
  have h1 : k + 1 + 1 = k + 2 := by fin_cases k <;> rfl
  have hn : ¬ 0 < T.det := not_lt.mpr hT.le
  have hk : T.leftDir k = -(T.pts (k + 1) - T.pts k) := by
    unfold Tri.leftDir; rw [if_neg hn]; abel
  have hk1 : T.leftDir (k + 1) = -(T.pts (k + 2) - T.pts (k + 1)) := by
    unfold Tri.leftDir; rw [if_neg hn, h1]; abel
  have hang : InnerProductGeometry.angle (T.pts (k + 1) - T.pts k) (T.pts (k + 2) - T.pts (k + 1))
      = InnerProductGeometry.angle (-(T.pts (k + 2) - T.pts (k + 1))) (-(T.pts (k + 1) - T.pts k)) := by
    rw [InnerProductGeometry.angle_neg_neg, InnerProductGeometry.angle_comm]
  rw [Tri.leftUnit_angle, Tri.leftUnit_angle, T.pi_sub_angleAt k, hk, hk1, hang]
  refine arg_turn ?_ ?_ ?_
  · rw [← hk1]; exact T.leftDir_ne_zero (k + 1)
  · rw [← hk]; exact T.leftDir_ne_zero k
  · have hc := T.cross_consecutive k
    simp only [cross, PiLp.neg_apply] at hc ⊢
    linarith
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
noncomputable def chi (θ : Real.Angle) : R := if h : θ ∈ G.L then G.ψ ⟨θ, h⟩ else 0
theorem chi_of_mem {θ : Real.Angle} (h : θ ∈ G.L) : G.chi θ = G.ψ ⟨θ, h⟩ := dif_pos h
theorem chi_add {l l' : Real.Angle} (hl : l ∈ G.L) (hl' : l' ∈ G.L) :
    G.chi (l + l') = G.chi l * G.chi l' := by
  rw [G.chi_of_mem (G.L.add_mem hl hl'), G.chi_of_mem hl, G.chi_of_mem hl']
  exact AddChar.map_add_eq_mul G.ψ ⟨l, hl⟩ ⟨l', hl'⟩
theorem chi_zero : G.chi 0 = 1 := by
  rw [G.chi_of_mem G.L.zero_mem]
  exact AddChar.map_zero_eq_one G.ψ
theorem chi_pi : G.chi ((Real.pi : ℝ) : Real.Angle) = -1 := by
  rw [G.chi_of_mem G.pi_mem]
  exact G.ψ_pi
noncomputable def rep (θ : Real.Angle) : Real.Angle :=
  if θ - G.anchor ∈ G.L then G.anchor else (QuotientAddGroup.mk θ : Real.Angle ⧸ G.L).out
theorem sub_rep_mem (θ : Real.Angle) : θ - G.rep θ ∈ G.L := by
  unfold rep
  split_ifs with h
  · exact h
  · obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_mul G.L θ
    rw [hl, show θ - (θ + (l : Real.Angle)) = -(l : Real.Angle) by abel]
    exact G.L.neg_mem l.2
theorem rep_add (θ : Real.Angle) {l : Real.Angle} (hl : l ∈ G.L) : G.rep (θ + l) = G.rep θ := by
  unfold rep
  have hiff : (θ + l - G.anchor ∈ G.L) ↔ (θ - G.anchor ∈ G.L) := by
    rw [show θ + l - G.anchor = (θ - G.anchor) + l by abel]
    exact G.L.add_mem_cancel_right hl
  have hmk : (QuotientAddGroup.mk (θ + l) : Real.Angle ⧸ G.L) = QuotientAddGroup.mk θ :=
    QuotientAddGroup.mk_add_of_mem θ hl
  by_cases h : θ - G.anchor ∈ G.L
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, hmk]
noncomputable def val (θ : Real.Angle) : R := G.chi (θ - G.rep θ)
theorem val_add (θ : Real.Angle) {l : Real.Angle} (hl : l ∈ G.L) :
    G.val (θ + l) = G.chi l * G.val θ := by
  unfold val
  rw [G.rep_add θ hl, show θ + l - G.rep θ = (θ - G.rep θ) + l by abel,
    G.chi_add (G.sub_rep_mem θ) hl, mul_comm]
noncomputable def weight (d : Dir) : R := G.val d.angle
theorem weight_odd (d : Dir) : G.weight (Dir.neg d) = - G.weight d := by
  unfold weight
  rw [Dir.angle_neg, G.val_add _ G.pi_mem, G.chi_pi, neg_one_mul]
theorem val_sq (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (θ : Real.Angle) :
    G.val θ * G.val θ = 1 :=
  hsq _ (G.sub_rep_mem θ)
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
theorem GridChar.ofHom_chi {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hχ : χ a₀ = 1) (anchor : Real.Angle) (a : A) :
    (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).chi (φ a) = if χ a = 0 then 1 else -1 := by
  rw [GridChar.chi_of_mem _ (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)]
  show signChar (rangeChar φ χ hker) ⟨φ a, _⟩ = _
  rw [signChar_apply, rangeChar_apply]
theorem GridChar.ofHom_sq {A : Type*} [AddCommGroup A] (φ : A →+ Real.Angle)
    (χ : A →+ ZMod 2) (hker : ∀ a, φ a = 0 → χ a = 0) (a₀ : A)
    (hπ : φ a₀ = ((Real.pi : ℝ) : Real.Angle)) (hχ : χ a₀ = 1) (anchor : Real.Angle) :
    ∀ l ∈ (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).L,
      (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).chi l
        * (GridChar.ofHom φ χ hker a₀ hπ hχ anchor).chi l = 1 := by
  intro l hl
  obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hl
  rw [GridChar.ofHom_chi]
  split_ifs <;> norm_num
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open MeasureTheory Set
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
noncomputable def Dissection.overlap (D : Dissection N) (e e' : Fin N × Fin 3) : ℝ :=
  ((Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e ∩ D.eSet e')).toReal
theorem Dissection.overlap_comm (D : Dissection N) (e e' : Fin N × Fin 3) :
    D.overlap e e' = D.overlap e' e := by
  unfold Dissection.overlap
  rw [Set.inter_comm]
theorem Dissection.opposite_cover (D : Dissection N) {e : Fin N × Fin 3} (he : e ∈ D.intEdges) :
    ∑ e' ∈ D.intEdges.filter (fun e' => D.eDir e' = Dir.neg (D.eDir e)),
        (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e' ∩ D.eSet e)
      = (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e) := by
  refine sum_hausdorff_of_partition _ (fun e' => D.eSet e' ∩ D.eSet e) (D.eSet e) D.vertexSet
    D.vertexSet_finite ?_ ?_ ?_ ?_
  · intro e' _
    exact (((D.tile e'.1).isClosed_edge e'.2).inter
      ((D.tile e.1).isClosed_edge e.2)).measurableSet
  · intro e₁ h₁ e₂ h₂ hne
    have hd₁ := (Finset.mem_filter.mp h₁).2
    have hd₂ := (Finset.mem_filter.mp h₂).2
    exact (D.sameDir_subsingleton hne (hd₁.trans hd₂.symm)).anti
      (fun y hy => ⟨hy.1.1, hy.2.1⟩)
  · intro e' _
    exact Set.inter_subset_right
  · rintro x ⟨hx, hxv⟩
    have hnv := D.notMem_vertexSet hxv
    have hxint : x ∈ interior D.target.carrier :=
      D.mem_interior_of_mem_intEdges he hx (hnv _ _) (hnv _ _)
    have hxd : x ∈ D.dirSet (D.eDir e) := by
      unfold Dissection.dirSet
      exact ⟨Set.mem_iUnion.mpr ⟨e.1, Set.mem_iUnion.mpr ⟨e.2, Set.mem_iUnion.mpr ⟨rfl, hx⟩⟩⟩,
        hxint⟩
    have hxd' := (D.dirSet_sub D.pos (D.eDir e) ⟨hxd, hxv⟩).1
    obtain ⟨i, k, hik, hxik⟩ := D.mem_dirSet _ hxd'
    refine Set.mem_iUnion₂.mpr ⟨(i, k), ?_, hxik, hx⟩
    rw [Finset.mem_filter]
    exact ⟨D.mem_intEdges_of_interior (e := (i, k)) hxik hxint, hik⟩
theorem Dissection.opposite_cover_real (D : Dissection N) {e : Fin N × Fin 3}
    (he : e ∈ D.intEdges) :
    ∑ e' ∈ D.intEdges, (if D.eDir e' = Dir.neg (D.eDir e) then D.overlap e' e else 0)
      = D.eLen e := by
  rw [← Finset.sum_filter]
  have hfin : ∀ e' ∈ D.intEdges.filter (fun e' => D.eDir e' = Dir.neg (D.eDir e)),
      (Measure.hausdorffMeasure 1 : Measure Plane) (D.eSet e' ∩ D.eSet e) ≠ ⊤ := by
    intro e' _
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_right)
    rw [show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge]
    exact edist_ne_top _ _
  unfold Dissection.overlap
  rw [← ENNReal.toReal_sum hfin, D.opposite_cover he,
    show D.eSet e = (D.tile e.1).edge e.2 from rfl, Tri.hausdorff_edge, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg]
  rfl
theorem Dissection.interior_flux_zero (D : Dissection N) (f : Dir → E)
    (hodd : ∀ d, f (Dir.neg d) = - f d) :
    ∑ e ∈ D.intEdges, D.eLen e • f (D.eDir e) = 0 := by
  set I := D.intEdges with hI
  let A : Fin N × Fin 3 → Fin N × Fin 3 → ℝ := fun e e' =>
    if D.eDir e' = Dir.neg (D.eDir e) then D.overlap e' e else 0
  set X := ∑ e ∈ I, D.eLen e • f (D.eDir e) with hX
  have h1 : X = ∑ e ∈ I, ∑ e' ∈ I, A e e' • f (D.eDir e) := by
    refine Finset.sum_congr rfl fun e he => ?_
    rw [← Finset.sum_smul]
    congr 1
    exact (D.opposite_cover_real he).symm
  have hterm : ∀ e e', A e e' • f (D.eDir e) = -(A e' e • f (D.eDir e')) := by
    intro e e'
    by_cases h : D.eDir e' = Dir.neg (D.eDir e)
    · have h' : D.eDir e = Dir.neg (D.eDir e') := by rw [h, Dir.neg_involutive (D.eDir e)]
      have hA : A e e' = D.overlap e' e := if_pos h
      have hA' : A e' e = D.overlap e e' := if_pos h'
      rw [hA, hA', h', hodd, D.overlap_comm e' e, smul_neg]
    · have h' : ¬ D.eDir e = Dir.neg (D.eDir e') := fun h'' =>
        h (by rw [h'', Dir.neg_involutive (D.eDir e')])
      have hA : A e e' = 0 := if_neg h
      have hA' : A e' e = 0 := if_neg h'
      rw [hA, hA', zero_smul, zero_smul, neg_zero]
  have h2 : X = -X := by
    calc X = ∑ e ∈ I, ∑ e' ∈ I, A e e' • f (D.eDir e) := h1
      _ = ∑ e' ∈ I, ∑ e ∈ I, A e e' • f (D.eDir e) := Finset.sum_comm
      _ = ∑ e' ∈ I, ∑ e ∈ I, -(A e' e • f (D.eDir e')) :=
          Finset.sum_congr rfl fun e' _ => Finset.sum_congr rfl fun e _ => hterm e e'
      _ = -∑ e' ∈ I, ∑ e ∈ I, A e' e • f (D.eDir e') := by
          simp only [Finset.sum_neg_distrib]
      _ = -X := by rw [h1]
  have h3 : (2:ℝ) • X = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h2]
    exact neg_add_cancel X
  calc X = (2:ℝ)⁻¹ • ((2:ℝ) • X) := by
        rw [smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
    _ = 0 := by rw [h3, smul_zero]
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
theorem Dissection.flux_cancel (D : Dissection N) (f : Dir → E)
    (hodd : ∀ d, f (Dir.neg d) = - f d) :
    ∑ i, (D.tile i).flux f = D.target.flux f := by
  rw [D.flux_sum_eq, D.sum_split, D.interior_flux_zero f hodd, zero_add, D.side_flux]
theorem CongruentDissection.flux_cancel (D : CongruentDissection N) (f : Dir → E)
    (hodd : ∀ d, f (Dir.neg d) = - f d) :
    ∑ i, (D.tile i).flux f = D.target.flux f :=
  D.toDissection.flux_cancel f hodd
end Erdos634.Geometry
end

section
namespace Erdos634.InvariantCore
open Finset
theorem integrality_parity (N : ℕ) (sgn : Fin N → ℤ) (hs : ∀ i, sgn i = 1 ∨ sgn i = -1) :
    (2 : ℤ) ∣ (∑ i, sgn i) - (N : ℤ) := by
  have hsum : ∑ i : Fin N, (sgn i - 1) = (∑ i, sgn i) - (N : ℤ) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [← hsum]
  refine Finset.dvd_sum ?_
  intro i _
  rcases hs i with h | h <;> rw [h] <;> decide
end Erdos634.InvariantCore
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
theorem Tri.pi_sub_angleAt_mem (G : GridChar ℝ) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) (k : Fin 3) :
    ((Real.pi - T.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
  rw [Real.Angle.coe_sub]
  exact G.L.sub_mem G.pi_mem (h k)
theorem Tri.flux_grid_of_pos (G : GridChar ℝ) (T : Tri) (hT : 0 < T.det)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.weight (T.leftUnit 0) *
      (T.oppLen 2 + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
          * G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 1) := by
  have t1 := T.leftUnit_turn_of_pos hT 0
  have t2 := T.leftUnit_turn_of_pos hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t1 t2
  have w1 : G.weight (T.leftUnit 1)
      = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * G.weight (T.leftUnit 0) := by
    unfold GridChar.weight
    rw [t1, G.val_add _ (T.pi_sub_angleAt_mem G h 1)]
  have w2 : G.weight (T.leftUnit 2)
      = G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 1) := by
    unfold GridChar.weight
    rw [t2, G.val_add _ (T.pi_sub_angleAt_mem G h 2)]
  unfold Tri.flux Tri.oppLen
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 2 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl, smul_eq_mul]
  rw [w2, w1]
  ring
theorem Tri.flux_grid_of_neg (G : GridChar ℝ) (T : Tri) (hT : T.det < 0)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.weight (T.leftUnit 2) *
      (T.oppLen 1 + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle)
          * G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 2) := by
  have t0 := T.leftUnit_turn_of_neg hT 0
  have t1 := T.leftUnit_turn_of_neg hT 1
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl] at t0 t1
  have w1 : G.weight (T.leftUnit 1)
      = G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * G.weight (T.leftUnit 2) := by
    unfold GridChar.weight
    rw [t1, G.val_add _ (T.pi_sub_angleAt_mem G h 2)]
  have w0 : G.weight (T.leftUnit 0)
      = G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * G.weight (T.leftUnit 1) := by
    unfold GridChar.weight
    rw [t0, G.val_add _ (T.pi_sub_angleAt_mem G h 1)]
  unfold Tri.flux Tri.oppLen
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (1:Fin 3) + 1 = 2 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 2 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl, smul_eq_mul]
  rw [w0, w1]
  ring
noncomputable def GridChar.tileValue (G : GridChar ℝ) (T : Tri) : ℝ :=
  ∑ k : Fin 3, G.chi ((Real.pi - T.angleAt k : ℝ) : Real.Angle) * T.oppLen k
theorem Tri.chi_prod (G : GridChar ℝ) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle)
      * G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle)
      * G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) = 1 := by
  have m0 := T.pi_sub_angleAt_mem G h 0
  have m1 := T.pi_sub_angleAt_mem G h 1
  have m2 := T.pi_sub_angleAt_mem G h 2
  rw [← G.chi_add m0 m1, ← G.chi_add (G.L.add_mem m0 m1) m2, ← Real.Angle.coe_add,
    ← Real.Angle.coe_add]
  have hs : (Real.pi - T.angleAt 0) + (Real.pi - T.angleAt 1) + (Real.pi - T.angleAt 2)
      = 2 * Real.pi := by linarith [T.angleAt_sum]
  rw [hs, Real.Angle.coe_two_pi, G.chi_zero]
theorem Tri.flux_grid_pm (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1) (T : Tri)
    (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    T.flux G.weight = G.tileValue T ∨ T.flux G.weight = - G.tileValue T := by
  have hc0 := hsq _ (T.pi_sub_angleAt_mem G h 0)
  have hc1 := hsq _ (T.pi_sub_angleAt_mem G h 1)
  have hc2 := hsq _ (T.pi_sub_angleAt_mem G h 2)
  have hprod := T.chi_prod G h
  have hK : G.tileValue T
      = G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) * T.oppLen 0
        + G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) * T.oppLen 1
        + G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) * T.oppLen 2 := by
    unfold GridChar.tileValue
    rw [Fin.sum_univ_three]
  set c0 := G.chi ((Real.pi - T.angleAt 0 : ℝ) : Real.Angle) with hc0def
  set c1 := G.chi ((Real.pi - T.angleAt 1 : ℝ) : Real.Angle) with hc1def
  set c2 := G.chi ((Real.pi - T.angleAt 2 : ℝ) : Real.Angle) with hc2def
  rcases T.det_pos_or_neg with hT | hT
  · rw [T.flux_grid_of_pos G hT h, hK]
    set w := G.weight (T.leftUnit 0) with hwdef
    have hw : w * w = 1 := G.val_sq hsq _
    have e1 : c0 * c2 = c1 := by linear_combination c1 * hprod - (c0 * c2) * hc1
    have key : w * (T.oppLen 2 + c1 * T.oppLen 0 + c1 * c2 * T.oppLen 1)
        = (w * c2) * (c0 * T.oppLen 0 + c1 * T.oppLen 1 + c2 * T.oppLen 2) := by
      linear_combination (-(w * T.oppLen 0)) * e1 - (w * T.oppLen 2) * hc2
    have hs : (w * c2) * (w * c2) = 1 := by linear_combination c2 * c2 * hw + hc2
    rw [key]
    rcases mul_self_eq_one_iff.mp hs with h1 | h1
    · left; rw [h1, one_mul]
    · right; rw [h1, neg_one_mul]
  · rw [T.flux_grid_of_neg G hT h, hK]
    set w := G.weight (T.leftUnit 2) with hwdef
    have hw : w * w = 1 := G.val_sq hsq _
    have e2 : c0 * c1 = c2 := by linear_combination c2 * hprod - (c0 * c1) * hc2
    have key : w * (T.oppLen 1 + c2 * T.oppLen 0 + c2 * c1 * T.oppLen 2)
        = (w * c1) * (c0 * T.oppLen 0 + c1 * T.oppLen 1 + c2 * T.oppLen 2) := by
      linear_combination (-(w * T.oppLen 0)) * e2 - (w * T.oppLen 1) * hc1
    have hs : (w * c1) * (w * c1) = 1 := by linear_combination c1 * c1 * hw + hc1
    rw [key]
    rcases mul_self_eq_one_iff.mp hs with h1 | h1
    · left; rw [h1, one_mul]
    · right; rw [h1, neg_one_mul]
theorem Tri.Congruent.exists_perm {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k, T.angleAt k = U.angleAt (σ k) ∧ T.oppLen k = U.oppLen (σ k) := by
  obtain ⟨σ, hd⟩ := h.dist_eq
  refine ⟨σ, fun k => ?_⟩
  have hne1 : k + 1 ≠ k := by fin_cases k <;> decide
  have hne2 : k + 2 ≠ k := by fin_cases k <;> decide
  have hne12 : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  have hT1 : T.pts (k + 1) ≠ T.pts k := fun hh => hne1 (T.indep.injective hh)
  have hT2 : T.pts (k + 2) ≠ T.pts k := fun hh => hne2 (T.indep.injective hh)
  have hs1 : σ (k + 1) ≠ σ k := fun hh => hne1 (σ.injective hh)
  have hs2 : σ (k + 2) ≠ σ k := fun hh => hne2 (σ.injective hh)
  have hs12 : σ (k + 1) ≠ σ (k + 2) := fun hh => hne12 (σ.injective hh)
  have hang : T.angleAt k = cornerAngle (U.pts (σ (k + 1))) (U.pts (σ k)) (U.pts (σ (k + 2))) := by
    unfold Tri.angleAt cornerAngle
    exact angle_of_sss (hd (k + 1) k) (hd k (k + 2)) (hd (k + 1) (k + 2)) hT1 hT2
  have hopp : T.oppLen k = dist (U.pts (σ (k + 1))) (U.pts (σ (k + 2))) := hd (k + 1) (k + 2)
  have hsum : σ k + 1 ≠ σ k + 2 := by
    intro hh
    have := add_left_cancel hh
    exact absurd this (by decide)
  rcases fin3_cases _ _ hs1 with ha | ha
  · rcases fin3_cases _ _ hs2 with hb | hb
    · exact absurd (ha.trans hb.symm) hs12
    · refine ⟨?_, ?_⟩
      · rw [hang, ha, hb]; rfl
      · rw [hopp, ha, hb]; rfl
  · rcases fin3_cases _ _ hs2 with hb | hb
    · refine ⟨?_, ?_⟩
      · rw [hang, ha, hb]
        unfold Tri.angleAt cornerAngle
        exact EuclideanGeometry.angle_comm _ _ _
      · rw [hopp, ha, hb, dist_comm]; rfl
    · exact absurd (ha.trans hb.symm) hs12
theorem GridChar.tileValue_congr (G : GridChar ℝ) {T U : Tri} (h : T.Congruent U) :
    G.tileValue T = G.tileValue U := by
  obtain ⟨σ, hσ⟩ := h.exists_perm
  unfold GridChar.tileValue
  rw [← Equiv.sum_comp σ
    (fun j => G.chi ((Real.pi - U.angleAt j : ℝ) : Real.Angle) * U.oppLen j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(hσ k).1, (hσ k).2]
theorem CongruentDissection.target_flux_signs (D : CongruentDissection N) (G : GridChar ℝ)
    (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (h : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L) :
    ∃ S : ℤ, (2 : ℤ) ∣ S - N ∧ |S| ≤ N ∧
      D.target.flux G.weight = (S : ℝ) * G.tileValue D.model := by
  set K := G.tileValue D.model with hKdef
  have htile : ∀ i, (D.tile i).flux G.weight = K ∨ (D.tile i).flux G.weight = -K := by
    intro i
    obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).exists_perm
    have hi : ∀ k, (((D.tile i).angleAt k : ℝ) : Real.Angle) ∈ G.L := fun k => by
      rw [(hσ k).1]; exact h _
    rw [hKdef, ← G.tileValue_congr (D.tiles_congruent i)]
    exact (D.tile i).flux_grid_pm G hsq hi
  let ε : Fin N → ℤ := fun i => if (D.tile i).flux G.weight = K then 1 else -1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    by_cases hi : (D.tile i).flux G.weight = K
    · left; exact if_pos hi
    · right; exact if_neg hi
  have hεval : ∀ i, (D.tile i).flux G.weight = (ε i : ℝ) * K := by
    intro i
    by_cases hi : (D.tile i).flux G.weight = K
    · rw [show ε i = 1 from if_pos hi]; push_cast; rw [one_mul, hi]
    · rw [show ε i = -1 from if_neg hi]; push_cast
      rcases htile i with h1 | h1
      · exact absurd h1 hi
      · rw [h1, neg_one_mul]
  refine ⟨∑ i, ε i, InvariantCore.integrality_parity N ε hε, ?_, ?_⟩
  · calc |∑ i, ε i| ≤ ∑ i, |ε i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _i : Fin N, (1 : ℤ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rcases hε i with h1 | h1 <;> rw [h1] <;> rfl
      _ = N := by simp
  · rw [← D.flux_cancel G.weight G.weight_odd]
    rw [Finset.sum_congr rfl fun i _ => hεval i, ← Finset.sum_mul]
    push_cast
    rfl
end Erdos634.Geometry
end

section
namespace Erdos634.VertexFigureReal
open Erdos634.Geometry Finset
theorem localAngle_mem {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (hcorners : ∀ (i : Fin N) (j : Fin 3),
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        ∈ ({α, β, γ} : Finset ℝ))
    (i : Fin N) : (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
  classical
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with ⟨j, _, hval⟩ | h2 | hpi | h0
  · have := hcorners i j
    rw [hval]
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  · exact absurd (Erdos634.PinPlumbing.no_interior_tile_at_pin D hv hnv i h2) (by simp)
  · simp [hpi]
  · simp [h0]
end Erdos634.VertexFigureReal
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
noncomputable def sideOpp (T : Tri) (j : Fin 3) : ℝ := dist (T.pts (j + 1)) (T.pts (j + 2))
noncomputable def angleAt (T : Tri) (j : Fin 3) : ℝ :=
  cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))
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
namespace Erdos634.TriLawSin
open Erdos634.Geometry Erdos634.TilePlacement
theorem sin_angleAt_mul_sideOpp (T : Tri) (j : Fin 3) :
    Real.sin (angleAt T (j + 1)) * sideOpp T j
      = Real.sin (angleAt T j) * sideOpp T (j + 1) := by
  fin_cases j
  · simpa [angleAt, sideOpp, cornerAngle, EuclideanGeometry.angle_comm] using
      EuclideanGeometry.law_sin (T.pts 0) (T.pts 1) (T.pts 2)
  · simpa [angleAt, sideOpp, cornerAngle, EuclideanGeometry.angle_comm] using
      EuclideanGeometry.law_sin (T.pts 1) (T.pts 2) (T.pts 0)
  · simpa [angleAt, sideOpp, cornerAngle, EuclideanGeometry.angle_comm] using
      EuclideanGeometry.law_sin (T.pts 2) (T.pts 0) (T.pts 1)
end Erdos634.TriLawSin
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
variable {N : ℕ}
theorem Tri.lawSin (T : Tri) (i j : Fin 3) :
    Real.sin (T.angleAt i) * T.oppLen j = Real.sin (T.angleAt j) * T.oppLen i := by
  have h0 : Real.sin (T.angleAt 1) * T.oppLen 0 = Real.sin (T.angleAt 0) * T.oppLen 1 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 0
  have h1 : Real.sin (T.angleAt 2) * T.oppLen 1 = Real.sin (T.angleAt 1) * T.oppLen 2 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 1
  have h2 : Real.sin (T.angleAt 0) * T.oppLen 2 = Real.sin (T.angleAt 2) * T.oppLen 0 :=
    Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 2
  fin_cases i <;> fin_cases j
  · rfl
  · exact h0.symm
  · exact h2
  · exact h0
  · rfl
  · exact h1.symm
  · exact h2.symm
  · exact h1
  · rfl
theorem Tri.angleAt_pos' (T : Tri) (j : Fin 3) : 0 < T.angleAt j :=
  Erdos634.MarchFlank.cornerAngle_pos T j
theorem Tri.oppLen_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  have hne : k + 1 ≠ k + 2 := by fin_cases k <;> decide
  exact dist_pos.mpr fun h => hne (T.indep.injective h)
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
theorem exists_zmod2_char {A : Type*} [AddCommGroup A] (x : A) (hx : ∀ y : A, x ≠ 2 • y) :
    ∃ χ : A →+ ZMod 2, χ x = 1 := by
  let H : AddSubgroup A := (nsmulAddMonoidHom 2 : A →+ A).range
  have hH : ∀ z : A, 2 • z ∈ H := fun z => AddMonoidHom.mem_range.mpr ⟨z, rfl⟩
  letI : Module (ZMod 2) (A ⧸ H) := QuotientAddGroup.zmodModule hH
  have hq : (QuotientAddGroup.mk x : A ⧸ H) ≠ 0 := by
    intro h
    rw [QuotientAddGroup.eq_zero_iff] at h
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.mp h
    exact hx z hz.symm
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hq
  exact ⟨f.toAddMonoidHom.comp (QuotientAddGroup.mk' H), hf⟩
theorem Tri.range_pts_eq' (T : Tri) (j : Fin 3) :
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
theorem Tri.strict_triangle' (T : Tri) (j : Fin 3) :
    dist (T.pts (j + 1)) (T.pts (j + 2))
      < dist (T.pts (j + 1)) (T.pts j) + dist (T.pts j) (T.pts (j + 2)) := by
  rcases lt_or_eq_of_le (dist_triangle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exact h
  · exfalso
    have hw : Wbtw ℝ (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) :=
      dist_add_dist_eq_iff.mp h.symm
    have hcol : Collinear ℝ (Set.range T.pts) := by
      rw [T.range_pts_eq' j]; exact hw.collinear
    exact (affineIndependent_iff_not_collinear.mp T.indep) hcol
theorem GridChar.tileValue_ne_zero (G : GridChar ℝ) (hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1)
    (T : Tri) (h : ∀ k, ((T.angleAt k : ℝ) : Real.Angle) ∈ G.L) : G.tileValue T ≠ 0 := by
  unfold GridChar.tileValue Tri.oppLen
  rw [Fin.sum_univ_three]
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  have s0 := T.strict_triangle' 0
  have s1 := T.strict_triangle' 1
  have s2 := T.strict_triangle' 2
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl] at s0 s1 s2
  have c01 := dist_comm (T.pts 0) (T.pts 1)
  have c12 := dist_comm (T.pts 1) (T.pts 2)
  have c20 := dist_comm (T.pts 2) (T.pts 0)
  rcases mul_self_eq_one_iff.mp (hsq _ (T.pi_sub_angleAt_mem G h 0)) with e0 | e0 <;>
  rcases mul_self_eq_one_iff.mp (hsq _ (T.pi_sub_angleAt_mem G h 1)) with e1 | e1 <;>
  rcases mul_self_eq_one_iff.mp (hsq _ (T.pi_sub_angleAt_mem G h 2)) with e2 | e2 <;>
  · rw [e0, e1, e2]
    intro hz
    linarith
theorem Row2.lemmaW {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k
      ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hπ : ∀ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, Real.pi} : Set ℝ),
      Real.pi ≠ 2 * y) :
    ∃ S : ℤ, μ = S ∧ (2 : ℤ) ∣ S - N := by
  set Λ := AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, Real.pi} : Set ℝ) with hΛ
  have hπΛ : Real.pi ∈ Λ := AddSubgroup.subset_closure (by simp)
  have h0Λ : D.model.angleAt 0 ∈ Λ := AddSubgroup.subset_closure (by simp)
  have h1Λ : D.model.angleAt 1 ∈ Λ := AddSubgroup.subset_closure (by simp)
  have h2Λ : D.model.angleAt 2 ∈ Λ := by
    have hs := D.model.angleAt_sum
    have e : D.model.angleAt 2 = Real.pi - D.model.angleAt 0 - D.model.angleAt 1 := by linarith
    rw [e]
    exact Λ.sub_mem (Λ.sub_mem hπΛ h0Λ) h1Λ
  let x₀ : Λ := ⟨Real.pi, hπΛ⟩
  have hx : ∀ y : Λ, x₀ ≠ 2 • y := by
    intro y hy
    have h1 : ((x₀ : Λ) : ℝ) = ((2 • y : Λ) : ℝ) := congrArg Subtype.val hy
    have h2 : Real.pi = 2 * (y : ℝ) := by
      rw [show ((x₀ : Λ) : ℝ) = Real.pi from rfl, AddSubgroup.coe_nsmul, nsmul_eq_mul] at h1
      exact_mod_cast h1
    exact hπ y y.2 h2
  obtain ⟨χ, hχ⟩ := exists_zmod2_char x₀ hx
  let φ : Λ →+ Real.Angle := Real.Angle.coeHom.comp Λ.subtype
  have hφ : ∀ a : Λ, φ a = ((a : ℝ) : Real.Angle) := fun a => rfl
  have hker : ∀ a, φ a = 0 → χ a = 0 := by
    intro a ha
    rw [hφ, Real.Angle.coe_eq_zero_iff] at ha
    obtain ⟨m, hm⟩ := ha
    have hsplit : a = 2 • (m • x₀) := by
      apply Subtype.ext
      rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zsmul, ← hm]
      show m • (2 * Real.pi) = 2 • (m • Real.pi)
      rw [zsmul_eq_mul, zsmul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    rw [hsplit, map_nsmul, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  let G : GridChar ℝ := GridChar.ofHom φ χ hker x₀ rfl hχ 0
  have hsq : ∀ l ∈ G.L, G.chi l * G.chi l = 1 := GridChar.ofHom_sq φ χ hker x₀ rfl hχ 0
  have hmemL : ∀ θ ∈ Λ, ((θ : ℝ) : Real.Angle) ∈ G.L := fun θ hθ =>
    AddMonoidHom.mem_range.mpr ⟨⟨θ, hθ⟩, rfl⟩
  have hmodel : ∀ k, ((D.model.angleAt k : ℝ) : Real.Angle) ∈ G.L := by
    intro k
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    rcases hk with rfl | rfl | rfl
    · exact hmemL _ h0Λ
    · exact hmemL _ h1Λ
    · exact hmemL _ h2Λ
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ G.L := fun k => by
    rw [(hsim k).1]; exact hmodel k
  obtain ⟨S, hS2, -, hSf⟩ := D.target_flux_signs G hsq hmodel
  have hKt : G.tileValue D.target = μ * G.tileValue D.model := by
    unfold GridChar.tileValue
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hsim k).1, (hsim k).2]
    ring
  have hK0 := G.tileValue_ne_zero hsq D.model hmodel
  rcases D.target.flux_grid_pm G hsq htarget with h1 | h1
  · refine ⟨S, ?_, hS2⟩
    rw [hSf, hKt] at h1
    exact (mul_right_cancel₀ hK0 h1).symm
  · refine ⟨-S, ?_, ?_⟩
    · rw [hSf, hKt] at h1
      have h3 : ((S : ℝ) + μ) * G.tileValue D.model = 0 := by linear_combination h1
      have h4 := (mul_eq_zero.mp h3).resolve_right hK0
      push_cast
      linarith
    · rw [show -S - (N : ℤ) = -(S - N) - 2 * N by ring]
      exact dvd_sub (dvd_neg.mpr hS2) (dvd_mul_right 2 _)
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open MeasureTheory
variable {N : ℕ}
theorem dist_sq_coord' (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
theorem Tri.four_detTri_sq (T : Tri) :
    4 * Erdos634.AreaDet.detTri T ^ 2
      = 4 * T.oppLen 2 ^ 2 * T.oppLen 1 ^ 2 - (T.oppLen 2 ^ 2 + T.oppLen 1 ^ 2 - T.oppLen 0 ^ 2) ^ 2 := by
  rw [Erdos634.AreaDet.detTri_eq]
  unfold Tri.oppLen
  simp only [show (0:Fin 3) + 1 = 1 from rfl, show (0:Fin 3) + 2 = 2 from rfl,
    show (1:Fin 3) + 1 = 2 from rfl, show (1:Fin 3) + 2 = 0 from rfl,
    show (2:Fin 3) + 1 = 0 from rfl, show (2:Fin 3) + 2 = 1 from rfl]
  rw [dist_sq_coord' (T.pts 0) (T.pts 1), dist_sq_coord' (T.pts 2) (T.pts 0),
    dist_sq_coord' (T.pts 1) (T.pts 2)]
  simp only [PiLp.sub_apply]
  ring
theorem Tri.detTri_eq_det (T : Tri) : Erdos634.AreaDet.detTri T = T.det := by
  rw [Erdos634.AreaDet.detTri_eq]
  unfold Tri.det
  ring
theorem CongruentDissection.abs_detTri_target (D : CongruentDissection N) :
    |Erdos634.AreaDet.detTri D.target| = N * |Erdos634.AreaDet.detTri D.model| := by
  have h := Erdos634.CongruentArea.congruentDissection_volume_target D
  have hm := D.model.volume_pos
  have hmt := D.model.volume_ne_top
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.volume_eq_det_mul] at h
  rw [Erdos634.AreaDet.volume_eq_det_mul] at hm hmt
  set V := volume Erdos634.AreaDet.stdCarrier with hVdef
  have hV0 : V ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hm; exact lt_irrefl _ hm
  have hd0 : ENNReal.ofReal |Erdos634.AreaDet.detTri D.model| ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hm; exact lt_irrefl _ hm
  have hVt : V ≠ ⊤ := by
    intro ht; apply hmt; rw [ht, ENNReal.mul_top hd0]
  rw [← mul_assoc, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)] at h
  have h2 := (ENNReal.mul_left_inj hV0 hVt).mp h
  exact (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (by positivity)).mp h2
theorem Row2.area_scale (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) : (N : ℝ) = μ ^ 2 := by
  have hA := D.abs_detTri_target
  have hT := D.target.four_detTri_sq
  have hM := D.model.four_detTri_sq
  rw [hside 0, hside 1, hside 2] at hT
  have hdm : Erdos634.AreaDet.detTri D.model ≠ 0 := by
    rw [Tri.detTri_eq_det]; exact D.model.det_ne_zero
  have hsq : Erdos634.AreaDet.detTri D.target ^ 2 = (N : ℝ) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hA
    simp only [mul_pow, sq_abs] at h
    exact h
  have h4 : Erdos634.AreaDet.detTri D.target ^ 2 = (μ ^ 2) ^ 2 * Erdos634.AreaDet.detTri D.model ^ 2 := by
    linear_combination (1/4 : ℝ) * hT - (μ ^ 4 / 4) * hM
  have hd2 : Erdos634.AreaDet.detTri D.model ^ 2 ≠ 0 := pow_ne_zero 2 hdm
  have hN2 : (N : ℝ) ^ 2 = (μ ^ 2) ^ 2 := by
    have := hsq.symm.trans h4
    exact mul_right_cancel₀ hd2 this
  have hNpos : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hμpos : (0 : ℝ) ≤ μ ^ 2 := sq_nonneg μ
  exact (pow_left_inj₀ hNpos hμpos two_ne_zero).mp hN2
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
theorem Tri.oppLen_succ (T : Tri) (v : Fin 3) : T.oppLen (v + 1) = dist (T.pts (v + 2)) (T.pts v) := by
  unfold Tri.oppLen
  rw [show v + 1 + 1 = v + 2 by fin_cases v <;> rfl, show v + 1 + 2 = v by fin_cases v <;> rfl]
theorem Tri.oppLen_succ2 (T : Tri) (v : Fin 3) : T.oppLen (v + 2) = dist (T.pts (v + 1)) (T.pts v) := by
  unfold Tri.oppLen
  rw [show v + 2 + 1 = v by fin_cases v <;> rfl, show v + 2 + 2 = v + 1 by fin_cases v <;> rfl,
    dist_comm]
theorem Tri.lawCos (T : Tri) (v : Fin 3) :
    T.oppLen v ^ 2 = T.oppLen (v + 1) ^ 2 + T.oppLen (v + 2) ^ 2
      - 2 * T.oppLen (v + 1) * T.oppLen (v + 2) * Real.cos (T.angleAt v) := by
  have hlaw :=
    EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle
      (T.pts (v + 1)) (T.pts v) (T.pts (v + 2))
  rw [T.oppLen_succ, T.oppLen_succ2]
  show dist (T.pts (v + 1)) (T.pts (v + 2)) ^ 2 = _ - _ * Real.cos
    (EuclideanGeometry.angle (T.pts (v + 1)) (T.pts v) (T.pts (v + 2)))
  linear_combination hlaw
end Erdos634.Geometry
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
namespace Erdos634.EdgeWordConversion
open Erdos634.Geometry
variable {N : ℕ}
noncomputable def sideLen (D : CongruentDissection N) : Fin 3 → ℝ :=
  fun i => dist (D.model.pts i) (D.model.pts (i + 1))
theorem dist_pair_mem_sideLen (T : Erdos634.Geometry.Tri) (i i' : Fin 3) (hii' : i ≠ i') :
    ∃ k : Fin 3, dist (T.pts i) (T.pts i') = dist (T.pts k) (T.pts (k + 1)) := by
  fin_cases i <;> fin_cases i' <;> simp_all
  · exact ⟨0, rfl⟩
  · exact ⟨2, dist_comm _ _⟩
  · exact ⟨0, dist_comm _ _⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨1, dist_comm _ _⟩
theorem edge_succ_ne (j : Fin 3) : j ≠ j + 1 := by
  fin_cases j <;> decide
theorem chain_edge_length_mem_model (D : CongruentDissection N) (e : Fin N × Fin 3) :
    ∃ i : Fin 3, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = sideLen D i := by
  have hne : e.2 ≠ e.2 + 1 := edge_succ_ne e.2
  obtain ⟨i, i', hii', hdist⟩ :=
    congruent_edge_lengths (D.tiles_congruent e.1).symm e.2 (e.2 + 1) hne
  obtain ⟨k, hk⟩ := dist_pair_mem_sideLen D.model i i' hii'
  exact ⟨k, hdist.trans hk⟩
end Erdos634.EdgeWordConversion
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
theorem CongruentDissection.sideLen_eq_oppLen (D : CongruentDissection N) (i : Fin 3) :
    Erdos634.EdgeWordConversion.sideLen D i = D.model.oppLen (i + 2) := by
  unfold Erdos634.EdgeWordConversion.sideLen Tri.oppLen
  fin_cases i <;> rfl
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
theorem irr_coord_eq_zero {s : ℝ} (hs : ¬ ∃ r : ℚ, s = r) {p q : ℤ}
    (h : (q : ℝ) * s + p = 0) : q = 0 ∧ p = 0 := by
  by_cases hq : q = 0
  · subst hq
    refine ⟨rfl, ?_⟩
    have : (p : ℝ) = 0 := by simpa using h
    exact_mod_cast this
  · exfalso
    apply hs
    have hq' : (q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hq
    refine ⟨-(p : ℚ) / q, ?_⟩
    push_cast
    rw [eq_div_iff hq']
    linear_combination h
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
theorem Row2.det_sub_smul (A : Matrix (Fin 3) (Fin 3) ℝ) (x : ℝ) :
    (A - x • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = -x ^ 3 + (A 0 0 + A 1 1 + A 2 2) * x ^ 2
        - (A 0 0 * A 1 1 + A 0 0 * A 2 2 + A 1 1 * A 2 2 - A 1 2 * A 2 1 - A 0 1 * A 1 0
            - A 0 2 * A 2 0) * x
        + (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2
            + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0) := by
  rw [Matrix.det_fin_three]
  simp
  ring
theorem Row2.neg_eigen_det (D : Fin 3 → Fin 3 → ℕ) {μ : ℝ} (hμ : ¬ ∃ r : ℚ, μ = r) {p : ℤ}
    (hp : μ ^ 2 = p)
    (hdet : (Matrix.of (fun i j => (D i j : ℝ)) - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0) :
    (Matrix.of (fun i j => (D i j : ℝ)) + μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
  set A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j => (D i j : ℝ)) with hAdef
  have hchar := Row2.det_sub_smul A μ
  rw [hdet] at hchar
  simp only [hAdef, Matrix.of_apply] at hchar
  have e : (((-p - ((D 0 0 : ℤ) * D 1 1 + (D 0 0 : ℤ) * D 2 2 + (D 1 1 : ℤ) * D 2 2
        - (D 1 2 : ℤ) * D 2 1 - (D 0 1 : ℤ) * D 1 0 - (D 0 2 : ℤ) * D 2 0)) : ℤ) : ℝ) * μ
      + ((((D 0 0 : ℤ) + D 1 1 + D 2 2) * p
        + ((D 0 0 : ℤ) * D 1 1 * D 2 2 - (D 0 0 : ℤ) * D 1 2 * D 2 1 - (D 0 1 : ℤ) * D 1 0 * D 2 2
          + (D 0 1 : ℤ) * D 1 2 * D 2 0 + (D 0 2 : ℤ) * D 1 0 * D 2 1
          - (D 0 2 : ℤ) * D 1 1 * D 2 0) : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination (-1 : ℝ) * hchar
      + (μ - ((D 0 0 : ℝ) + D 1 1 + D 2 2)) * hp
  obtain ⟨hq, hp'⟩ := irr_coord_eq_zero hμ e
  have hq' := congrArg (fun z : ℤ => (z : ℝ)) hq
  have hp'' := congrArg (fun z : ℤ => (z : ℝ)) hp'
  push_cast at hq' hp''
  have h2 := Row2.det_sub_smul A (-μ)
  rw [neg_smul, sub_neg_eq_add] at h2
  rw [h2]
  simp only [hAdef, Matrix.of_apply]
  linear_combination (-μ) * hq' + hp'' + (μ + ((D 0 0 : ℝ) + D 1 1 + D 2 2)) * hp
theorem Row2.lemmaD (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i) {μ : ℝ}
    (hμ : ¬ ∃ r : ℚ, μ = r) {p : ℤ} (hp : μ ^ 2 = p)
    (hDv : ∀ i, ∑ j, (D i j : ℝ) * v j = μ * v i) (hrow : ∀ i, ∃ j, 0 < D i j)
    (hA : (0 < D 2 1 ∧ 0 < D 1 2) ∨ (0 < D 2 2 ∧ 0 < D 1 1))
    (hB : (0 < D 2 0 ∧ 0 < D 0 2) ∨ (0 < D 2 2 ∧ 0 < D 0 0)) :
    D 0 0 = 0 ∧ D 0 1 = 0 ∧ D 1 0 = 0 ∧ D 1 1 = 0 ∧ D 2 2 = 0 ∧
      0 < D 0 2 ∧ 0 < D 1 2 ∧ 0 < D 2 0 ∧ 0 < D 2 1 := by
  set A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j => (D i j : ℝ)) with hAdef
  have hdet1 : (A - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, fun h => (hv 0).ne' (congrFun h 0), ?_⟩
    ext i
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have : (Matrix.mulVec A v) i = ∑ j, (D i j : ℝ) * v j := by
      simp [hAdef, Matrix.mulVec, dotProduct]
    rw [this, hDv i, sub_self]
  have hdet2 := Row2.neg_eigen_det D hμ hp hdet1
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet2
  have hDw : ∀ i, ∑ j, (D i j : ℝ) * w j = -μ * w i := by
    intro i
    have h := congrFun hw i
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    have : (Matrix.mulVec (Matrix.of fun i j => (D i j : ℝ)) w) i = ∑ j, (D i j : ℝ) * w j := by
      simp [Matrix.mulVec, dotProduct]
    rw [this] at h
    linarith
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun j => |w j| / v j)
    Finset.univ_nonempty
  set t := |w i₀| / v i₀ with htdef
  have hle : ∀ j, |w j| ≤ t * v j := fun j => by
    have := hi₀ j (Finset.mem_univ _)
    rwa [div_le_iff₀ (hv j)] at this
  have ht : 0 < t := by
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
      by_contra hc; push Not at hc; exact hw0 (funext hc)
    have h1 : 0 < |w j| := abs_pos.mpr hj
    have h2 := hle j
    have h3 := hv j
    by_contra ht'; push Not at ht'
    have := mul_nonpos_of_nonpos_of_nonneg ht' h3.le
    linarith
  have htv : ∀ j, 0 < t * v j := fun j => mul_pos ht (hv j)
  have hi₀eq : |w i₀| = t * v i₀ := by rw [htdef, div_mul_cancel₀ _ (hv i₀).ne']
  have sgn : ∀ i j, (w i = t * v i → 0 < D i j → w j = -(t * v j)) ∧
      (w i = -(t * v i) → 0 < D i j → w j = t * v j) := by
    intro i j
    have e1 := hDw i
    have e2 := hDv i
    constructor
    · intro hi hij
      have hsum : ∑ k, (D i k : ℝ) * (t * v k + w k) = 0 := by
        rw [Fin.sum_univ_three] at e1 e2 ⊢
        rw [hi] at e1
        linear_combination e1 + t * e2
      have hnn : ∀ k ∈ Finset.univ, 0 ≤ (D i k : ℝ) * (t * v k + w k) := fun k _ =>
        mul_nonneg (Nat.cast_nonneg _) (by have := hle k; have := neg_abs_le (w k); linarith)
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ _)
      have hD : (0 : ℝ) < D i j := by exact_mod_cast hij
      have := (mul_eq_zero.mp h0).resolve_left hD.ne'
      linarith
    · intro hi hij
      have hsum : ∑ k, (D i k : ℝ) * (t * v k - w k) = 0 := by
        rw [Fin.sum_univ_three] at e1 e2 ⊢
        rw [hi] at e1
        linear_combination -e1 + t * e2
      have hnn : ∀ k ∈ Finset.univ, 0 ≤ (D i k : ℝ) * (t * v k - w k) := fun k _ =>
        mul_nonneg (Nat.cast_nonneg _) (by have := hle k; have := le_abs_self (w k); linarith)
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum j (Finset.mem_univ _)
      have hD : (0 : ℝ) < D i j := by exact_mod_cast hij
      have := (mul_eq_zero.mp h0).resolve_left hD.ne'
      linarith
  have self0 : ∀ i, (w i = t * v i ∨ w i = -(t * v i)) → D i i = 0 := by
    intro i hi
    by_contra hne
    have hpos : 0 < D i i := Nat.pos_of_ne_zero hne
    have := htv i
    rcases hi with hi | hi
    · have := (sgn i i).1 hi hpos; linarith
    · have := (sgn i i).2 hi hpos; linarith
  have hi₀S : w i₀ = t * v i₀ ∨ w i₀ = -(t * v i₀) := by
    rcases abs_choice (w i₀) with h | h
    · left; rw [← h, hi₀eq]
    · right; rw [← hi₀eq, h, neg_neg]
  by_cases hcp : w 2 = t * v 2
  · have h22 := self0 2 (Or.inl hcp)
    have hA' : 0 < D 2 1 ∧ 0 < D 1 2 := by
      rcases hA with h | h
      · exact h
      · omega
    have hB' : 0 < D 2 0 ∧ 0 < D 0 2 := by
      rcases hB with h | h
      · exact h
      · omega
    have hw1 := (sgn 2 1).1 hcp hA'.1
    have hw0 := (sgn 2 0).1 hcp hB'.1
    have h00 := self0 0 (Or.inr hw0)
    have h11 := self0 1 (Or.inr hw1)
    have h01 : D 0 1 = 0 := by
      by_contra hne
      have := (sgn 0 1).2 hw0 (Nat.pos_of_ne_zero hne)
      have := htv 1
      linarith
    have h10 : D 1 0 = 0 := by
      by_contra hne
      have := (sgn 1 0).2 hw1 (Nat.pos_of_ne_zero hne)
      have := htv 0
      linarith
    exact ⟨h00, h01, h10, h11, h22, hB'.2, hA'.2, hB'.1, hA'.1⟩
  by_cases hcm : w 2 = -(t * v 2)
  · have h22 := self0 2 (Or.inr hcm)
    have hA' : 0 < D 2 1 ∧ 0 < D 1 2 := by
      rcases hA with h | h
      · exact h
      · omega
    have hB' : 0 < D 2 0 ∧ 0 < D 0 2 := by
      rcases hB with h | h
      · exact h
      · omega
    have hw1 := (sgn 2 1).2 hcm hA'.1
    have hw0 := (sgn 2 0).2 hcm hB'.1
    have h00 := self0 0 (Or.inl hw0)
    have h11 := self0 1 (Or.inl hw1)
    have h01 : D 0 1 = 0 := by
      by_contra hne
      have := (sgn 0 1).1 hw0 (Nat.pos_of_ne_zero hne)
      have := htv 1
      linarith
    have h10 : D 1 0 = 0 := by
      by_contra hne
      have := (sgn 1 0).1 hw1 (Nat.pos_of_ne_zero hne)
      have := htv 0
      linarith
    exact ⟨h00, h01, h10, h11, h22, hB'.2, hA'.2, hB'.1, hA'.1⟩
  exfalso
  have hno2 : ∀ i, (w i = t * v i ∨ w i = -(t * v i)) → D i 2 = 0 := by
    intro i hi
    by_contra hne
    have hpos := Nat.pos_of_ne_zero hne
    rcases hi with hi | hi
    · exact hcm ((sgn i 2).1 hi hpos)
    · exact hcp ((sgn i 2).2 hi hpos)
  have ha : w 0 = t * v 0 ∨ w 0 = -(t * v 0) := by
    have hcase : i₀ = 0 ∨ i₀ = 1 ∨ i₀ = 2 := by fin_cases i₀ <;> simp
    rcases hcase with h | h | h
    · rw [h] at hi₀S; exact hi₀S
    · rw [h] at hi₀S
      obtain ⟨j, hj⟩ := hrow 1
      have hjcase : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hjcase with rfl | rfl | rfl
      · rcases hi₀S with h' | h'
        · right; exact (sgn 1 0).1 h' hj
        · left; exact (sgn 1 0).2 h' hj
      · exact absurd (self0 1 hi₀S) hj.ne'
      · exact absurd (hno2 1 hi₀S) hj.ne'
    · rw [h] at hi₀S
      rcases hi₀S with h' | h'
      · exact absurd h' hcp
      · exact absurd h' hcm
  have h02 := hno2 0 ha
  have h00 := self0 0 ha
  omega
theorem Row2.lemmaD_scale (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i) {μ : ℝ}
    (hμ : ¬ ∃ r : ℚ, μ = r) {p : ℤ} (hp : μ ^ 2 = p)
    (hDv : ∀ i, ∑ j, (D i j : ℝ) * v j = μ * v i) (hrow : ∀ i, ∃ j, 0 < D i j)
    (hA : (0 < D 2 1 ∧ 0 < D 1 2) ∨ (0 < D 2 2 ∧ 0 < D 1 1))
    (hB : (0 < D 2 0 ∧ 0 < D 0 2) ∨ (0 < D 2 2 ∧ 0 < D 0 0)) :
    μ * v 0 = D 0 2 * v 2 ∧ μ * v 1 = D 1 2 * v 2 ∧ μ * v 2 = D 2 0 * v 0 + D 2 1 * v 1 := by
  obtain ⟨h00, h01, h10, h11, h22, -⟩ := Row2.lemmaD D v hv hμ hp hDv hrow hA hB
  have e0 := hDv 0
  have e1 := hDv 1
  have e2 := hDv 2
  rw [Fin.sum_univ_three] at e0 e1 e2
  rw [h00, h01] at e0
  rw [h10, h11] at e1
  rw [h22] at e2
  push_cast at e0 e1 e2
  refine ⟨by linarith, by linarith, by linarith⟩
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
noncomputable def CongruentDissection.sideCount (D : CongruentDissection N) (i k : Fin 3) : ℕ :=
  ((D.sideEdges (i + 1)).filter (fun e => D.eLen e = D.model.oppLen k)).card
theorem CongruentDissection.eLen_mem (D : CongruentDissection N) (e : Fin N × Fin 3) :
    ∃ k, D.eLen e = D.model.oppLen k := by
  obtain ⟨k, hk⟩ := Erdos634.EdgeWordConversion.chain_edge_length_mem_model D e
  exact ⟨k + 2, hk.trans (D.sideLen_eq_oppLen k)⟩
theorem CongruentDissection.sideCount_sum (D : CongruentDissection N)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') (i : Fin 3) :
    ∑ k, (D.sideCount i k : ℝ) * D.model.oppLen k = D.target.oppLen i := by
  have hlen := D.toDissection.side_len_sum (i + 1)
  have hopp : D.target.oppLen i = dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) := by
    unfold Tri.oppLen
    rw [show i + 1 + 1 = i + 2 by fin_cases i <;> rfl]
  rw [hopp, ← hlen]
  have hsplit : ∀ e ∈ D.sideEdges (i + 1), D.eLen e
      = ∑ k, if D.eLen e = D.model.oppLen k then D.model.oppLen k else 0 := by
    intro e _
    obtain ⟨k, hk⟩ := D.eLen_mem e
    rw [Finset.sum_eq_single k]
    · rw [if_pos hk, hk]
    · intro k' _ hk'
      rw [if_neg]
      intro h
      exact hscal k' k hk' (h.symm.trans hk)
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [Finset.sum_congr rfl hsplit, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold CongruentDissection.sideCount
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
theorem Row2.sideCount_eigen (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') (i : Fin 3) :
    ∑ j, (D.sideCount i j : ℝ) * D.model.oppLen j = μ * D.model.oppLen i := by
  rw [D.sideCount_sum hscal i, hside i]
theorem Row2.sideCount_rows (D : CongruentDissection N)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') (i : Fin 3) :
    ∃ j, 0 < D.sideCount i j := by
  by_contra h
  push Not at h
  have h0 : ∀ j, D.sideCount i j = 0 := fun j => by have := h j; omega
  have hs := D.sideCount_sum hscal i
  simp only [h0, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at hs
  exact (D.target.oppLen_pos i).ne' hs.symm
theorem Row2.mu_irrational (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) (hN : ¬ IsSquare N) :
    (¬ ∃ r : ℚ, μ = r) ∧ μ ^ 2 = ((N : ℤ) : ℝ) := by
  have harea := Row2.area_scale D μ hside
  refine ⟨?_, by push_cast; exact harea.symm⟩
  rintro ⟨r, hr⟩
  have hq : ((N : ℚ) : ℝ) = ((r * r : ℚ) : ℝ) := by
    push_cast; rw [harea, hr]; ring
  have hq' : (N : ℚ) = r * r := Rat.cast_injective hq
  exact hN (Rat.isSquare_natCast_iff.mp ⟨r, hq'⟩)
theorem Row2.lemmaD_tiling (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') (hN : ¬ IsSquare N)
    (hA : (0 < D.sideCount 2 1 ∧ 0 < D.sideCount 1 2) ∨ (0 < D.sideCount 2 2 ∧ 0 < D.sideCount 1 1))
    (hB : (0 < D.sideCount 2 0 ∧ 0 < D.sideCount 0 2) ∨ (0 < D.sideCount 2 2 ∧ 0 < D.sideCount 0 0)) :
    D.sideCount 0 0 = 0 ∧ D.sideCount 0 1 = 0 ∧ D.sideCount 1 0 = 0 ∧ D.sideCount 1 1 = 0 ∧
      D.sideCount 2 2 = 0 ∧ 0 < D.sideCount 0 2 ∧ 0 < D.sideCount 1 2 ∧ 0 < D.sideCount 2 0 ∧
      0 < D.sideCount 2 1 := by
  obtain ⟨hμ, hp⟩ := Row2.mu_irrational D μ hside hN
  exact Row2.lemmaD D.sideCount D.model.oppLen D.model.oppLen_pos hμ hp
    (Row2.sideCount_eigen D μ hside hscal) (Row2.sideCount_rows D hscal) hA hB
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
def Row2.QMu (μ z : ℝ) : Prop := ∃ q₁ q₂ : ℚ, z = q₁ + q₂ * μ
theorem Row2.QMu.rat (μ : ℝ) (q : ℚ) : Row2.QMu μ q := ⟨q, 0, by simp⟩
theorem Row2.QMu.nat (μ : ℝ) (n : ℕ) : Row2.QMu μ n := ⟨n, 0, by simp⟩
theorem Row2.QMu.mu (μ : ℝ) : Row2.QMu μ μ := ⟨0, 1, by simp⟩
theorem Row2.QMu.add {μ z w : ℝ} (hz : Row2.QMu μ z) (hw : Row2.QMu μ w) : Row2.QMu μ (z + w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a + c, b + d, by push_cast; ring⟩
theorem Row2.QMu.sub {μ z w : ℝ} (hz : Row2.QMu μ z) (hw : Row2.QMu μ w) : Row2.QMu μ (z - w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a - c, b - d, by push_cast; ring⟩
theorem Row2.QMu.mul {μ z w : ℝ} {p : ℤ} (hp : μ ^ 2 = p) (hz : Row2.QMu μ z)
    (hw : Row2.QMu μ w) : Row2.QMu μ (z * w) := by
  obtain ⟨a, b, rfl⟩ := hz
  obtain ⟨c, d, rfl⟩ := hw
  exact ⟨a * c + b * d * p, a * d + b * c, by push_cast; linear_combination ((b : ℝ) * d) * hp⟩
theorem Row2.QMu.inv {μ z : ℝ} {p : ℤ} (hμ : ¬ ∃ r : ℚ, μ = r) (hp : μ ^ 2 = p)
    (hz : Row2.QMu μ z) : Row2.QMu μ z⁻¹ := by
  obtain ⟨a, b, rfl⟩ := hz
  by_cases h0 : (a : ℝ) + b * μ = 0
  · rw [h0, inv_zero]; exact ⟨0, 0, by simp⟩
  have hn : (a : ℝ) ^ 2 - p * b ^ 2 ≠ 0 := by
    intro hn
    have e : ((a : ℝ) + b * μ) * ((a : ℝ) - b * μ) = 0 := by linear_combination hn - (b : ℝ) ^ 2 * hp
    have e2 := (mul_eq_zero.mp e).resolve_left h0
    by_cases hb : b = 0
    · subst hb; apply h0; simp at e2 ⊢; exact_mod_cast e2
    · apply hμ
      refine ⟨a / b, ?_⟩
      have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
      push_cast
      rw [eq_div_iff hb']
      linarith
  have hnq : ((a ^ 2 - p * b ^ 2 : ℚ) : ℝ) ≠ 0 := by push_cast; exact hn
  have hnq0 : (a ^ 2 - p * b ^ 2 : ℚ) ≠ 0 := fun h => hnq (by rw [h, Rat.cast_zero])
  have hprod : ((a : ℝ) + b * μ) * ((a : ℝ) - b * μ) = ((a ^ 2 - p * b ^ 2 : ℚ) : ℝ) := by
    push_cast; linear_combination (-(b : ℝ) ^ 2) * hp
  have hinv : ((a : ℝ) + b * μ)⁻¹ = ((a : ℝ) - b * μ) * (((1 / (a ^ 2 - p * b ^ 2)) : ℚ) : ℝ) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hprod, ← Rat.cast_mul, mul_one_div_cancel hnq0, Rat.cast_one]
  rw [hinv]
  exact ((Row2.QMu.rat μ a).sub ((Row2.QMu.rat μ b).mul hp (Row2.QMu.mu μ))).mul hp
    (Row2.QMu.rat μ _)
theorem Row2.QMu.div {μ z w : ℝ} {p : ℤ} (hμ : ¬ ∃ r : ℚ, μ = r) (hp : μ ^ 2 = p)
    (hz : Row2.QMu μ z) (hw : Row2.QMu μ w) : Row2.QMu μ (z / w) := by
  rw [div_eq_mul_inv]; exact hz.mul hp (hw.inv hμ hp)
theorem Row2.par_cross {r₀ r₁ r₂ s₀ s₁ s₂ v₀ v₁ v₂ : ℝ}
    (hr : r₀ * v₀ + r₁ * v₁ + r₂ * v₂ = 0) (hs : s₀ * v₀ + s₁ * v₁ + s₂ * v₂ = 0) :
    v₀ * (r₂ * s₀ - r₀ * s₂) = v₁ * (r₁ * s₂ - r₂ * s₁) ∧
    v₀ * (r₀ * s₁ - r₁ * s₀) = v₂ * (r₁ * s₂ - r₂ * s₁) ∧
    v₁ * (r₀ * s₁ - r₁ * s₀) = v₂ * (r₂ * s₀ - r₀ * s₂) :=
  ⟨by linear_combination r₂ * hs - s₂ * hr, by linear_combination s₁ * hr - r₁ * hs,
    by linear_combination r₀ * hs - s₀ * hr⟩
theorem Row2.ratio_of_par {c₀ c₁ c₂ v₀ v₁ v₂ : ℝ} (hv₂ : 0 < v₂)
    (h01 : v₀ * c₁ = v₁ * c₀) (h02 : v₀ * c₂ = v₂ * c₀) (h12 : v₁ * c₂ = v₂ * c₁)
    (hc : c₀ ≠ 0 ∨ c₁ ≠ 0 ∨ c₂ ≠ 0) : c₂ ≠ 0 ∧ v₀ / v₂ = c₀ / c₂ ∧ v₁ / v₂ = c₁ / c₂ := by
  have hc₂ : c₂ ≠ 0 := by
    intro h
    rw [h, mul_zero] at h02 h12
    have e0 : c₀ = 0 := (mul_eq_zero.mp h02.symm).resolve_left hv₂.ne'
    have e1 : c₁ = 0 := (mul_eq_zero.mp h12.symm).resolve_left hv₂.ne'
    rcases hc with h' | h' | h'
    · exact h' e0
    · exact h' e1
    · exact h' h
  refine ⟨hc₂, ?_, ?_⟩
  · rw [div_eq_div_iff hv₂.ne' hc₂]; linarith
  · rw [div_eq_div_iff hv₂.ne' hc₂]; linarith
theorem Row2.lemmaK (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i) {μ : ℝ}
    (hμ : ¬ ∃ r : ℚ, μ = r) {p : ℤ} (hp : μ ^ 2 = p)
    (hDv : ∀ i, ∑ j, (D i j : ℝ) * v j = μ * v i) :
    Row2.QMu μ (v 0 / v 2) ∧ Row2.QMu μ (v 1 / v 2) ∧
      ¬ ((∃ r : ℚ, v 0 = r * v 2) ∧ (∃ r : ℚ, v 1 = r * v 2)) := by
  have E0 := hDv 0
  have E1 := hDv 1
  have E2 := hDv 2
  rw [Fin.sum_univ_three] at E0 E1 E2
  have R0 : ((D 0 0 : ℝ) - μ) * v 0 + (D 0 1 : ℝ) * v 1 + (D 0 2 : ℝ) * v 2 = 0 := by
    linear_combination E0
  have R1 : (D 1 0 : ℝ) * v 0 + ((D 1 1 : ℝ) - μ) * v 1 + (D 1 2 : ℝ) * v 2 = 0 := by
    linear_combination E1
  have R2 : (D 2 0 : ℝ) * v 0 + (D 2 1 : ℝ) * v 1 + ((D 2 2 : ℝ) - μ) * v 2 = 0 := by
    linear_combination E2
  have q := fun (i j : Fin 3) => Row2.QMu.nat μ (D i j)
  have qd := fun (i : Fin 3) => (Row2.QMu.nat μ (D i i)).sub (Row2.QMu.mu μ)
  have hdet : (((D 0 0 : ℝ) - μ) * (((D 1 1 : ℝ) - μ) * ((D 2 2 : ℝ) - μ) - (D 1 2 : ℝ) * D 2 1)
      - (D 0 1 : ℝ) * ((D 1 0 : ℝ) * ((D 2 2 : ℝ) - μ) - (D 1 2 : ℝ) * D 2 0)
      + (D 0 2 : ℝ) * ((D 1 0 : ℝ) * D 2 1 - ((D 1 1 : ℝ) - μ) * D 2 0)) * v 2 = 0 := by
    linear_combination ((D 1 0 : ℝ) * D 2 1 - ((D 1 1 : ℝ) - μ) * D 2 0) * R0
      - (((D 0 0 : ℝ) - μ) * D 2 1 - (D 0 1 : ℝ) * D 2 0) * R1
      + (((D 0 0 : ℝ) - μ) * ((D 1 1 : ℝ) - μ) - (D 0 1 : ℝ) * D 1 0) * R2
  have hdet' := (mul_eq_zero.mp hdet).resolve_right (hv 2).ne'
  have e : (((-p - ((D 0 0 : ℤ) * D 1 1 + (D 0 0 : ℤ) * D 2 2 + (D 1 1 : ℤ) * D 2 2
        - (D 1 2 : ℤ) * D 2 1 - (D 0 1 : ℤ) * D 1 0 - (D 0 2 : ℤ) * D 2 0)) : ℤ) : ℝ) * μ
      + ((((D 0 0 : ℤ) + D 1 1 + D 2 2) * p
        + ((D 0 0 : ℤ) * D 1 1 * D 2 2 - (D 0 0 : ℤ) * D 1 2 * D 2 1 - (D 0 1 : ℤ) * D 1 0 * D 2 2
          + (D 0 1 : ℤ) * D 1 2 * D 2 0 + (D 0 2 : ℤ) * D 1 0 * D 2 1
          - (D 0 2 : ℤ) * D 1 1 * D 2 0) : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination hdet' + (μ - ((D 0 0 : ℝ) + D 1 1 + D 2 2)) * hp
  obtain ⟨hS, -⟩ := irr_coord_eq_zero hμ e
  have hS' := congrArg (fun z : ℤ => (z : ℝ)) hS
  push_cast at hS'
  have hminor : ((D 1 1 : ℝ) - μ) * ((D 2 2 : ℝ) - μ) - (D 1 2 : ℝ) * D 2 1 ≠ 0 ∨
      (D 0 2 : ℝ) * D 2 0 - ((D 0 0 : ℝ) - μ) * ((D 2 2 : ℝ) - μ) ≠ 0 ∨
      ((D 0 0 : ℝ) - μ) * ((D 1 1 : ℝ) - μ) - (D 0 1 : ℝ) * D 1 0 ≠ 0 := by
    by_contra hall
    push Not at hall
    obtain ⟨h12, h02, h01⟩ := hall
    have e2 : (((-2 * ((D 0 0 : ℤ) + D 1 1 + D 2 2)) : ℤ) : ℝ) * μ + (((2 * p) : ℤ) : ℝ) = 0 := by
      push_cast
      linear_combination h12 - h02 + h01 - 3 * hp + hS'
    obtain ⟨hT, hp0⟩ := irr_coord_eq_zero hμ e2
    have hp00 : p = 0 := by omega
    rw [hp00, Int.cast_zero] at hp
    have hμ0 : μ = 0 := (pow_eq_zero_iff two_ne_zero).mp hp
    exact hμ ⟨0, by rw [hμ0]; simp⟩
  rcases hminor with hm | hm | hm
  · 
    obtain ⟨h01, h02, h12⟩ := Row2.par_cross R1 R2
    obtain ⟨-, k0, k1⟩ := Row2.ratio_of_par (hv 2) h01 h02 h12 (Or.inl hm)
    refine ⟨?_, ?_, ?_⟩
    · rw [k0]
      exact (((qd 1).mul hp (qd 2)).sub ((q 1 2).mul hp (q 2 1))).div hμ hp
        (((q 1 0).mul hp (q 2 1)).sub ((qd 1).mul hp (q 2 0)))
    · rw [k1]
      exact (((q 1 2).mul hp (q 2 0)).sub ((q 1 0).mul hp (qd 2))).div hμ hp
        (((q 1 0).mul hp (q 2 1)).sub ((qd 1).mul hp (q 2 0)))
    · rintro ⟨⟨r₀, hr₀⟩, ⟨r₁, hr₁⟩⟩
      apply hμ
      refine ⟨(D 2 0 : ℚ) * r₀ + (D 2 1 : ℚ) * r₁ + (D 2 2 : ℚ), ?_⟩
      have : v 2 * ((D 2 0 : ℝ) * r₀ + (D 2 1 : ℝ) * r₁ + (D 2 2 : ℝ) - μ) = 0 := by
        rw [hr₀, hr₁] at R2; linear_combination R2
      have := (mul_eq_zero.mp this).resolve_left (hv 2).ne'
      push_cast; linarith
  · 
    obtain ⟨h01, h02, h12⟩ := Row2.par_cross R0 R2
    obtain ⟨-, k0, k1⟩ := Row2.ratio_of_par (hv 2) h01 h02 h12 (Or.inr (Or.inl hm))
    refine ⟨?_, ?_, ?_⟩
    · rw [k0]
      exact (((q 0 1).mul hp (qd 2)).sub ((q 0 2).mul hp (q 2 1))).div hμ hp
        (((qd 0).mul hp (q 2 1)).sub ((q 0 1).mul hp (q 2 0)))
    · rw [k1]
      exact (((q 0 2).mul hp (q 2 0)).sub ((qd 0).mul hp (qd 2))).div hμ hp
        (((qd 0).mul hp (q 2 1)).sub ((q 0 1).mul hp (q 2 0)))
    · rintro ⟨⟨r₀, hr₀⟩, ⟨r₁, hr₁⟩⟩
      apply hμ
      refine ⟨(D 2 0 : ℚ) * r₀ + (D 2 1 : ℚ) * r₁ + (D 2 2 : ℚ), ?_⟩
      have : v 2 * ((D 2 0 : ℝ) * r₀ + (D 2 1 : ℝ) * r₁ + (D 2 2 : ℝ) - μ) = 0 := by
        rw [hr₀, hr₁] at R2; linear_combination R2
      have := (mul_eq_zero.mp this).resolve_left (hv 2).ne'
      push_cast; linarith
  · 
    obtain ⟨h01, h02, h12⟩ := Row2.par_cross R0 R1
    obtain ⟨-, k0, k1⟩ := Row2.ratio_of_par (hv 2) h01 h02 h12 (Or.inr (Or.inr hm))
    refine ⟨?_, ?_, ?_⟩
    · rw [k0]
      exact (((q 0 1).mul hp (q 1 2)).sub ((q 0 2).mul hp (qd 1))).div hμ hp
        (((qd 0).mul hp (qd 1)).sub ((q 0 1).mul hp (q 1 0)))
    · rw [k1]
      exact (((q 0 2).mul hp (q 1 0)).sub ((qd 0).mul hp (q 1 2))).div hμ hp
        (((qd 0).mul hp (qd 1)).sub ((q 0 1).mul hp (q 1 0)))
    · rintro ⟨⟨r₀, hr₀⟩, ⟨r₁, hr₁⟩⟩
      apply hμ
      refine ⟨(D 2 0 : ℚ) * r₀ + (D 2 1 : ℚ) * r₁ + (D 2 2 : ℚ), ?_⟩
      have : v 2 * ((D 2 0 : ℝ) * r₀ + (D 2 1 : ℝ) * r₁ + (D 2 2 : ℝ) - μ) = 0 := by
        rw [hr₀, hr₁] at R2; linear_combination R2
      have := (mul_eq_zero.mp this).resolve_left (hv 2).ne'
      push_cast; linarith
theorem Row2.lemmaK_cos (D : Fin 3 → Fin 3 → ℕ) (v : Fin 3 → ℝ) (hv : ∀ i, 0 < v i) {μ : ℝ}
    (hμ : ¬ ∃ r : ℚ, μ = r) {p : ℤ} (hp : μ ^ 2 = p)
    (hDv : ∀ i, ∑ j, (D i j : ℝ) * v j = μ * v i) :
    Row2.QMu μ ((v 1 ^ 2 + v 2 ^ 2 - v 0 ^ 2) / (2 * v 1 * v 2)) ∧
    Row2.QMu μ ((v 2 ^ 2 + v 0 ^ 2 - v 1 ^ 2) / (2 * v 2 * v 0)) ∧
    Row2.QMu μ ((v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2) / (2 * v 0 * v 1)) := by
  obtain ⟨h0, h1, -⟩ := Row2.lemmaK D v hv hμ hp hDv
  set t₀ := v 0 / v 2 with ht₀
  set t₁ := v 1 / v 2 with ht₁
  have hv2 := (hv 2).ne'
  have e₀ : v 0 = t₀ * v 2 := by rw [ht₀, div_mul_cancel₀ _ hv2]
  have e₁ : v 1 = t₁ * v 2 := by rw [ht₁, div_mul_cancel₀ _ hv2]
  have one : Row2.QMu μ 1 := by simpa using Row2.QMu.nat μ 1
  have two : Row2.QMu μ 2 := by simpa using Row2.QMu.nat μ 2
  have ht0 : t₀ ≠ 0 := div_ne_zero (hv 0).ne' hv2
  have ht1 : t₁ ≠ 0 := div_ne_zero (hv 1).ne' hv2
  refine ⟨?_, ?_, ?_⟩
  · have : (v 1 ^ 2 + v 2 ^ 2 - v 0 ^ 2) / (2 * v 1 * v 2) = (t₁ * t₁ + 1 - t₀ * t₀) / (2 * t₁) := by
      rw [e₀, e₁]; field_simp
    rw [this]
    exact (((h1.mul hp h1).add one).sub (h0.mul hp h0)).div hμ hp (two.mul hp h1)
  · have : (v 2 ^ 2 + v 0 ^ 2 - v 1 ^ 2) / (2 * v 2 * v 0) = (1 + t₀ * t₀ - t₁ * t₁) / (2 * t₀) := by
      rw [e₀, e₁]; field_simp
    rw [this]
    exact ((one.add (h0.mul hp h0)).sub (h1.mul hp h1)).div hμ hp (two.mul hp h0)
  · have : (v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2) / (2 * v 0 * v 1)
        = (t₀ * t₀ + t₁ * t₁ - 1) / (2 * t₀ * t₁) := by
      rw [e₀, e₁]; field_simp
    rw [this]
    exact (((h0.mul hp h0).add (h1.mul hp h1)).sub one).div hμ hp ((two.mul hp h0).mul hp h1)
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open Real Polynomial
def Row2.cheb {R : Type*} [CommRing R] (z : R) : ℕ → R
  | 0 => 2
  | 1 => z
  | (k + 2) => z * Row2.cheb z (k + 1) - Row2.cheb z k
theorem Row2.cheb_cos (θ : ℝ) : ∀ k : ℕ, Row2.cheb (2 * Real.cos θ) k = 2 * Real.cos (k * θ)
  | 0 => by simp [Row2.cheb]
  | 1 => by simp [Row2.cheb]
  | (k + 2) => by
      rw [Row2.cheb, Row2.cheb_cos θ (k + 1), Row2.cheb_cos θ k]
      have key : Real.cos (((k : ℝ) + 1) * θ + θ) + Real.cos (((k : ℝ) + 1) * θ - θ)
          = 2 * Real.cos (((k : ℝ) + 1) * θ) * Real.cos θ := by
        rw [Real.cos_add, Real.cos_sub]; ring
      have e1 : ((k : ℝ) + 1) * θ + θ = ((k + 2 : ℕ) : ℝ) * θ := by push_cast; ring
      have e2 : ((k : ℝ) + 1) * θ - θ = (k : ℝ) * θ := by ring
      rw [e1, e2] at key
      push_cast at key ⊢
      linear_combination (-2 : ℝ) * key
theorem Row2.cheb_add_inv (t : ℝ) (ht : t ≠ 0) :
    ∀ k : ℕ, Row2.cheb (t + t⁻¹) k = t ^ k + t⁻¹ ^ k
  | 0 => by simp [Row2.cheb]; norm_num
  | 1 => by simp [Row2.cheb]
  | (k + 2) => by
      rw [Row2.cheb, Row2.cheb_add_inv t ht (k + 1), Row2.cheb_add_inv t ht k]
      have h : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
      linear_combination (t ^ k + t⁻¹ ^ k) * h
theorem Row2.cheb_conj {s : ℝ} {p : ℚ} (hs : s ^ 2 = p) (a b : ℚ) :
    ∀ k : ℕ, ∃ A B : ℚ, Row2.cheb ((a : ℝ) + b * s) k = A + B * s ∧
      Row2.cheb ((a : ℝ) - b * s) k = A - B * s
  | 0 => ⟨2, 0, by simp [Row2.cheb], by simp [Row2.cheb]⟩
  | 1 => ⟨a, b, by simp [Row2.cheb], by simp [Row2.cheb]⟩
  | (k + 2) => by
      obtain ⟨A1, B1, h1, h1'⟩ := Row2.cheb_conj hs a b (k + 1)
      obtain ⟨A0, B0, h0, h0'⟩ := Row2.cheb_conj hs a b k
      refine ⟨a * A1 + b * B1 * p - A0, a * B1 + b * A1 - B0, ?_, ?_⟩
      · rw [Row2.cheb, h1, h0]; push_cast; linear_combination ((b : ℝ) * B1) * hs
      · rw [Row2.cheb, h1', h0']; push_cast; linear_combination ((b : ℝ) * B1) * hs
theorem Row2.poly_conj {s : ℝ} {p : ℚ} (hs : s ^ 2 = p) (a b : ℚ) (P : ℤ[X]) :
    ∃ A B : ℚ, P.eval₂ (algebraMap ℤ ℝ) ((a : ℝ) + b * s) = A + B * s ∧
      P.eval₂ (algebraMap ℤ ℝ) ((a : ℝ) - b * s) = A - B * s := by
  induction P using Polynomial.induction_on with
  | C c => exact ⟨c, 0, by rw [Polynomial.eval₂_C]; simp, by rw [Polynomial.eval₂_C]; simp⟩
  | add P Q hP hQ =>
    obtain ⟨A1, B1, h1, h1'⟩ := hP
    obtain ⟨A2, B2, h2, h2'⟩ := hQ
    refine ⟨A1 + A2, B1 + B2, ?_, ?_⟩
    · rw [Polynomial.eval₂_add, h1, h2]; push_cast; ring
    · rw [Polynomial.eval₂_add, h1', h2']; push_cast; ring
  | monomial n c h =>
    obtain ⟨A, B, h1, h1'⟩ := h
    have hstep : ∀ z : ℝ, (C c * X ^ (n + 1)).eval₂ (algebraMap ℤ ℝ) z
        = (C c * X ^ n).eval₂ (algebraMap ℤ ℝ) z * z := by
      intro z; simp [Polynomial.eval₂_mul, pow_succ, mul_assoc]
    refine ⟨A * a + B * b * p, A * b + B * a, ?_, ?_⟩
    · rw [hstep, h1]; push_cast; linear_combination ((B : ℝ) * b) * hs
    · rw [hstep, h1']; push_cast; linear_combination ((B : ℝ) * b) * hs
theorem Row2.exists_add_inv {y : ℝ} (hy : 2 < |y|) : ∃ t : ℝ, t ≠ 0 ∧ 1 < |t| ∧ t + t⁻¹ = y := by
  have hd : 0 ≤ y ^ 2 - 4 := by
    have : 4 < y ^ 2 := by
      have h2 : (2 : ℝ) ^ 2 < |y| ^ 2 := by
        exact pow_lt_pow_left₀ hy (by norm_num) two_ne_zero
      rw [sq_abs] at h2; linarith
    linarith
  set r := √(y ^ 2 - 4) with hr
  have hr2 : r * r = y ^ 2 - 4 := Real.mul_self_sqrt hd
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  rcases lt_abs.mp hy with h | h
  · 
    refine ⟨(y + r) / 2, by positivity, ?_, ?_⟩
    · rw [abs_of_pos (by positivity)]; linarith
    · have hinv : ((y + r) / 2)⁻¹ = (y - r) / 2 :=
        inv_eq_of_mul_eq_one_right (by linear_combination (-1 / 4 : ℝ) * hr2)
      rw [hinv]; ring
  · 
    have hneg : (y - r) / 2 < -1 := by linarith
    refine ⟨(y - r) / 2, by linarith, ?_, ?_⟩
    · rw [abs_of_neg (by linarith)]; linarith
    · have hne : (y - r) / 2 ≠ 0 := by linarith
      have hinv : ((y - r) / 2)⁻¹ = (y + r) / 2 :=
        inv_eq_of_mul_eq_one_right (by linear_combination (-1 / 4 : ℝ) * hr2)
      rw [hinv]; ring
theorem Row2.abs_le_two_of_cheb {y : ℝ} {n : ℕ} (hn : 0 < n) (h : Row2.cheb y n = 2) : |y| ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨t, ht0, ht1, rfl⟩ := Row2.exists_add_inv hc
  rw [Row2.cheb_add_inv t ht0 n, inv_pow] at h
  have hw0 : t ^ n ≠ 0 := pow_ne_zero n ht0
  have hw : t ^ n = 1 := by
    have h2 : (t ^ n - 1) ^ 2 = 0 := by
      have e : t ^ n * (t ^ n)⁻¹ = 1 := mul_inv_cancel₀ hw0
      linear_combination (t ^ n) * h - e
    have := pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h2
    linarith
  have habs : |t| ^ n = 1 := by rw [← abs_pow, hw, abs_one]
  have := one_lt_pow₀ ht1 hn.ne'
  linarith
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
open Real
variable {N : ℕ}
noncomputable def CongruentDissection.eType (D : CongruentDissection N) (e : Fin N × Fin 3) :
    Fin 3 :=
  (D.eLen_mem e).choose
theorem CongruentDissection.eLen_eType (D : CongruentDissection N) (e : Fin N × Fin 3) :
    D.eLen e = D.model.oppLen (D.eType e) :=
  (D.eLen_mem e).choose_spec
noncomputable def CongruentDissection.sideCountT (D : CongruentDissection N) (i k : Fin 3) : ℕ :=
  ((D.sideEdges (i + 1)).filter (fun e => D.eType e = k)).card
theorem CongruentDissection.sideCountT_sum (D : CongruentDissection N) (i : Fin 3) :
    ∑ k, (D.sideCountT i k : ℝ) * D.model.oppLen k = D.target.oppLen i := by
  have hlen := D.toDissection.side_len_sum (i + 1)
  have hopp : D.target.oppLen i = dist (D.target.pts (i + 1)) (D.target.pts (i + 1 + 1)) := by
    unfold Tri.oppLen
    rw [show i + 1 + 1 = i + 2 by fin_cases i <;> rfl]
  rw [hopp, ← hlen]
  have hsplit : ∀ e ∈ D.sideEdges (i + 1), D.eLen e
      = ∑ k, if D.eType e = k then D.model.oppLen k else 0 := by
    intro e _
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    exact D.eLen_eType e
  rw [Finset.sum_congr rfl hsplit, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold CongruentDissection.sideCountT
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
theorem Row2.sideCountT_eigen (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) (i : Fin 3) :
    ∑ j, (D.sideCountT i j : ℝ) * D.model.oppLen j = μ * D.model.oppLen i := by
  rw [D.sideCountT_sum i, hside i]
theorem Row2.lemmaK_general (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) (hN : ¬ IsSquare N) :
    μ ^ 2 = N ∧
      ¬ ((∃ r : ℚ, D.model.oppLen 0 = r * D.model.oppLen 2) ∧
        (∃ r : ℚ, D.model.oppLen 1 = r * D.model.oppLen 2)) ∧
      ∀ k, Row2.QMu μ (Real.cos (D.model.angleAt k)) := by
  obtain ⟨hμ, hp⟩ := Row2.mu_irrational D μ hside hN
  have hDv := Row2.sideCountT_eigen D μ hside
  obtain ⟨-, -, knot⟩ := Row2.lemmaK D.sideCountT D.model.oppLen D.model.oppLen_pos hμ hp hDv
  obtain ⟨c0, c1, c2⟩ :=
    Row2.lemmaK_cos D.sideCountT D.model.oppLen D.model.oppLen_pos hμ hp hDv
  refine ⟨by exact_mod_cast hp, knot, fun k => ?_⟩
  have hpos := D.model.oppLen_pos
  have hcos : ∀ k, Real.cos (D.model.angleAt k)
      = (D.model.oppLen (k + 1) ^ 2 + D.model.oppLen (k + 2) ^ 2 - D.model.oppLen k ^ 2)
        / (2 * D.model.oppLen (k + 1) * D.model.oppLen (k + 2)) := by
    intro k
    have hl := D.model.lawCos k
    have hne : 2 * D.model.oppLen (k + 1) * D.model.oppLen (k + 2) ≠ 0 :=
      (mul_pos (mul_pos two_pos (hpos _)) (hpos _)).ne'
    rw [eq_div_iff hne]
    linarith
  rw [hcos k]
  fin_cases k
  · exact c0
  · exact c1
  · exact c2
theorem Row2.fin3_pairs : ∀ a b : Fin 3, a ≠ b →
    (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨
      (a = 2 ∧ b = 0) ∨ (a = 2 ∧ b = 1) := by decide
theorem Row2.fin3_triples : ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b →
    (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 0 ∧ b = 2 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 2) ∨
      (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 0) := by decide
theorem Tri.angleAt_add_lt (T : Tri) {i j : Fin 3} (hij : i ≠ j) :
    T.angleAt i + T.angleAt j < π := by
  have hsum := T.angleAt_sum
  have h0 := T.angleAt_pos' 0
  have h1 := T.angleAt_pos' 1
  have h2 := T.angleAt_pos' 2
  rcases Row2.fin3_pairs i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
theorem Tri.angle_eq_of_oppLen_eq (T : Tri) {i j : Fin 3} (hij : i ≠ j)
    (h : T.oppLen i = T.oppLen j) : T.angleAt i = T.angleAt j := by
  have hs := T.lawSin i j
  rw [h] at hs
  have hsin : Real.sin (T.angleAt i) = Real.sin (T.angleAt j) :=
    mul_right_cancel₀ (T.oppLen_pos j).ne' hs
  have hlt := T.angleAt_add_lt hij
  have hi0 := T.angleAt_pos' i
  have hj0 := T.angleAt_pos' j
  by_contra hne
  have hsub := Real.sin_sub_sin (T.angleAt i) (T.angleAt j)
  rw [hsin, sub_self] at hsub
  have hc : 0 < Real.cos ((T.angleAt i + T.angleAt j) / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hs0 : Real.sin ((T.angleAt i - T.angleAt j) / 2) ≠ 0 := by
    rcases lt_or_gt_of_ne hne with hlt' | hgt
    · exact (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)).ne
    · exact (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  exact mul_ne_zero (mul_ne_zero two_ne_zero hs0) hc.ne' hsub.symm
theorem Row2.third_angle (θ : Fin 3 → ℝ) (hsum : θ 0 + θ 1 + θ 2 = π) {i j l : Fin 3}
    (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j) : θ l = π - θ i - θ j := by
  rcases Row2.fin3_triples i j l hij hli hlj with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> linarith
end Erdos634.Geometry
end

section
namespace Erdos634.EdgeDisjoint
open Erdos634.Geometry
theorem exists_pos_dir (T : Tri) (k : Fin 3) : ∃ v : Plane, 0 < (T.basis.coord k).linear v := by
  have h := T.coord_linear_ne_zero k
  obtain ⟨v, hv⟩ : ∃ v, (T.basis.coord k).linear v ≠ 0 := by
    by_contra hc
    exact h (LinearMap.ext (by intro x; by_contra hx; exact hc ⟨x, hx⟩))
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · exact ⟨-v, by simpa using hlt⟩
  · exact ⟨v, hgt⟩
theorem coord_add_smul (f : Plane →ᵃ[ℝ] ℝ) (x v : Plane) (t : ℝ) :
    f (x + t • v) = f x + t * f.linear v := by
  have h : x + t • v = (t • v) +ᵥ x := by simp [vadd_eq_add]; abel
  rw [h, f.map_vadd]
  simp [add_comm]
end Erdos634.EdgeDisjoint
end

section
namespace Erdos634.Geometry.Dissection
variable {N : ℕ}
theorem target_vertex_not_interior (T : Erdos634.Geometry.Tri) (k : Fin 3) :
    T.pts k ∉ interior T.carrier := by
  rw [T.mem_interior_iff_coord_pos]
  push_neg
  refine ⟨k + 1, ?_⟩
  have hne : (k + 1 : Fin 3) ≠ k := by
    have h : ∀ x : Fin 3, x + 1 ≠ x := by decide
    exact h k
  have hz : T.basis.coord (k + 1) (T.pts k) = 0 := by
    have h := T.basis.coord_apply (k + 1) k
    simp only [if_neg hne] at h
    exact h
  rw [hz]
theorem target_vertex_not_interior_tile (D : Dissection N) (k : Fin 3) (i : Fin N) :
    D.target.pts k ∉ interior (D.tile i).carrier := by
  intro h
  exact target_vertex_not_interior D.target k (Erdos634.BaseSelection.tile_interior_subset D i h)
theorem localAngle_ne_two_pi_of_not_mem_interior {T : Erdos634.Geometry.Tri} {p : Plane}
    (hp : p ∉ interior T.carrier) : T.localAngle p ≠ 2 * Real.pi := by
  classical
  intro h2
  rw [Erdos634.Geometry.Tri.localAngle] at h2
  split at h2
  · rename_i hv
    have hle := EuclideanGeometry.angle_le_pi ((T.pts (hv.choose + 1)))
      (T.pts hv.choose) (T.pts (hv.choose + 2))
    have hpi := Real.pi_pos
    rw [Erdos634.Geometry.cornerAngle] at h2
    rw [h2] at hle; linarith
  · split at h2
    · rename_i hall
      exact hp (T.mem_interior_iff_coord_pos p |>.mpr hall)
    · split at h2 <;> [skip; skip] <;>
        first
          | (exfalso; have := Real.pi_pos; linarith)
          | (exfalso; have := Real.pi_pos; linarith)
theorem tile_angle_dichotomy_at_vertex (D : Dissection N) (k : Fin 3) {i : Fin N}
    (hi : D.target.pts k ∈ (D.tile i).carrier) :
    (∃ j : Fin 3, D.target.pts k = (D.tile i).pts j ∧
        (D.tile i).localAngle (D.target.pts k)
          = cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))) ∨
    (D.tile i).localAngle (D.target.pts k) = Real.pi := by
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) (D.target.pts k) with
    hvertex | h2pi | hpi | h0
  · exact Or.inl hvertex
  · exact absurd h2pi (localAngle_ne_two_pi_of_not_mem_interior (D.target_vertex_not_interior_tile k i))
  · exact Or.inr hpi
  · exact absurd h0 (Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hi)
open Erdos634.TilePlacement in
theorem congruentDissection_localAngle_mem (D : CongruentDissection N) (α β γ : ℝ)
    (hα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (k : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
  classical
  by_cases hi : D.target.pts k ∈ (D.tile i).carrier
  · rcases D.toDissection.tile_angle_dichotomy_at_vertex k hi with ⟨j, hjp, hjeq⟩ | hpi
    · obtain ⟨m, hm⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
      rw [hjeq, hm]
      have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hcases with rfl | rfl | rfl
      · left; rw [← hα]; congr 1
      · right; left; rw [← hβ]; congr 1
      · right; right; left; rw [← hγ]; congr 1
    · simp [hpi]
  · 
    have h0 : (D.tile i).localAngle (D.target.pts k) = 0 := by
      classical
      rw [Erdos634.Geometry.Tri.localAngle]
      split
      · rename_i hv
        have hvmem : (D.target.pts k) ∈ Set.range (D.tile i).pts := ⟨hv.choose, hv.choose_spec.symm⟩
        exact absurd (subset_convexHull ℝ _ hvmem) hi
      · split
        · rename_i hall
          have hint : D.target.pts k ∈ interior (D.tile i).carrier :=
            (D.tile i).mem_interior_iff_coord_pos _ |>.mpr hall
          exact absurd (interior_subset hint) hi
        · split
          · rename_i hedge
            obtain ⟨kk, hkk1, hkk2⟩ := hedge
            have hmem : D.target.pts k ∈ (D.tile i).carrier := by
              rw [(D.tile i).carrier_eq_nonneg_coord]
              intro j
              rcases eq_or_ne j kk with rfl | hne
              · exact hkk1.ge
              · exact (hkk2 j hne).le
            exact absurd hmem hi
          · rfl
    simp [h0]
open Erdos634.TilePlacement Erdos634.VertexFigureReal in
theorem congruentDissection_hcorners (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ) :
    ∀ (i : Fin N) (j : Fin 3),
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        ∈ ({α, β, γ} : Finset ℝ) := by
  intro i j
  obtain ⟨m, hm⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
  rw [hm]
  fin_cases m
  · simp [hα']
  · simp [hβ']
  · simp [hγ']
open Erdos634.VertexFigureReal in
theorem congruentDissection_localAngle_mem_boundary (D : CongruentDissection N) (α β γ : ℝ)
    (hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (hv : v ∈ frontier D.target.carrier) (hnv : v ∉ Set.range D.target.pts)
    (i : Fin N) : (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
  localAngle_mem D.toDissection α β γ hv hnv (congruentDissection_hcorners D α β γ hα' hβ' hγ') i
end Erdos634.Geometry.Dissection
end

section
open scoped Classical
namespace Erdos634.Geometry
open Real
variable {N : ℕ}
theorem Row2.fin3_ne_add_two : ∀ m k : Fin 3, m ≠ k + 2 → m = k ∨ m = k + 1 := by decide
theorem Tri.vertex_mem_edge (T : Tri) {m k : Fin 3} (h : T.pts m ∈ T.edge k) :
    m = k ∨ m = k + 1 := by
  have h0 := T.coord_eq_zero_of_mem_edge k h
  have hb : T.pts m = (T.basis : Fin 3 → Plane) m := rfl
  rw [hb, AffineBasis.coord_apply] at h0
  refine Row2.fin3_ne_add_two m k fun hmk => ?_
  rw [if_pos hmk.symm] at h0
  exact one_ne_zero h0
theorem Dissection.eLen_eq_oppLen (D : Dissection N) (e : Fin N × Fin 3) :
    D.eLen e = (D.tile e.1).oppLen (e.2 + 2) := by
  have h : ∀ k : Fin 3, k + 2 + 1 = k ∧ k + 2 + 2 = k + 1 := by decide
  unfold Dissection.eLen Tri.oppLen
  rw [(h e.2).1, (h e.2).2]
theorem Dissection.exists_sideEdge_mem (D : Dissection N) (j : Fin 3) {y : Plane}
    (hy : y ∈ D.target.edge j) : ∃ e ∈ D.sideEdges j, y ∈ D.eSet e := by
  obtain ⟨part, hpart⟩ := hasEdgeChains_edge D j
  have hy' := (Set.ext_iff.mp hpart y).mpr hy
  obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.mp hy'
  refine ⟨e, ?_, hye⟩
  unfold Dissection.sideEdges
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, fun z hz => ?_⟩
  exact (Set.ext_iff.mp hpart z).mp (Set.mem_iUnion₂.mpr ⟨e, he, hz⟩)
theorem Row2.sideCount_pos (D : CongruentDissection N) {i k : Fin 3} {e : Fin N × Fin 3}
    (he : e ∈ D.sideEdges (i + 1)) (hl : D.eLen e = D.model.oppLen k) : 0 < D.sideCount i k :=
  Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hl⟩⟩
theorem Row2.corner_edges (D : CongruentDissection N) (t m0 : Fin 3)
    (hdist : ∀ i j : Fin 3, i ≠ j → D.model.angleAt i ≠ D.model.angleAt j)
    (i0 : Fin N) (hi0 : (D.tile i0).localAngle (D.target.pts t) = D.model.angleAt m0)
    (hother : ∀ i, i ≠ i0 → (D.tile i).localAngle (D.target.pts t) = 0) :
    ∃ k1 k2 : Fin 3, k1 ≠ m0 ∧ k2 ≠ m0 ∧ k1 ≠ k2 ∧
      (∃ e ∈ D.sideEdges t, D.eLen e = D.model.oppLen k1) ∧
      (∃ e ∈ D.sideEdges (t + 2), D.eLen e = D.model.oppLen k2) := by
  have hθ0 : 0 < D.model.angleAt m0 := D.model.angleAt_pos' m0
  have hθπ : D.model.angleAt m0 < π := by
    have hne : m0 ≠ m0 + 1 := by
      have : ∀ a : Fin 3, a ≠ a + 1 := by decide
      exact this m0
    have := D.model.angleAt_add_lt hne
    linarith [D.model.angleAt_pos' (m0 + 1)]
  obtain ⟨jv, hjv, hang⟩ : ∃ jv : Fin 3, D.target.pts t = (D.tile i0).pts jv ∧
      (D.tile i0).angleAt jv = D.model.angleAt m0 := by
    rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i0) (D.target.pts t) with
      ⟨j, hj, hjl⟩ | h | h | h
    · exact ⟨j, hj, by rw [← hi0, hjl]; rfl⟩
    · rw [hi0] at h; linarith [Real.pi_pos]
    · rw [hi0] at h; linarith
    · rw [hi0] at h; linarith
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i0).exists_perm
  have hσjv : σ jv = m0 := by
    by_contra hne
    exact hdist _ _ hne (by rw [← (hσ jv).1, hang])
  have side : ∀ j : Fin 3, D.target.pts t ∈ D.target.edge j → ∃ e ∈ D.sideEdges j,
      D.eLen e = D.model.oppLen (σ (e.2 + 2)) ∧ e.1 = i0 ∧ e.2 + 2 ≠ jv := by
    intro j hPj
    obtain ⟨e, he, hPe⟩ := D.toDissection.exists_sideEdge_mem j hPj
    have hcar : D.target.pts t ∈ (D.tile e.1).carrier :=
      (D.tile e.1).edge_subset_carrier e.2 hPe
    have he1 : e.1 = i0 := by
      by_contra hne
      exact Erdos634.MarchFlank.localAngle_ne_zero_of_mem _ hcar (hother e.1 hne)
    refine ⟨e, he, ?_, he1, ?_⟩
    · rw [D.toDissection.eLen_eq_oppLen e, he1, (hσ _).2]
    · have hmem : (D.tile i0).pts jv ∈ (D.tile i0).edge e.2 := by
        rw [← hjv, ← he1]; exact hPe
      intro h2
      rcases (D.tile i0).vertex_mem_edge hmem with h | h
      · have : ∀ a : Fin 3, a + 2 ≠ a := by decide
        exact this e.2 (h2.trans h)
      · have : ∀ a : Fin 3, a + 2 ≠ a + 1 := by decide
        exact this e.2 (h2.trans h)
  have hPt : D.target.pts t ∈ D.target.edge t := left_mem_segment ℝ _ _
  have hPt2 : D.target.pts t ∈ D.target.edge (t + 2) := by
    have h : ∀ a : Fin 3, a + 2 + 1 = a := by decide
    show D.target.pts t ∈ segment ℝ (D.target.pts (t + 2)) (D.target.pts (t + 2 + 1))
    rw [h t]; exact right_mem_segment ℝ _ _
  obtain ⟨e, he, hel, he1, he2⟩ := side t hPt
  obtain ⟨e', he', hel', he1', he2'⟩ := side (t + 2) hPt2
  have hee : e ≠ e' := by
    intro h
    have htt : t ≠ t + 2 := by
      have : ∀ a : Fin 3, a ≠ a + 2 := by decide
      exact this t
    exact Finset.disjoint_left.mp (D.toDissection.sideEdges_disjoint htt) he (by rw [h]; exact he')
  have h22 : e.2 ≠ e'.2 := fun h => hee (Prod.ext (he1.trans he1'.symm) h)
  refine ⟨σ (e.2 + 2), σ (e'.2 + 2), ?_, ?_, ?_, ⟨e, he, hel⟩, ⟨e', he', hel'⟩⟩
  · intro h; exact he2 (σ.injective (h.trans hσjv.symm))
  · intro h; exact he2' (σ.injective (h.trans hσjv.symm))
  · intro h; exact h22 (add_right_cancel (σ.injective h))
theorem Row2.others_zero (f : Fin N → ℝ) (hnn : ∀ i, 0 ≤ f i) {i0 : Fin N}
    (h : f i0 = ∑ i, f i) : ∀ i, i ≠ i0 → f i = 0 := by
  intro i hi
  have h2 : f i0 + f i ≤ ∑ j, f j := by
    rw [← Finset.sum_pair hi.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hnn j)
  linarith [hnn i]
theorem Row2.fill_min (f : Fin N → ℝ) (φ : ℝ) (hnn : ∀ i, 0 ≤ f i) (hsum : ∑ i, f i = φ)
    (hφ : 0 < φ) (hge : ∀ i, f i ≠ 0 → φ ≤ f i) :
    ∃ i0, f i0 = φ ∧ ∀ i, i ≠ i0 → f i = 0 := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := f)
    (by rw [hsum]; exact hφ.ne')
  have hle : f i0 ≤ φ := by
    rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i0)
  have heq : f i0 = φ := le_antisymm hle (hge i0 hi0)
  exact ⟨i0, heq, Row2.others_zero f hnn (heq.trans hsum.symm)⟩
theorem Row2.fill_mid (f : Fin N → ℝ) {α β γ : ℝ}
    (hvals : ∀ i, f i ∈ ({α, β, γ, π, 0} : Finset ℝ))
    (hα : 0 < α) (hαβ : α < β) (hβγ : β < γ) (hγπ : γ < π) (hsum : ∑ i, f i = β)
    (hmult : ∀ k : ℕ, β ≠ k * α) : ∃ i0, f i0 = β ∧ ∀ i, i ≠ i0 → f i = 0 := by
  have hnn : ∀ i, 0 ≤ f i := by
    intro i
    have hv := hvals i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h | h <;> rw [h] <;> linarith [Real.pi_pos]
  by_cases hex : ∃ i0, f i0 = β
  · obtain ⟨i0, hi0⟩ := hex
    exact ⟨i0, hi0, Row2.others_zero f hnn (hi0.trans hsum.symm)⟩
  · exfalso
    push Not at hex
    have hle : ∀ i, f i ≤ β := fun i => by
      rw [← hsum]; exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    have hsplit : ∀ i, f i = if f i = α then α else 0 := by
      intro i
      have hv := hvals i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      have hi := hle i
      rcases hv with h | h | h | h | h
      · rw [if_pos h, h]
      · exact absurd h (hex i)
      · rw [h] at hi; linarith
      · rw [h] at hi; linarith
      · rw [if_neg (by rw [h]; exact hα.ne), h]
    have hcount : ∑ i, f i = ((Finset.univ.filter (fun i => f i = α)).card : ℝ) * α := by
      rw [Finset.sum_congr rfl (fun i _ => hsplit i), ← Finset.sum_filter, Finset.sum_const,
        nsmul_eq_mul]
    exact hmult _ (hsum.symm.trans hcount)
theorem Row2.corner_sum (D : CongruentDissection N) (t : Fin 3) :
    ∑ i, (D.tile i).localAngle (D.target.pts t) = D.target.angleAt t :=
  (D.toDissection.sum_localAngle_eq _).trans (D.target.localAngle_vertex t)
theorem Row2.corner_vals (D : CongruentDissection N) (t : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts t) ∈
      ({D.model.angleAt 0, D.model.angleAt 1, D.model.angleAt 2, π, 0} : Finset ℝ) :=
  Dissection.congruentDissection_localAngle_mem D _ _ _ rfl rfl rfl t i
theorem Row2.dist_of_lt (T : Tri) (h01 : T.angleAt 0 < T.angleAt 1)
    (h12 : T.angleAt 1 < T.angleAt 2) : ∀ i j : Fin 3, i ≠ j → T.angleAt i ≠ T.angleAt j := by
  intro i j hij h
  rcases Row2.fin3_pairs i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
theorem Row2.angle2_lt_pi (T : Tri) : T.angleAt 2 < π := by
  have := T.angleAt_add_lt (show (2 : Fin 3) ≠ 0 by decide)
  linarith [T.angleAt_pos' 0]
theorem Row2.fin3_others0 : ∀ k1 k2 : Fin 3, k1 ≠ 0 → k2 ≠ 0 → k1 ≠ k2 →
    (k1 = 1 ∧ k2 = 2) ∨ (k1 = 2 ∧ k2 = 1) := by decide
theorem Row2.fin3_others1 : ∀ k1 k2 : Fin 3, k1 ≠ 1 → k2 ≠ 1 → k1 ≠ k2 →
    (k1 = 0 ∧ k2 = 2) ∨ (k1 = 2 ∧ k2 = 0) := by decide
theorem Row2.cornerA (D : CongruentDissection N)
    (hang : ∀ k, D.target.angleAt k = D.model.angleAt k)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2) :
    (0 < D.sideCount 2 1 ∧ 0 < D.sideCount 1 2) ∨ (0 < D.sideCount 2 2 ∧ 0 < D.sideCount 1 1) := by
  have hdist := Row2.dist_of_lt D.model h01 h12
  have h2π := Row2.angle2_lt_pi D.model
  have hge : ∀ i, (D.tile i).localAngle (D.target.pts 0) ≠ 0 →
      D.model.angleAt 0 ≤ (D.tile i).localAngle (D.target.pts 0) := by
    intro i hi
    have hv := Row2.corner_vals D 0 i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with h | h | h | h | h
    · rw [h]
    · rw [h]; linarith
    · rw [h]; linarith
    · rw [h]; linarith
    · exact absurd h hi
  obtain ⟨i0, hi0, hoth⟩ := Row2.fill_min (fun i => (D.tile i).localAngle (D.target.pts 0))
    (D.model.angleAt 0) (fun i => (D.tile i).localAngle_nonneg _)
    (by rw [← hang 0]; exact Row2.corner_sum D 0) (D.model.angleAt_pos' 0) hge
  obtain ⟨k1, k2, hk1, hk2, hk12, ⟨e, he, hel⟩, ⟨e', he', hel'⟩⟩ :=
    Row2.corner_edges D 0 0 hdist i0 hi0 hoth
  have c1 : 0 < D.sideCount 2 k1 := Row2.sideCount_pos D (i := 2) he hel
  have c2 : 0 < D.sideCount 1 k2 := Row2.sideCount_pos D (i := 1) he' hel'
  rcases Row2.fin3_others0 k1 k2 hk1 hk2 hk12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨c1, c2⟩
  · exact Or.inr ⟨c1, c2⟩
theorem Row2.cornerB (D : CongruentDissection N)
    (hang : ∀ k, D.target.angleAt k = D.model.angleAt k)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hmult : ∀ k : ℕ, D.model.angleAt 1 ≠ k * D.model.angleAt 0) :
    (0 < D.sideCount 2 0 ∧ 0 < D.sideCount 0 2) ∨ (0 < D.sideCount 2 2 ∧ 0 < D.sideCount 0 0) := by
  have hdist := Row2.dist_of_lt D.model h01 h12
  obtain ⟨i0, hi0, hoth⟩ := Row2.fill_mid (fun i => (D.tile i).localAngle (D.target.pts 1))
    (Row2.corner_vals D 1) (D.model.angleAt_pos' 0) h01 h12 (Row2.angle2_lt_pi D.model)
    (by rw [← hang 1]; exact Row2.corner_sum D 1) hmult
  obtain ⟨k1, k2, hk1, hk2, hk12, ⟨e, he, hel⟩, ⟨e', he', hel'⟩⟩ :=
    Row2.corner_edges D 1 1 hdist i0 hi0 hoth
  have c1 : 0 < D.sideCount 0 k1 := Row2.sideCount_pos D (i := 0) he hel
  have c2 : 0 < D.sideCount 2 k2 := Row2.sideCount_pos D (i := 2) he' hel'
  rcases Row2.fin3_others1 k1 k2 hk1 hk2 hk12 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨c2, c1⟩
  · exact Or.inl ⟨c2, c1⟩
end Erdos634.Geometry
end

section
namespace Erdos634.SideWall
open Erdos634.Geometry
noncomputable def wallFun (T : Tri) (k : Fin 3) : Plane →ᵃ[ℝ] ℝ := -(T.basis.coord (k + 2))
theorem wallFun_eq_zero (T : Tri) (k : Fin 3) {y : Plane} (hy : y ∈ T.edge k) :
    wallFun T k y = 0 := by
  have hk1 : (k + 2 : Fin 3) ≠ k := by
    have : ∀ x : Fin 3, x + 2 ≠ x := by decide
    exact this k
  have hk2 : (k + 2 : Fin 3) ≠ k + 1 := by
    have : ∀ x : Fin 3, x + 2 ≠ x + 1 := by decide
    exact this k
  have e1 : T.basis.coord (k + 2) (T.pts k) = 0 := by
    have := T.basis.coord_apply (k + 2) k
    simp only [if_neg hk1] at this; exact this
  have e2 : T.basis.coord (k + 2) (T.pts (k + 1)) = 0 := by
    have := T.basis.coord_apply (k + 2) (k + 1)
    simp only [if_neg hk2] at this; exact this
  rw [Tri.edge] at hy
  obtain ⟨u, v, _, _, huv, rfl⟩ := hy
  have hx : u • T.pts k + v • T.pts (k + 1)
      = AffineMap.lineMap (T.pts k) (T.pts (k + 1)) v := by
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_sub]
    have : u = 1 - v := by linarith
    rw [this]; module
  simp only [wallFun, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero]
  rw [hx, AffineMap.apply_lineMap, e1, e2]
  simp
theorem edge_subset_frontier (T : Tri) (k : Fin 3) : T.edge k ⊆ frontier T.carrier := by
  intro x hx
  have hxc : x ∈ T.carrier := T.edge_subset_carrier k hx
  have hcl : IsClosed T.carrier := by
    rw [Tri.carrier]
    exact (Set.finite_range T.pts).isClosed_convexHull (𝕜 := ℝ)
  refine ⟨by rw [hcl.closure_eq]; exact hxc, ?_⟩
  intro hint
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_interior x hint
  obtain ⟨v, hv⟩ := Erdos634.EdgeDisjoint.exists_pos_dir T (k + 2)
  have hvne : v ≠ 0 := by rintro rfl; simp at hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  set t : ℝ := min (r / (2 * ‖v‖)) 1 with ht
  have htpos : 0 < t := lt_min (by positivity) one_pos
  set y : Plane := x + t • (-v) with hy
  have hdist : dist y x < r := by
    have : dist y x = t * ‖v‖ := by
      simp [hy, dist_eq_norm, norm_smul, abs_of_pos htpos]
    rw [this]
    calc t * ‖v‖ ≤ (r / (2 * ‖v‖)) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (le_of_lt hvpos)
      _ = r / 2 := by field_simp
      _ < r := by linarith
  have hyc : y ∈ T.carrier := interior_subset (hsub (Metric.mem_ball.mpr hdist))
  have hx0 : T.basis.coord (k + 2) x = 0 := by
    have := wallFun_eq_zero T k hx
    simpa [wallFun] using this
  have hyneg : T.basis.coord (k + 2) y < 0 := by
    have := Erdos634.EdgeDisjoint.coord_add_smul (T.basis.coord (k + 2)) x (-v) t
    rw [hy, this, hx0]
    simp only [map_neg]
    nlinarith [hv, htpos]
  have : 0 ≤ T.basis.coord (k + 2) y := by
    have h : y ∈ T.carrier := hyc
    rw [T.carrier_eq_nonneg_coord] at h
    exact h (k + 2)
  linarith
end Erdos634.SideWall
end

section
open scoped Classical
namespace Erdos634.Geometry
open Real
variable {N : ℕ}
noncomputable def Row2.tau (T : Tri) (x : Plane) : ℝ := T.basis.coord 1 x
theorem Row2.tau_A (T : Tri) : Row2.tau T (T.pts 0) = 0 :=
  T.basis.coord_apply_ne (show (1 : Fin 3) ≠ 0 by decide)
theorem Row2.tau_B (T : Tri) : Row2.tau T (T.pts 1) = 1 := T.basis.coord_apply_eq 1
theorem Row2.edge0_coord (T : Tri) {x : Plane} (hx : x ∈ T.edge 0) :
    T.basis.coord 2 x = 0 ∧ 0 ≤ T.basis.coord 0 x ∧ 0 ≤ Row2.tau T x ∧
      T.basis.coord 0 x + Row2.tau T x = 1 := by
  have h2 : T.basis.coord 2 x = 0 := T.coord_eq_zero_of_mem_edge 0 hx
  have hc := T.edge_subset_carrier 0 hx
  rw [T.carrier_eq_nonneg_coord] at hc
  have hs := T.basis.sum_coord_apply_eq_one x
  rw [Fin.sum_univ_three, h2] at hs
  exact ⟨h2, hc 0, hc 1, by unfold Row2.tau; linarith⟩
theorem Row2.tau_inj (T : Tri) {x y : Plane} (hx : x ∈ T.edge 0) (hy : y ∈ T.edge 0)
    (h : Row2.tau T x = Row2.tau T y) : x = y := by
  obtain ⟨hx2, -, -, hx1⟩ := Row2.edge0_coord T hx
  obtain ⟨hy2, -, -, hy1⟩ := Row2.edge0_coord T hy
  unfold Row2.tau at h hx1 hy1
  apply T.basis.ext_elem
  intro i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with rfl | rfl | rfl
  · linarith
  · exact h
  · rw [hx2, hy2]
theorem Row2.tau_surj (T : Tri) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    ∃ x ∈ T.edge 0, Row2.tau T x = s := by
  refine ⟨AffineMap.lineMap (T.pts 0) (T.pts 1) s, ?_, ?_⟩
  · show _ ∈ segment ℝ (T.pts 0) (T.pts (0 + 1))
    rw [segment_eq_image_lineMap]
    exact ⟨s, ⟨h0, h1⟩, rfl⟩
  · unfold Row2.tau
    rw [AffineMap.apply_lineMap]
    rw [show T.basis.coord 1 (T.pts 0) = 0 from Row2.tau_A T,
      show T.basis.coord 1 (T.pts 1) = 1 from Row2.tau_B T]
    simp [AffineMap.lineMap_apply]
theorem Row2.tau_image_segment (T : Tri) (X Y : Plane) :
    Row2.tau T '' segment ℝ X Y = Set.uIcc (Row2.tau T X) (Row2.tau T Y) := by
  rw [← segment_eq_uIcc]
  exact image_segment (f := T.basis.coord 1) (a := X) (b := Y)
theorem Row2.mem_seg_iff (T : Tri) {X Y z : Plane} (hseg : segment ℝ X Y ⊆ T.edge 0)
    (hz : z ∈ T.edge 0) :
    z ∈ segment ℝ X Y ↔ Row2.tau T z ∈ Set.uIcc (Row2.tau T X) (Row2.tau T Y) := by
  rw [← Row2.tau_image_segment]
  constructor
  · intro h; exact ⟨z, h, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    rw [← Row2.tau_inj T (hseg hw) hz hwz]; exact hw
theorem Row2.sideEdge_sub (D : Dissection N) {j : Fin 3} {e : Fin N × Fin 3}
    (he : e ∈ D.sideEdges j) : D.eSet e ⊆ D.target.edge j := by
  unfold Dissection.sideEdges at he
  exact (Finset.mem_filter.mp he).2
noncomputable def Row2.lo (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  Row2.tau D.target ((D.tile e.1).pts e.2) ⊓ Row2.tau D.target ((D.tile e.1).pts (e.2 + 1))
noncomputable def Row2.hi (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  Row2.tau D.target ((D.tile e.1).pts e.2) ⊔ Row2.tau D.target ((D.tile e.1).pts (e.2 + 1))
theorem Row2.mem_eSet_iff (D : Dissection N) {e : Fin N × Fin 3} (he : e ∈ D.sideEdges 0)
    {z : Plane} (hz : z ∈ D.target.edge 0) :
    z ∈ D.eSet e ↔ Row2.lo D e ≤ Row2.tau D.target z ∧ Row2.tau D.target z ≤ Row2.hi D e := by
  have h := Row2.mem_seg_iff D.target (X := (D.tile e.1).pts e.2)
    (Y := (D.tile e.1).pts (e.2 + 1)) (Row2.sideEdge_sub D he) hz
  rw [Set.uIcc, Set.mem_Icc] at h
  exact h
theorem Row2.endpoints_mem (D : Dissection N) {e : Fin N × Fin 3} (he : e ∈ D.sideEdges 0) :
    (D.tile e.1).pts e.2 ∈ D.target.edge 0 ∧ (D.tile e.1).pts (e.2 + 1) ∈ D.target.edge 0 :=
  ⟨Row2.sideEdge_sub D he (left_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))),
    Row2.sideEdge_sub D he (right_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))⟩
theorem Row2.lo_hi_bounds (D : Dissection N) {e : Fin N × Fin 3} (he : e ∈ D.sideEdges 0) :
    0 ≤ Row2.lo D e ∧ Row2.hi D e ≤ 1 := by
  obtain ⟨h1, h2⟩ := Row2.endpoints_mem D he
  obtain ⟨-, a0, a1, a2⟩ := Row2.edge0_coord D.target h1
  obtain ⟨-, b0, b1, b2⟩ := Row2.edge0_coord D.target h2
  exact ⟨le_inf a1 b1, sup_le (by linarith) (by linarith)⟩
theorem Row2.lo_lt_hi (D : Dissection N) {e : Fin N × Fin 3} (he : e ∈ D.sideEdges 0) :
    Row2.lo D e < Row2.hi D e := by
  obtain ⟨h1, h2⟩ := Row2.endpoints_mem D he
  have hne : Row2.tau D.target ((D.tile e.1).pts e.2)
      ≠ Row2.tau D.target ((D.tile e.1).pts (e.2 + 1)) := by
    intro h
    have := Row2.tau_inj D.target h1 h2 h
    have hsucc : ∀ i : Fin 3, i ≠ i + 1 := by decide
    exact hsucc e.2 ((D.tile e.1).indep.injective this)
  unfold Row2.lo Row2.hi
  rcases lt_or_gt_of_ne hne with h | h
  · rw [inf_of_le_left h.le, sup_of_le_right h.le]; exact h
  · rw [inf_of_le_right h.le, sup_of_le_left h.le]; exact h
theorem Row2.eq_inf_or_sup (a b : ℝ) : (a = a ⊓ b ∨ a = a ⊔ b) ∧ (b = a ⊓ b ∨ b = a ⊔ b) := by
  rcases le_total a b with h | h
  · exact ⟨Or.inl (inf_of_le_left h).symm, Or.inr (sup_of_le_right h).symm⟩
  · exact ⟨Or.inr (sup_of_le_left h).symm, Or.inl (inf_of_le_right h).symm⟩
theorem Row2.sideEdges_inter_subsingleton (D : Dissection N) (j : Fin 3) {e₁ e₂ : Fin N × Fin 3}
    (h₁ : e₁ ∈ D.sideEdges j) (h₂ : e₂ ∈ D.sideEdges j) (hne : e₁ ≠ e₂) :
    (D.eSet e₁ ∩ D.eSet e₂).Subsingleton := by
  obtain ⟨g, c, hg, hle, hj, hj1, hj2⟩ := exists_supporting D.target j
  have hS : {x ∈ D.target.carrier | g x = c} = D.target.edge j :=
    target_contact_side D.target g c hle hj hj1 hj2
  have hon : ∀ e ∈ D.sideEdges j, ∀ y ∈ (D.tile e.1).edge e.2, g y = c := by
    intro e he y hy
    have hy' : y ∈ {x ∈ D.target.carrier | g x = c} := by
      rw [hS]; exact Row2.sideEdge_sub D he hy
    exact hy'.2
  have hleT : ∀ e : Fin N × Fin 3, ∀ y ∈ (D.tile e.1).carrier, g y ≤ c :=
    fun e y hy => hle y (tile_subset_target D e.1 hy)
  exact D.sameside_edges_subsingleton g c hg hne (hleT e₁) (hleT e₂) (hon e₁ h₁) (hon e₂ h₂)
theorem Row2.interiors_disjoint (D : Dissection N) {e e' : Fin N × Fin 3}
    (he : e ∈ D.sideEdges 0) (he' : e' ∈ D.sideEdges 0) (hne : e ≠ e') {s : ℝ}
    (h1 : Row2.lo D e < s) (h2 : s < Row2.hi D e) (h3 : Row2.lo D e' < s) (h4 : s < Row2.hi D e') :
    False := by
  obtain ⟨hl0, hh1⟩ := Row2.lo_hi_bounds D he
  have hu : max (Row2.lo D e) (Row2.lo D e') < s := max_lt h1 h3
  have hm1 := le_max_left (Row2.lo D e) (Row2.lo D e')
  have hm2 := le_max_right (Row2.lo D e) (Row2.lo D e')
  obtain ⟨z1, hz1, hz1t⟩ := Row2.tau_surj D.target
    (s := (max (Row2.lo D e) (Row2.lo D e') + s) / 2) (by linarith) (by linarith)
  obtain ⟨z, hz, hzt⟩ := Row2.tau_surj D.target (s := s) (by linarith) (by linarith)
  have m1 : z1 ∈ D.eSet e := (Row2.mem_eSet_iff D he hz1).mpr ⟨by linarith, by linarith⟩
  have m1' : z1 ∈ D.eSet e' := (Row2.mem_eSet_iff D he' hz1).mpr ⟨by linarith, by linarith⟩
  have m2 : z ∈ D.eSet e := (Row2.mem_eSet_iff D he hz).mpr ⟨by linarith, by linarith⟩
  have m2' : z ∈ D.eSet e' := (Row2.mem_eSet_iff D he' hz).mpr ⟨by linarith, by linarith⟩
  have := Row2.sideEdges_inter_subsingleton D 0 he he' hne ⟨m1, m1'⟩ ⟨m2, m2'⟩
  rw [this] at hz1t
  linarith
theorem Row2.distinct_tiles (D : Dissection N) {e e' : Fin N × Fin 3}
    (he : e ∈ D.sideEdges 0) (he' : e' ∈ D.sideEdges 0) (hne : e ≠ e') : e.1 ≠ e'.1 := by
  intro h1
  have h2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext h1 h2)
  have hcov : ∀ a b m : Fin 3, a ≠ b → m = a ∨ m = a + 1 ∨ m = b ∨ m = b + 1 := by decide
  have hall : ∀ m : Fin 3, (D.tile e.1).pts m ∈ D.target.edge 0 := by
    intro m
    obtain ⟨p1, p2⟩ := Row2.endpoints_mem D he
    obtain ⟨q1, q2⟩ := Row2.endpoints_mem D he'
    rw [← h1] at q1 q2
    rcases hcov e.2 e'.2 m h2 with rfl | rfl | rfl | rfl
    · exact p1
    · exact p2
    · exact q1
    · exact q2
  have hline : ∀ m, (D.tile e.1).pts m ∈ line[ℝ, D.target.pts 0, D.target.pts 1] := fun m =>
    (mem_segment_iff_wbtw.mp (hall m)).mem_affineSpan
  have hcol : Collinear ℝ (Set.range (D.tile e.1).pts) := by
    rw [(D.tile e.1).range_pts_eq' 0]
    refine (collinear_insert_insert_insert_of_mem_affineSpan_pair (hline (0 + 1)) (hline 0)
      (hline (0 + 2))).subset ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  exact (affineIndependent_iff_not_collinear.mp (D.tile e.1).indep) hcol
theorem Row2.gamma_endpoint (D : CongruentDissection N) {e : Fin N × Fin 3}
    (hl : D.eLen e ≠ D.model.oppLen 2) :
    ∃ k, (D.tile e.1).angleAt k = D.model.angleAt 2 ∧ (k = e.2 ∨ k = e.2 + 1) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent e.1).exists_perm
  refine ⟨σ.symm 2, by rw [(hσ _).1, Equiv.apply_symm_apply],
    Row2.fin3_ne_add_two _ _ fun h => hl ?_⟩
  rw [D.toDissection.eLen_eq_oppLen e, ← h, (hσ _).2, Equiv.apply_symm_apply]
theorem Row2.no_gamma_corner (D : CongruentDissection N) (t : Fin 3) (i : Fin N) (k : Fin 3)
    (hk : (D.tile i).angleAt k = D.model.angleAt 2) (hlt : D.target.angleAt t < D.model.angleAt 2) :
    (D.tile i).pts k ≠ D.target.pts t := by
  intro h
  have hloc : (D.tile i).localAngle (D.target.pts t) = D.model.angleAt 2 := by
    rw [← h, (D.tile i).localAngle_vertex k]; exact hk
  have hle : (D.tile i).localAngle (D.target.pts t) ≤ ∑ j, (D.tile j).localAngle (D.target.pts t) :=
    Finset.single_le_sum (fun j _ => (D.tile j).localAngle_nonneg _) (Finset.mem_univ i)
  rw [Row2.corner_sum D t, hloc] at hle
  linarith
theorem Row2.two_gamma (f : Fin N → ℝ) {θ0 θ1 θ2 : ℝ} (hnn : ∀ i, 0 ≤ f i)
    (hge : ∀ i, f i ≠ 0 → θ0 ≤ f i) (hsum : ∑ i, f i = π) (hθ : θ0 + θ1 + θ2 = π)
    (h12 : θ1 < θ2) {i1 i2 : Fin N} (hne : i1 ≠ i2) (h1 : f i1 = θ2) (h2 : f i2 = θ2) :
    2 * θ2 = π := by
  have hi2 : i2 ∈ Finset.univ.erase i1 := Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  have hsplit : ∑ i, f i = f i1 + (f i2 + ∑ i ∈ (Finset.univ.erase i1).erase i2, f i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i1), ← Finset.add_sum_erase _ _ hi2]
  have hS0 : 0 ≤ ∑ i ∈ (Finset.univ.erase i1).erase i2, f i := Finset.sum_nonneg (fun i _ => hnn i)
  by_contra hne2
  have hSpos : ∑ i ∈ (Finset.univ.erase i1).erase i2, f i ≠ 0 := by
    intro h; apply hne2; rw [hsplit, h1, h2, h] at hsum; linarith
  obtain ⟨i3, hi3, hf3⟩ := Finset.exists_ne_zero_of_sum_ne_zero hSpos
  have h3 : f i3 ≤ ∑ i ∈ (Finset.univ.erase i1).erase i2, f i :=
    Finset.single_le_sum (fun i _ => hnn i) hi3
  have := hge i3 hf3
  rw [hsplit, h1, h2] at hsum
  linarith
theorem Row2.lemmaR (D : CongruentDissection N)
    (hang : ∀ k, D.target.angleAt k = D.model.angleAt k)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hnoc : ∀ e ∈ D.sideEdges 0, D.eLen e ≠ D.model.oppLen 2) :
    2 * D.model.angleAt 2 = π := by
  classical
  have A_mem : D.target.pts 0 ∈ D.target.edge 0 := left_mem_segment ℝ _ _
  have B_mem : D.target.pts 1 ∈ D.target.edge 0 := right_mem_segment ℝ _ _
  have hnA : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ≠ D.target.pts 0 :=
    fun i k hk => Row2.no_gamma_corner D 0 i k hk (by rw [hang 0]; linarith)
  have hnB : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ≠ D.target.pts 1 :=
    fun i k hk => Row2.no_gamma_corner D 1 i k hk (by rw [hang 1]; exact h12)
  have tau_lt : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ∈ D.target.edge 0 →
      0 < Row2.tau D.target ((D.tile i).pts k) ∧ Row2.tau D.target ((D.tile i).pts k) < 1 := by
    intro i k hk hmem
    obtain ⟨-, h0, h1, h2⟩ := Row2.edge0_coord D.target hmem
    constructor
    · rcases h1.lt_or_eq with h | h
      · exact h
      · exact absurd (Row2.tau_inj D.target hmem A_mem (h.symm.trans (Row2.tau_A D.target).symm))
          (hnA i k hk)
    · rcases (show Row2.tau D.target ((D.tile i).pts k) ≤ 1 by linarith).lt_or_eq with h | h
      · exact h
      · exact absurd (Row2.tau_inj D.target hmem B_mem (h.trans (Row2.tau_B D.target).symm))
          (hnB i k hk)
  have gend : ∀ e ∈ D.sideEdges 0, ∃ k, (D.tile e.1).angleAt k = D.model.angleAt 2 ∧
      (D.tile e.1).pts k ∈ D.eSet e ∧
      (Row2.tau D.target ((D.tile e.1).pts k) = Row2.lo D.toDissection e ∨
        Row2.tau D.target ((D.tile e.1).pts k) = Row2.hi D.toDissection e) := by
    intro e he
    obtain ⟨k, hk, hke⟩ := Row2.gamma_endpoint D (hnoc e he)
    obtain ⟨hX, hY⟩ := Row2.eq_inf_or_sup (Row2.tau D.target ((D.tile e.1).pts e.2))
      (Row2.tau D.target ((D.tile e.1).pts (e.2 + 1)))
    rcases hke with rfl | rfl
    · exact ⟨_, hk, left_mem_segment ℝ _ _, hX⟩
    · exact ⟨_, hk, right_mem_segment ℝ _ _, hY⟩
  obtain ⟨R, hR⟩ : ∃ R : Finset (Fin N × Fin 3), R = (D.sideEdges 0).filter (fun e =>
      ∃ k, (D.tile e.1).angleAt k = D.model.angleAt 2 ∧ (D.tile e.1).pts k ∈ D.eSet e ∧
        Row2.tau D.target ((D.tile e.1).pts k) = Row2.hi D.toDissection e) := ⟨_, rfl⟩
  obtain ⟨eA, heA, hAe⟩ := D.toDissection.exists_sideEdge_mem 0 A_mem
  have hReA : eA ∈ R := by
    obtain ⟨k, hk, hkm, hlh⟩ := gend eA heA
    have hpos := (tau_lt _ _ hk (Row2.sideEdge_sub D.toDissection heA hkm)).1
    have hlo : Row2.lo D.toDissection eA ≤ 0 := by
      have := ((Row2.mem_eSet_iff D.toDissection heA A_mem).mp hAe).1
      rwa [Row2.tau_A] at this
    rw [hR, Finset.mem_filter]
    refine ⟨heA, k, hk, hkm, ?_⟩
    rcases hlh with h | h
    · exfalso; linarith
    · exact h
  obtain ⟨eS, heSR, hmax⟩ := R.exists_max_image (Row2.hi D.toDissection) ⟨eA, hReA⟩
  rw [hR, Finset.mem_filter] at heSR
  obtain ⟨heS, kS, hkS, hkSm, hkSt⟩ := heSR
  obtain ⟨s, hs⟩ : ∃ s, s = Row2.hi D.toDissection eS := ⟨_, rfl⟩
  have hkSedge := Row2.sideEdge_sub D.toDissection heS hkSm
  have hs1 : s < 1 := by rw [hs, ← hkSt]; exact (tau_lt _ _ hkS hkSedge).2
  have hs0 : 0 < s := by rw [hs, ← hkSt]; exact (tau_lt _ _ hkS hkSedge).1
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin N × Fin 3),
      F = (D.sideEdges 0).filter (fun e => s < Row2.hi D.toDissection e) := ⟨_, rfl⟩
  obtain ⟨eB, heB, hBe⟩ := D.toDissection.exists_sideEdge_mem 0 B_mem
  have hFB : eB ∈ F := by
    rw [hF, Finset.mem_filter]
    refine ⟨heB, ?_⟩
    have := ((Row2.mem_eSet_iff D.toDissection heB B_mem).mp hBe).2
    rw [Row2.tau_B] at this
    linarith
  obtain ⟨e', he'F, hmin⟩ := F.exists_min_image (Row2.lo D.toDissection) ⟨eB, hFB⟩
  have he'F' := he'F
  rw [hF, Finset.mem_filter] at he'F'
  obtain ⟨he', he's⟩ := he'F'
  have hlo' : Row2.lo D.toDissection e' ≤ s := by
    by_contra hc
    push Not at hc
    obtain ⟨-, hhi1⟩ := Row2.lo_hi_bounds D.toDissection he'
    have hlohi := Row2.lo_lt_hi D.toDissection he'
    obtain ⟨z, hz, hzw⟩ := Row2.tau_surj D.target (s := (s + Row2.lo D.toDissection e') / 2)
      (by linarith) (by linarith)
    obtain ⟨e'', he'', hze''⟩ := D.toDissection.exists_sideEdge_mem 0 hz
    have hz'' := (Row2.mem_eSet_iff D.toDissection he'' hz).mp hze''
    rw [hzw] at hz''
    have he''F : e'' ∈ F := by
      rw [hF, Finset.mem_filter]; exact ⟨he'', by linarith [hz''.2]⟩
    have := hmin e'' he''F
    linarith [hz''.1]
  have hne : e' ≠ eS := by
    intro h; rw [h, ← hs] at he's; exact lt_irrefl _ he's
  have hlo'eq : Row2.lo D.toDissection e' = s := by
    by_contra hc
    have hlt : Row2.lo D.toDissection e' < s := lt_of_le_of_ne hlo' hc
    have hSlo := Row2.lo_lt_hi D.toDissection heS
    rw [← hs] at hSlo
    have hm1 := le_max_left (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e')
    have hm2 := le_max_right (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e')
    have hus : max (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e') < s := max_lt hSlo hlt
    exact Row2.interiors_disjoint D.toDissection heS he' hne.symm
      (s := (max (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e') + s) / 2)
      (by linarith) (by rw [← hs]; linarith) (by linarith) (by linarith)
  obtain ⟨k', hk', hk'm, hk't⟩ := gend e' he'
  have hk's : Row2.tau D.target ((D.tile e'.1).pts k') = s := by
    rcases hk't with h | h
    · rw [h, hlo'eq]
    · exfalso
      have he'R : e' ∈ R := by
        rw [hR, Finset.mem_filter]; exact ⟨he', k', hk', hk'm, h⟩
      have := hmax e' he'R
      rw [← hs] at this
      linarith
  have hk'edge := Row2.sideEdge_sub D.toDissection he' hk'm
  have hP : (D.tile e'.1).pts k' = (D.tile eS.1).pts kS :=
    Row2.tau_inj D.target hk'edge hkSedge (hk's.trans (hs.trans hkSt.symm))
  have htiles : eS.1 ≠ e'.1 := Row2.distinct_tiles D.toDissection heS he' hne.symm
  have hPfr : (D.tile eS.1).pts kS ∈ frontier D.target.carrier :=
    Erdos634.SideWall.edge_subset_frontier D.target 0 hkSedge
  have hPnv : (D.tile eS.1).pts kS ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    have hsP : Row2.tau D.target ((D.tile eS.1).pts kS) = s := hkSt.trans hs.symm
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 by fin_cases m <;> simp) with rfl | rfl | rfl
    · rw [← hm, Row2.tau_A] at hsP; linarith
    · rw [← hm, Row2.tau_B] at hsP; linarith
    · have h2 := (Row2.edge0_coord D.target hkSedge).1
      rw [← hm] at h2
      have h1 : D.target.basis.coord 2 (D.target.pts 2) = 1 := D.target.basis.coord_apply_eq 2
      rw [h1] at h2; exact one_ne_zero h2
  have hsum := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hPfr hPnv
  have hS : (D.tile eS.1).localAngle ((D.tile eS.1).pts kS) = D.model.angleAt 2 := by
    rw [(D.tile eS.1).localAngle_vertex kS]; exact hkS
  have h' : (D.tile e'.1).localAngle ((D.tile eS.1).pts kS) = D.model.angleAt 2 := by
    rw [← hP, (D.tile e'.1).localAngle_vertex k']; exact hk'
  have h2π := Row2.angle2_lt_pi D.model
  refine Row2.two_gamma (fun i => (D.tile i).localAngle ((D.tile eS.1).pts kS))
    (θ0 := D.model.angleAt 0) (θ1 := D.model.angleAt 1)
    (fun i => (D.tile i).localAngle_nonneg _) ?_ hsum D.model.angleAt_sum h12 htiles hS h'
  intro i hi
  have hi' : (D.tile i).localAngle ((D.tile eS.1).pts kS) ≠ 0 := hi
  show D.model.angleAt 0 ≤ (D.tile i).localAngle ((D.tile eS.1).pts kS)
  have hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = D.model.angleAt 0 := rfl
  have hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = D.model.angleAt 1 := rfl
  have hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = D.model.angleAt 2 := rfl
  have hv := Dissection.congruentDissection_localAngle_mem_boundary D
    (D.model.angleAt 0) (D.model.angleAt 1) (D.model.angleAt 2) hα' hβ' hγ' hPfr hPnv i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h | h | h | h | h
  · rw [h]
  · rw [h]; linarith
  · rw [h]; linarith
  · rw [h]; linarith
  · exact absurd h hi'
theorem Row2.noc_of_sideCount (D : CongruentDissection N) (h : D.sideCount 2 2 = 0) :
    ∀ e ∈ D.sideEdges 0, D.eLen e ≠ D.model.oppLen 2 := by
  intro e he hl
  have : 0 < D.sideCount 2 2 := Row2.sideCount_pos D (i := 2) he hl
  omega
end Erdos634.Geometry
end

section
namespace Erdos634.RouteOneVertexKill
open Erdos634.Geometry
theorem cornerAngle_lt_pi (T : Tri) (j : Fin 3) :
    cornerAngle (T.pts (j + 1)) (T.pts j) (T.pts (j + 2)) < Real.pi := by
  rw [Erdos634.Geometry.cornerAngle]
  rcases lt_or_eq_of_le (EuclideanGeometry.angle_le_pi
    (T.pts (j + 1)) (T.pts j) (T.pts (j + 2))) with h | h
  · exact h
  · exfalso
    have hcol : Collinear ℝ ({T.pts (j + 1), T.pts j, T.pts (j + 2)} : Set Plane) :=
      EuclideanGeometry.collinear_of_angle_eq_pi h
    have hidx : ∀ i j : Fin 3, i = j ∨ i = j + 1 ∨ i = j + 2 := by decide
    have hsub : Set.range T.pts ⊆ ({T.pts (j + 1), T.pts j, T.pts (j + 2)} : Set Plane) := by
      rintro _ ⟨i, rfl⟩
      have := hidx i j
      rcases this with rfl | rfl | rfl <;> simp
    have hrange : Collinear ℝ (Set.range T.pts) := hcol.subset hsub
    exact (affineIndependent_iff_not_collinear.mp T.indep) hrange
end Erdos634.RouteOneVertexKill
end

section
namespace Erdos634.NormalPosition
open Erdos634.Geometry
noncomputable def relabelTri (T : Tri) (σ : Equiv.Perm (Fin 3)) : Tri where
  pts := T.pts ∘ σ
  indep := T.indep.comp_embedding σ.toEmbedding
@[simp] theorem relabelTri_carrier (T : Tri) (σ : Equiv.Perm (Fin 3)) :
    (relabelTri T σ).carrier = T.carrier := by
  simp only [Tri.carrier, relabelTri]
  rw [Set.range_comp, σ.surjective.range_eq, Set.image_univ]
noncomputable def relabelTarget {N : ℕ} (D : Dissection N) (σ : Equiv.Perm (Fin 3)) :
    Dissection N where
  target := relabelTri D.target σ
  tile := D.tile
  covers := by rw [D.covers, relabelTri_carrier]
  interiors_disjoint := D.interiors_disjoint
end Erdos634.NormalPosition
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
open scoped Classical
namespace Erdos634.Geometry.Row3.RP
open Real Erdos634.Geometry Erdos634.Geometry.Row3
theorem abs_det_eq (T : Tri) :
    |T.det| = T.oppLen 1 * T.oppLen 2 * Real.sin (T.angleAt 0) := by
  have hang : T.angleAt 0
      = InnerProductGeometry.angle (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) := rfl
  have h1 : T.oppLen 1 = ‖T.pts 2 - T.pts 0‖ := by
    show dist (T.pts 2) (T.pts 0) = _; rw [dist_eq_norm]
  have h2 : T.oppLen 2 = ‖T.pts 1 - T.pts 0‖ := by
    show dist (T.pts 0) (T.pts 1) = _; rw [dist_comm, dist_eq_norm]
  have hsin := InnerProductGeometry.sin_angle_mul_norm_mul_norm (T.pts 1 - T.pts 0)
    (T.pts 2 - T.pts 0)
  have hid : inner ℝ (T.pts 1 - T.pts 0) (T.pts 1 - T.pts 0)
        * inner ℝ (T.pts 2 - T.pts 0) (T.pts 2 - T.pts 0)
      - inner ℝ (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0)
        * inner ℝ (T.pts 1 - T.pts 0) (T.pts 2 - T.pts 0) = T.det ^ 2 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two]
    unfold Tri.det; ring
  rw [← Real.sqrt_sq_eq_abs, ← hid, ← hsin, hang, h1, h2]
  ring
theorem abs_det_target {N : ℕ} (D : CongruentDissection N) :
    |D.target.det| = N * |D.model.det| := by
  have hdt : ∀ T : Tri, Erdos634.AreaDet.detTri T = T.det := fun T => by
    rw [Erdos634.AreaDet.detTri_eq]; unfold Tri.det; ring
  have hv := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [Erdos634.AreaDet.volume_eq_det_mul, Erdos634.AreaDet.volume_eq_det_mul, hdt, hdt] at hv
  set S := MeasureTheory.volume Erdos634.AreaDet.stdCarrier
  have hB : ENNReal.ofReal |D.model.det| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact abs_pos.mpr D.model.det_ne_zero
  have hS0 : S ≠ 0 := by
    have hp := D.model.volume_pos
    rw [Erdos634.AreaDet.volume_eq_det_mul, hdt] at hp
    change 0 < ENNReal.ofReal |D.model.det| * S at hp
    intro h; rw [h, mul_zero] at hp; exact lt_irrefl _ hp
  have hST : S ≠ ⊤ := by
    have hf := D.model.volume_ne_top
    rw [Erdos634.AreaDet.volume_eq_det_mul, hdt] at hf
    change ENNReal.ofReal |D.model.det| * S ≠ ⊤ at hf
    intro h; apply hf; rw [h]; exact ENNReal.mul_top hB
  have hpos : 0 < S.toReal := ENNReal.toReal_pos hS0 hST
  have hr := congrArg ENNReal.toReal hv
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_natCast] at hr
  have : (|D.target.det| - N * |D.model.det|) * S.toReal = 0 := by linear_combination hr
  have := (mul_eq_zero.mp this).resolve_right hpos.ne'
  linarith
end Erdos634.Geometry.Row3.RP
end

section
open scoped Classical
namespace Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry Erdos634.TilePlacement
def SimilarTM {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ (μ : ℝ) (τ : Equiv.Perm (Fin 3)), ∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧
    D.target.oppLen k = μ * D.model.oppLen (τ k)
section Controls
end Controls
end Erdos634.Draft.TheoremPConditional
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
namespace Erdos634.Draft.LemmaCFinal
theorem key3 : ∀ p q r k : Fin 3, p ≠ q → p ≠ r → q ≠ r → k = p ∨ k = q ∨ k = r := by decide
theorem sum3 {M : Type*} [AddCommMonoid M] (f : Fin 3 → M) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : f i + f j + f l = f 0 + f 1 + f 2 := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {i, j, l} := by
    ext k; simp [key3 i j l k hij hil hjl]
  have h := Fin.sum_univ_three f
  rw [huniv, Finset.sum_insert (by simp [hij, hil]), Finset.sum_insert (by simp [hjl]),
    Finset.sum_singleton] at h
  rw [← h, add_assoc]
end Erdos634.Draft.LemmaCFinal
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFinal
namespace Erdos634.Draft.LaczFormal
theorem angleAt_sum (T : Tri) : T.angleAt 0 + T.angleAt 1 + T.angleAt 2 = Real.pi := by
  show cornerAngle (T.pts 1) (T.pts 0) (T.pts 2) +
       cornerAngle (T.pts 2) (T.pts 1) (T.pts 0) +
       cornerAngle (T.pts 0) (T.pts 2) (T.pts 1) = Real.pi
  exact Erdos634.Geometry.cornerAngle_sum T
def TileAngles {N : ℕ} (D : CongruentDissection N) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), D.model.angleAt (σ 0) = x ∧ D.model.angleAt (σ 1) = y ∧
    D.model.angleAt (σ 2) = z
theorem TileAngles.swap {N : ℕ} {D : CongruentDissection N} {x y z : ℝ}
    (h : TileAngles D x y z) : TileAngles D y x z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨(Equiv.swap (0 : Fin 3) 1).trans σ, ?_, ?_, ?_⟩
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]; exact h1
  · simp only [Equiv.trans_apply, Equiv.swap_apply_right]; exact h0
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact h2
theorem TileAngles.swap23 {N : ℕ} {D : CongruentDissection N} {x y z : ℝ}
    (h : TileAngles D x y z) : TileAngles D x z y := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  refine ⟨(Equiv.swap (1 : Fin 3) 2).trans σ, ?_, ?_, ?_⟩
  · simp only [Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact h0
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]; exact h2
  · simp only [Equiv.trans_apply, Equiv.swap_apply_right]; exact h1
theorem TileAngles.cast {N : ℕ} {D : CongruentDissection N} {x y z x' y' z' : ℝ}
    (h : TileAngles D x y z) (ex : x = x') (ey : y = y') (ez : z = z') :
    TileAngles D x' y' z' := by
  subst ex ey ez; exact h
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
namespace Erdos634.Draft.LaczFormal
theorem similar_ratio_sq {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧
      D.target.oppLen k = μ * D.model.oppLen k) : 0 < μ ∧ (N : ℝ) = μ ^ 2 := by
  have h1 := D.target.oppLen_pos 0
  have h2 := D.model.oppLen_pos 0
  have hpos : 0 < μ := by
    by_contra hc; push Not at hc
    have := (hsim 0).2
    nlinarith
  refine ⟨hpos, ?_⟩
  have ha := Row3.RP.abs_det_target D
  rw [Row3.RP.abs_det_eq, Row3.RP.abs_det_eq, (hsim 1).2, (hsim 2).2, (hsim 0).1] at ha
  have hs : 0 < Real.sin (D.model.angleAt 0) :=
    Real.sin_pos_of_pos_of_lt_pi (Erdos634.MarchFlank.cornerAngle_pos D.model 0)
      (Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model 0)
  have hp : 0 < D.model.oppLen 1 * D.model.oppLen 2 * Real.sin (D.model.angleAt 0) :=
    mul_pos (mul_pos (D.model.oppLen_pos 1) (D.model.oppLen_pos 2)) hs
  refine mul_right_cancel₀ hp.ne' ?_
  linear_combination -ha
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
namespace Erdos634.Draft.LaczFormal
theorem similar_reduction {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧
      D.target.oppLen k = μ * D.model.oppLen k) (hN : ¬ IsSquare N) :
    ((N : ℝ) = μ ^ 2 ∧ ¬ ∃ r : ℚ, μ = r) ∧
    (∃ y ∈ AddSubgroup.closure ({D.model.angleAt 0, D.model.angleAt 1, Real.pi} : Set ℝ),
      Real.pi = 2 * y) ∧
    (∀ i, ∑ j, (D.sideCountT i j : ℝ) * D.model.oppLen j = μ * D.model.oppLen i) ∧
    (¬ ((∃ r : ℚ, D.model.oppLen 0 = r * D.model.oppLen 2) ∧
        (∃ r : ℚ, D.model.oppLen 1 = r * D.model.oppLen 2))) ∧
    (∀ k, Row2.QMu μ (Real.cos (D.model.angleAt k))) := by
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  obtain ⟨hμq, -⟩ := Row2.mu_irrational D μ hside hN
  obtain ⟨-, hnot, hcos⟩ := Row2.lemmaK_general D μ hside hN
  refine ⟨⟨(similar_ratio_sq D μ hsim).2, hμq⟩, ?_, Row2.sideCountT_eigen D μ hside, hnot, hcos⟩
  by_contra hc
  push Not at hc
  obtain ⟨S, hS, -⟩ := Row2.lemmaW D μ hsim hc
  apply hN
  have hsq := (similar_ratio_sq D μ hsim).2
  rw [hS] at hsq
  have : (N : ℤ) = S ^ 2 := by exact_mod_cast hsq
  have hN' : N = S.natAbs ^ 2 := by
    have := congrArg Int.natAbs this
    simpa [Int.natAbs_pow] using this
  exact ⟨S.natAbs, by rw [hN']; ring⟩
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
open Real Polynomial Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal
theorem t1_core {N : ℕ} (hN : ¬ IsSquare N) {s : ℝ} (hs : s ^ 2 = N) {θ : ℝ}
    (hθ : ∃ r : ℚ, θ = r * π) (hc : Row2.QMu s (Real.cos θ)) :
    ∃ (a b : ℚ) (U W : ℤ), 2 * Real.cos θ = (a : ℝ) + b * s ∧ (U : ℝ) = 2 * a ∧
      (W : ℝ) = a * a - b * b * N ∧ |(a : ℝ) + b * s| ≤ 2 ∧ |(a : ℝ) - b * s| ≤ 2 := by
  obtain ⟨r, hr⟩ := hθ
  obtain ⟨q₁, q₂, hq⟩ := hc
  have hsq : s ^ 2 = ((N : ℚ) : ℝ) := by rw [hs]; push_cast; ring
  have hirr : ∀ q : ℚ, s ≠ q := by
    intro q hsq'
    have habs : √(N : ℝ) = |(q : ℝ)| := by
      rw [← hsq', ← hs, Real.sqrt_sq_eq_abs]
    exact (irrational_sqrt_natCast_iff.mpr hN) ⟨|q|, by rw [habs]; push_cast; rfl⟩
  set a : ℚ := 2 * q₁ with ha
  set b : ℚ := 2 * q₂ with hb
  set x : ℝ := 2 * Real.cos θ with hx
  have hxab : x = (a : ℝ) + b * s := by rw [hx, hq, ha, hb]; push_cast; ring
  set x' : ℝ := (a : ℝ) - b * s with hx'
  have hxint : IsIntegral ℤ x := by
    rw [hx, hr]; exact Real.isIntegral_two_mul_cos_rat_mul_pi r
  have hx'int : IsIntegral ℤ x' := by
    obtain ⟨P, hPm, hP⟩ := hxint
    obtain ⟨A, B, h1, h2⟩ := Row2.poly_conj hsq a b P
    rw [hxab, h1] at hP
    have hB : B = 0 := by
      by_contra hB0
      apply hirr (-A / B)
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB0
      push_cast; field_simp; linarith
    have hA : (A : ℝ) = 0 := by rw [hB] at hP; simpa using hP
    exact ⟨P, hPm, by rw [hx', h2, hA, hB]; simp⟩
  have hxle : |x| ≤ 2 := by
    rw [hx, abs_mul, abs_two]
    have := Real.abs_cos_le_one θ
    linarith
  set n : ℕ := 2 * r.den with hn
  have hnpos : 0 < n := by positivity
  have hchebx : Row2.cheb x n = 2 := by
    rw [hx, Row2.cheb_cos θ n, hr]
    have : ((n : ℕ) : ℝ) * ((r : ℝ) * π) = (r.num : ℝ) * (2 * π) := by
      rw [hn]; push_cast
      have hd : (r : ℝ) * r.den = r.num := by exact_mod_cast Rat.mul_den_eq_num r
      linear_combination (2 * π) * hd
    rw [this, Real.cos_int_mul_two_pi]; ring
  have hx'le : |x'| ≤ 2 := by
    obtain ⟨A, B, h1, h2⟩ := Row2.cheb_conj hsq a b n
    rw [← hxab, hchebx] at h1
    have hB : B = 0 := by
      by_contra hB0
      apply hirr ((2 - A) / B)
      have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB0
      push_cast; field_simp; linarith
    have hA : (A : ℝ) = 2 := by rw [hB] at h1; simpa using h1.symm
    refine Row2.abs_le_two_of_cheb hnpos ?_
    rw [hx', h2, hA, hB]; simp
  obtain ⟨U, hU⟩ := (hxint.add hx'int).exists_int_iff_exists_rat.mp
    ⟨2 * a, by rw [hxab, hx']; push_cast; ring⟩
  obtain ⟨W, hW⟩ := (hxint.mul hx'int).exists_int_iff_exists_rat.mp
    ⟨a * a - b * b * N, by rw [hxab, hx']; push_cast; linear_combination (-(b : ℝ) ^ 2) * hs⟩
  refine ⟨a, b, U, W, hxab, ?_, ?_, ?_, ?_⟩
  · rw [← hU, hxab, hx']; ring
  · rw [← hW, hxab, hx']; linear_combination (-(b : ℝ) ^ 2) * hs
  · rw [← hxab]; exact hxle
  · exact hx'le
theorem theta_eq_of_cos {θ φ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π) (g0 : 0 ≤ φ) (g1 : φ ≤ π)
    (h : Real.cos θ = Real.cos φ) : θ = φ :=
  Real.injOn_cos ⟨h0, h1⟩ ⟨g0, g1⟩ h
theorem nat_sq_of_rat {n : ℕ} (r : ℚ) (h : (r : ℝ) ^ 2 = (n : ℝ)) : ∃ j : ℕ, n = j ^ 2 := by
  have h' : r ^ 2 = (n : ℚ) := by exact_mod_cast h
  have h1 : IsSquare (((n : ℤ) : ℤ) : ℚ) := ⟨r, by push_cast; rw [← h']; ring⟩
  rw [Rat.isSquare_intCast_iff] at h1
  obtain ⟨j, hj⟩ := Int.isSquare_natCast_iff.mp h1
  exact ⟨j, by rw [hj]; ring⟩
theorem kernel2 {N j : ℕ} (h : 8 * N = j ^ 2) : ∃ k : ℕ, N = 2 * k ^ 2 := by
  have h2 : 2 ∣ j := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (⟨4 * N, by rw [← h]; ring⟩ : 2 ∣ j ^ 2)
  obtain ⟨i, rfl⟩ := h2
  have h3 : 2 * N = i ^ 2 := by nlinarith
  have h4 : 2 ∣ i := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (⟨N, by rw [← h3]⟩ : 2 ∣ i ^ 2)
  obtain ⟨k, rfl⟩ := h4
  exact ⟨k, by nlinarith⟩
theorem kernel3 {N j : ℕ} (h : 12 * N = j ^ 2) : ∃ k : ℕ, N = 3 * k ^ 2 := by
  have h2 : 2 ∣ j := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (⟨6 * N, by rw [← h]; ring⟩ : 2 ∣ j ^ 2)
  obtain ⟨i, rfl⟩ := h2
  have h3 : 3 * N = i ^ 2 := by nlinarith
  have h4 : 3 ∣ i := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (⟨N, by rw [← h3]⟩ : 3 ∣ i ^ 2)
  obtain ⟨k, rfl⟩ := h4
  exact ⟨k, by nlinarith⟩
theorem kernel5 {N j : ℕ} (h : 5 * N = j ^ 2) : ∃ k : ℕ, N = 5 * k ^ 2 := by
  have h2 : 5 ∣ j := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) (⟨N, by rw [← h]⟩ : 5 ∣ j ^ 2)
  obtain ⟨k, rfl⟩ := h2
  exact ⟨k, by nlinarith⟩
theorem cos_two_pi_div_five : Real.cos (2 * π / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]
theorem lemmaQ_general {N : ℕ} (hN : ¬ IsSquare N) {s : ℝ} (hs : s ^ 2 = N) {θ : ℝ}
    (hθ : ∃ r : ℚ, θ = r * π) (hθ0 : 0 < θ) (hθπ : θ < π) (hc : Row2.QMu s (Real.cos θ)) :
    (θ = π / 3 ∨ θ = π / 2 ∨ θ = π * (2 / 3)) ∨
    ((θ = π / 4 ∨ θ = π * (3 / 4)) ∧ ∃ k : ℕ, N = 2 * k ^ 2) ∨
    ((θ = π / 6 ∨ θ = π * (5 / 6)) ∧ ∃ k : ℕ, N = 3 * k ^ 2) ∨
    ((θ = π / 5 ∨ θ = π * (2 / 5) ∨ θ = π * (3 / 5) ∨ θ = π * (4 / 5)) ∧ ∃ k : ℕ, N = 5 * k ^ 2) := by
  have hpi := Real.pi_pos
  obtain ⟨a, b, U, W, hx, hUa, hWa, hle, hle'⟩ := t1_core hN hs hθ hc
  have hNpos : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; exact hN ⟨0, rfl⟩)
  have hirr : ∀ q : ℚ, s ≠ q := by
    intro q hsq'
    have habs : √(N : ℝ) = |(q : ℝ)| := by
      rw [← hsq', ← hs, Real.sqrt_sq_eq_abs]
    exact (irrational_sqrt_natCast_iff.mpr hN) ⟨|q|, by rw [habs]; push_cast; rfl⟩
  by_cases hb : b = 0
  · left
    have hcosq : ∃ q : ℚ, Real.cos θ = q := ⟨a / 2, by
      subst hb; push_cast at hx; push_cast; linarith⟩
    obtain ⟨r, hr⟩ := hθ
    have hmem := niven_angle_eq ⟨r, hr⟩ hcosq ⟨hθ0.le, hθπ.le⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h | h
    · exact absurd h hθ0.ne'
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h hθπ.ne
  right
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  set x : ℝ := 2 * Real.cos θ with hxdef
  set x' : ℝ := (a : ℝ) - b * s with hx'
  have hxab : x = (a : ℝ) + b * s := hx
  have hsum : x + x' = U := by rw [hxab, hx', hUa]; ring
  have hprod : x * x' = W := by rw [hxab, hx', hWa]; linear_combination (-(b : ℝ) ^ 2) * hs
  have hdiff : x - x' = 2 * b * s := by rw [hxab, hx']; ring
  obtain ⟨D, hDdef⟩ : ∃ D : ℤ, D = U * U - 4 * W := ⟨_, rfl⟩
  have hDR : (D : ℝ) = (x - x') ^ 2 := by
    rw [hDdef]; push_cast
    have : (x - x') ^ 2 = (x + x') ^ 2 - 4 * (x * x') := by ring
    rw [this, hsum, hprod]; ring
  have hxx : |x| ≤ 2 := by rw [hxab]; exact hle
  have hxx' : |x'| ≤ 2 := hle'
  have hDpos : 0 < D := by
    have : (0 : ℝ) < (x - x') ^ 2 := by
      rw [hdiff]; have : 2 * (b : ℝ) * s ≠ 0 := by
        have hs0 : s ≠ 0 := by
          intro h0; apply hirr 0; simpa using h0
        positivity
      positivity
    exact_mod_cast hDR ▸ this
  have hDle : D ≤ 16 := by
    have h4 : |x - x'| ≤ 4 := (abs_sub _ _).trans (by linarith)
    have : (x - x') ^ 2 ≤ 16 := by
      have := sq_le_sq' (abs_le.mp h4).1 (abs_le.mp h4).2
      linarith
    have : (D : ℝ) ≤ 16 := by rw [hDR]; exact this
    exact_mod_cast this
  have hUb : -4 ≤ U ∧ U ≤ 4 := by
    have h1 := abs_le.mp hxx; have h2 := abs_le.mp hxx'
    have a1 : (U : ℝ) ≤ 4 := by rw [← hsum]; linarith
    have a2 : (-4 : ℝ) ≤ U := by rw [← hsum]; linarith
    exact ⟨by exact_mod_cast a2, by exact_mod_cast a1⟩
  have hp2 : 0 ≤ 4 - 2 * U + W := by
    have h1 := abs_le.mp hxx; have h2 := abs_le.mp hxx'
    have : (0 : ℝ) ≤ (2 - x) * (2 - x') := mul_nonneg (by linarith) (by linarith)
    have e : (2 - x) * (2 - x') = 4 - 2 * U + W := by rw [← hsum, ← hprod]; ring
    have : (0 : ℝ) ≤ 4 - 2 * U + W := by rw [← e]; exact this
    exact_mod_cast this
  have hm2 : 0 ≤ 4 + 2 * U + W := by
    have h1 := abs_le.mp hxx; have h2 := abs_le.mp hxx'
    have : (0 : ℝ) ≤ (2 + x) * (2 + x') := mul_nonneg (by linarith) (by linarith)
    have e : (2 + x) * (2 + x') = 4 + 2 * U + W := by rw [← hsum, ← hprod]; ring
    have : (0 : ℝ) ≤ 4 + 2 * U + W := by rw [← e]; exact this
    exact_mod_cast this
  have hnsq : ∀ m : ℤ, D ≠ m ^ 2 := by
    intro m hm
    have h1 : (2 * (b : ℝ) * s) ^ 2 = (m : ℝ) ^ 2 := by
      rw [← hdiff, ← hDR, hm]; push_cast; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with e | e
    · apply hirr (m / (2 * b)); push_cast; field_simp; linarith
    · apply hirr (-m / (2 * b)); push_cast; field_simp; linarith
  have hn1 : D ≠ 1 := fun h => hnsq 1 (by rw [h]; norm_num)
  have hn4 : D ≠ 4 := fun h => hnsq 2 (by rw [h]; norm_num)
  have hn9 : D ≠ 9 := fun h => hnsq 3 (by rw [h]; norm_num)
  have hn16 : D ≠ 16 := fun h => hnsq 4 (by rw [h]; norm_num)
  have hW4 : 4 * W = U * U - D := by omega
  have hcases : (U = 0 ∧ D = 8) ∨ (U = 0 ∧ D = 12) ∨ (U = 1 ∧ D = 5) ∨ (U = -1 ∧ D = 5) := by
    obtain ⟨hU1, hU2⟩ := hUb
    interval_cases U <;> interval_cases D <;> omega
  have hND : ∀ d : ℕ, D = d → ∃ j : ℕ, d * N = j ^ 2 := by
    intro d hd
    refine nat_sq_of_rat (2 * b * N) ?_
    have h1 : (d : ℝ) = 4 * (b : ℝ) ^ 2 * N := by
      have : (D : ℝ) = d := by rw [hd]; simp
      rw [← this, hDR, hdiff]; linear_combination (4 * (b : ℝ) ^ 2) * hs
    push_cast
    rw [show ((2 : ℝ) * b * N) ^ 2 = (4 * (b : ℝ) ^ 2 * N) * N by ring, ← h1]
  have hxcos : Real.cos θ = x / 2 := by rw [hxdef]; ring
  rcases hcases with ⟨hU0, hD8⟩ | ⟨hU0, hD12⟩ | ⟨hU1, hD5⟩ | ⟨hU1, hD5⟩
  · 
    left
    have hW : W = -2 := by rw [hU0, hD8] at hW4; omega
    have hx2 : x ^ 2 = 2 := by
      have hxx' : x' = -x := by
        have : (U : ℝ) = 0 := by rw [hU0]; simp
        linarith
      have : (W : ℝ) = -2 := by rw [hW]; simp
      rw [← hprod, hxx'] at this; linarith
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    obtain ⟨j, hj⟩ := hND 8 (by rw [hD8]; norm_num)
    refine ⟨?_, kernel2 hj⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx2.trans hs2.symm) with e | e
    · left
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [hxcos, e, Real.cos_pi_div_four]
    · right
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [show π * (3 / 4) = π - π / 4 by ring, Real.cos_pi_sub, Real.cos_pi_div_four, hxcos, e]; ring
  · right; left
    have hW : W = -3 := by rw [hU0, hD12] at hW4; omega
    have hx2 : x ^ 2 = 3 := by
      have hxx' : x' = -x := by
        have : (U : ℝ) = 0 := by rw [hU0]; simp
        linarith
      have : (W : ℝ) = -3 := by rw [hW]; simp
      rw [← hprod, hxx'] at this; linarith
    have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    obtain ⟨j, hj⟩ := hND 12 (by rw [hD12]; norm_num)
    refine ⟨?_, kernel3 hj⟩
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx2.trans hs3.symm) with e | e
    · left
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [hxcos, e, Real.cos_pi_div_six]
    · right
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [show π * (5 / 6) = π - π / 6 by ring, Real.cos_pi_sub, Real.cos_pi_div_six, hxcos, e]; ring
  all_goals
    right; right
    have hW : W = -1 := by rw [hU1, hD5] at hW4; omega
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hq : x ^ 2 - U * x + W = 0 := by
      have : x' = U - x := by linarith
      rw [← hprod, this]; ring
    have hWR : (W : ℝ) = -1 := by rw [hW]; simp
    have hU2 : (U : ℝ) ^ 2 = 1 := by rw [hU1]; norm_num
    have hroot : x = (U + Real.sqrt 5) / 2 ∨ x = (U - Real.sqrt 5) / 2 := by
      have h : (x - (U + Real.sqrt 5) / 2) * (x - (U - Real.sqrt 5) / 2) = 0 := by
        linear_combination hq - hWR + (1 / 4) * hU2 - (1 / 4) * h5
      rcases mul_eq_zero.mp h with h | h
      · left; linarith
      · right; linarith
    obtain ⟨j, hj⟩ := hND 5 (by rw [hD5]; norm_num)
    refine ⟨?_, kernel5 hj⟩
    have c5 := Real.cos_pi_div_five
    have c25 := cos_two_pi_div_five
    have hr5 : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
    have hUR : (U : ℝ) = 1 ∨ (U : ℝ) = -1 := by
      have : U = 1 ∨ U = -1 := by omega
      rcases this with h | h
      · left; rw [h]; simp
      · right; rw [h]; simp
    rcases hUR with hu | hu <;> rcases hroot with e | e
    · left
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [hxcos, e, hu, Real.cos_pi_div_five]; ring
    · right; right; left
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [show π * (3 / 5) = π - 2 * π / 5 by ring, Real.cos_pi_sub, c25, hxcos, e, hu]; ring
    · right; left
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [show π * (2 / 5) = 2 * π / 5 by ring, c25, hxcos, e, hu]; ring
    · right; right; right
      refine theta_eq_of_cos hθ0.le hθπ.le (by positivity) (by linarith) ?_
      rw [show π * (4 / 5) = π - π / 5 by ring, Real.cos_pi_sub, c5, hxcos, e, hu]; ring
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
namespace Erdos634.Draft.LaczFormal
def TagCore (N n : ℕ) : Prop :=
  (n = 20 ∨ n = 30 ∨ n = 40) ∨ ((n = 15 ∨ n = 45) ∧ ∃ k : ℕ, N = 2 * k ^ 2) ∨
  ((n = 10 ∨ n = 50) ∧ ∃ k : ℕ, N = 3 * k ^ 2) ∨
  ((n = 12 ∨ n = 24 ∨ n = 36 ∨ n = 48) ∧ ∃ k : ℕ, N = 5 * k ^ 2)
def TagOK (N : ℕ) (θ : ℝ) : Prop := ∃ n : ℕ, θ = (n : ℝ) / 60 * π ∧ TagCore N n
theorem tagOK_of_Q {N : ℕ} {θ : ℝ}
    (h : (θ = π / 3 ∨ θ = π / 2 ∨ θ = π * (2 / 3)) ∨
    ((θ = π / 4 ∨ θ = π * (3 / 4)) ∧ ∃ k : ℕ, N = 2 * k ^ 2) ∨
    ((θ = π / 6 ∨ θ = π * (5 / 6)) ∧ ∃ k : ℕ, N = 3 * k ^ 2) ∨
    ((θ = π / 5 ∨ θ = π * (2 / 5) ∨ θ = π * (3 / 5) ∨ θ = π * (4 / 5)) ∧ ∃ k : ℕ, N = 5 * k ^ 2)) :
    TagOK N θ := by
  rcases h with (h | h | h) | ⟨h | h, k⟩ | ⟨h | h, k⟩ | ⟨h | h | h | h, k⟩
  · exact ⟨20, by rw [h]; push_cast; ring, Or.inl (by omega)⟩
  · exact ⟨30, by rw [h]; push_cast; ring, Or.inl (by omega)⟩
  · exact ⟨40, by rw [h]; push_cast; ring, Or.inl (by omega)⟩
  · exact ⟨15, by rw [h]; push_cast; ring, Or.inr (Or.inl ⟨by omega, k⟩)⟩
  · exact ⟨45, by rw [h]; push_cast; ring, Or.inr (Or.inl ⟨by omega, k⟩)⟩
  · exact ⟨10, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inl ⟨by omega, k⟩))⟩
  · exact ⟨50, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inl ⟨by omega, k⟩))⟩
  · exact ⟨12, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inr ⟨by omega, k⟩))⟩
  · exact ⟨24, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inr ⟨by omega, k⟩))⟩
  · exact ⟨36, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inr ⟨by omega, k⟩))⟩
  · exact ⟨48, by rw [h]; push_cast; ring, Or.inr (Or.inr (Or.inr ⟨by omega, k⟩))⟩
def VAL (n : ℕ) : Prop := n = 20 ∨ n = 30 ∨ n = 40 ∨ n = 15 ∨ n = 45 ∨ n = 10 ∨ n = 50 ∨ n = 12 ∨ n = 24 ∨ n = 36 ∨ n = 48
theorem val_of_tag {N n : ℕ} (t : TagCore N n) : VAL n := by
  unfold TagCore at t
  rcases t with h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> unfold VAL <;> omega
theorem tag2 {N n : ℕ} (t : TagCore N n) (h : n = 15 ∨ n = 45) : ∃ m : ℕ, N = 2 * m ^ 2 := by
  rcases t with h' | ⟨-, k⟩ | ⟨h', -⟩ | ⟨h', -⟩
  · omega
  · exact k
  · omega
  · omega
theorem tag3 {N n : ℕ} (t : TagCore N n) (h : n = 10 ∨ n = 50) : ∃ m : ℕ, N = 3 * m ^ 2 := by
  rcases t with h' | ⟨h', -⟩ | ⟨-, k⟩ | ⟨h', -⟩
  · omega
  · omega
  · exact k
  · omega
theorem tag5 {N n : ℕ} (t : TagCore N n) (h : n = 12 ∨ n = 24 ∨ n = 36 ∨ n = 48) :
    ∃ m : ℕ, N = 5 * m ^ 2 := by
  rcases t with h' | ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, k⟩
  · omega
  · omega
  · omega
  · exact k
def SLIST : List ℕ := [20, 30, 40, 15, 45, 10, 50, 12, 24, 36, 48]
def ALLOWED : List (ℕ × ℕ × ℕ) := [(20, 20, 20), (20, 30, 10), (20, 10, 30), (30, 20, 10), (30, 15, 15), (30, 10, 20), (40, 10, 10), (15, 30, 15), (15, 15, 30), (10, 20, 30), (10, 30, 20), (10, 40, 10), (10, 10, 40), (12, 12, 36), (12, 24, 24), (12, 36, 12), (24, 12, 24), (24, 24, 12), (36, 12, 12)]
theorem key_class : ∀ a ∈ SLIST, ∀ b ∈ SLIST, ∀ c ∈ SLIST, a + b + c = 60 → (a, b, c) ∈ ALLOWED := by
  decide +kernel
theorem val_mem {n : ℕ} (v : VAL n) : n ∈ SLIST := by
  unfold VAL at v; unfold SLIST; simp; omega
theorem nat_class (n0 n1 n2 : ℕ) (hs : n0 + n1 + n2 = 60) (v0 : VAL n0) (v1 : VAL n1) (v2 : VAL n2) :
  (n0 = 20 ∧ n1 = 20 ∧ n2 = 20) ∨ (n0 = 20 ∧ n1 = 30 ∧ n2 = 10) ∨ (n0 = 20 ∧ n1 = 10 ∧ n2 = 30) ∨ (n0 = 30 ∧ n1 = 20 ∧ n2 = 10) ∨ (n0 = 30 ∧ n1 = 15 ∧ n2 = 15) ∨ (n0 = 30 ∧ n1 = 10 ∧ n2 = 20) ∨ (n0 = 40 ∧ n1 = 10 ∧ n2 = 10) ∨ (n0 = 15 ∧ n1 = 30 ∧ n2 = 15) ∨ (n0 = 15 ∧ n1 = 15 ∧ n2 = 30) ∨ (n0 = 10 ∧ n1 = 20 ∧ n2 = 30) ∨ (n0 = 10 ∧ n1 = 30 ∧ n2 = 20) ∨ (n0 = 10 ∧ n1 = 40 ∧ n2 = 10) ∨ (n0 = 10 ∧ n1 = 10 ∧ n2 = 40) ∨ (n0 = 12 ∧ n1 = 12 ∧ n2 = 36) ∨ (n0 = 12 ∧ n1 = 24 ∧ n2 = 24) ∨ (n0 = 12 ∧ n1 = 36 ∧ n2 = 12) ∨ (n0 = 24 ∧ n1 = 12 ∧ n2 = 24) ∨ (n0 = 24 ∧ n1 = 24 ∧ n2 = 12) ∨ (n0 = 36 ∧ n1 = 12 ∧ n2 = 12) := by
  have := key_class n0 (val_mem v0) n1 (val_mem v1) n2 (val_mem v2) hs
  simpa [ALLOWED] using this
theorem class_of_rational {N : ℕ} (D : CongruentDissection N)
    (htag : ∀ k, TagOK N (D.model.angleAt k)) :
    (∀ k, D.model.angleAt k = π / 3) ∨
    ((∃ m : ℕ, N = 2 * m ^ 2) ∧ TileAngles D (π / 4) (π / 4) (π / 2)) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 6) (2 * π / 3)) ∨
    ((∃ m : ℕ, N = 5 * m ^ 2) ∧ TileAngles D (π / 5) (2 * π / 5) (2 * π / 5)) ∨
    ((∃ m : ℕ, N = 5 * m ^ 2) ∧ TileAngles D (π / 5) (π / 5) (3 * π / 5)) := by
  have hpi := Real.pi_pos
  obtain ⟨n0, hθ0, t0⟩ := htag 0
  obtain ⟨n1, hθ1, t1⟩ := htag 1
  obtain ⟨n2, hθ2, t2⟩ := htag 2
  have hsum := angleAt_sum D.model
  rw [hθ0, hθ1, hθ2] at hsum
  have h60 : (((n0 : ℝ) + n1 + n2 - 60)) * π = 0 := by linear_combination 60 * hsum
  have h60' : ((n0 : ℝ) + n1 + n2 - 60) = 0 := (mul_eq_zero.mp h60).resolve_right hpi.ne'
  have hn : n0 + n1 + n2 = 60 := by
    have : ((n0 + n1 + n2 : ℕ) : ℝ) = 60 := by push_cast; linarith
    exact_mod_cast this
  have base : TileAngles D (D.model.angleAt 0) (D.model.angleAt 1) (D.model.angleAt 2) :=
    ⟨1, rfl, rfl, rfl⟩
  have hc := nat_class n0 n1 n2 hn (val_of_tag t0) (val_of_tag t1) (val_of_tag t2)
  rcases hc with hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    left
    intro k
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by fin_cases k <;> simp) with rfl | rfl | rfl
    · rw [hθ0]; push_cast; ring
    · rw [hθ1]; push_cast; ring
    · rw [hθ2]; push_cast; ring
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t2 (by omega), (((base).swap23).swap).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t1 (by omega), ((base).swap).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t2 (by omega), ((((base).swap).swap23).swap).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; left
    refine ⟨tag2 t1 (by omega), (((base).swap).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t1 (by omega), (((base).swap).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; left
    refine ⟨tag3 t1 (by omega), (((base).swap).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; left
    refine ⟨tag2 t0 (by omega), ((base).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; left
    refine ⟨tag2 t0 (by omega), (base).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t0 (by omega), (base).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; left
    refine ⟨tag3 t0 (by omega), ((base).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; left
    refine ⟨tag3 t0 (by omega), ((base).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; left
    refine ⟨tag3 t0 (by omega), (base).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; right
    refine ⟨tag5 t0 (by omega), (base).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; left
    refine ⟨tag5 t0 (by omega), (base).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; right
    refine ⟨tag5 t0 (by omega), ((base).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; left
    refine ⟨tag5 t0 (by omega), ((base).swap).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; left
    refine ⟨tag5 t0 (by omega), (((base).swap23).swap).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
  · obtain ⟨h0', h1', h2'⟩ := hcase
    subst h0' h1' h2'
    right; right; right; right; right
    refine ⟨tag5 t0 (by omega), (((base).swap).swap23).cast (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring) (by simp only [hθ0, hθ1, hθ2]; push_cast; ring)⟩
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
namespace Erdos634.Draft.LaczFormal
def RightLegs {N : ℕ} (D : CongruentDissection N) (A B : ℕ) : Prop :=
  ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ D.model.angleAt k = π / 2 ∧
    D.model.oppLen i * B = D.model.oppLen j * A
theorem sorted_general {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hsq : ¬ IsSquare N)
    (h01 : D.model.angleAt 0 < D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hmult : ∀ k : ℕ, D.model.angleAt 1 ≠ k * D.model.angleAt 0)
    (hscal : ∀ k k', k ≠ k' → D.model.oppLen k ≠ D.model.oppLen k') :
    ∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ D.model.angleAt 2 = π / 2 ∧
      D.model.oppLen 0 * B = D.model.oppLen 1 * A := by
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  have hang : ∀ k, D.target.angleAt k = D.model.angleAt k := fun k => (hsim k).1
  have hA := Row2.cornerA D hang h01 h12
  have hB := Row2.cornerB D hang h01 h12 hmult
  obtain ⟨-, -, -, -, h22, -⟩ := Row2.lemmaD_tiling D μ hside hscal hsq hA hB
  have hR := Row2.lemmaR D hang h01 h12 (Row2.noc_of_sideCount D h22)
  obtain ⟨hμ, hp⟩ := Row2.mu_irrational D μ hside hsq
  obtain ⟨e0, e1, -⟩ := Row2.lemmaD_scale D.sideCount D.model.oppLen D.model.oppLen_pos hμ hp
    (Row2.sideCount_eigen D μ hside hscal) (Row2.sideCount_rows D hscal) hA hB
  have hμ2 : μ ^ 2 = N := by rw [hp]; push_cast; ring
  have hπ2 : D.model.angleAt 2 = π / 2 := by linarith
  have hcos : Real.cos (D.model.angleAt 2) = 0 := by rw [hπ2]; exact Real.cos_pi_div_two
  have hl := D.model.lawCos 2
  rw [hcos] at hl
  simp only [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at hl
  have hc := D.model.oppLen_pos 2
  have hpy : D.model.oppLen 2 ^ 2 = D.model.oppLen 0 ^ 2 + D.model.oppLen 1 ^ 2 := by
    linarith [hl]
  have key : (N : ℝ) * D.model.oppLen 2 ^ 2
      = (((D.sideCount 0 2 : ℕ) : ℝ) ^ 2 + ((D.sideCount 1 2 : ℕ) : ℝ) ^ 2)
        * D.model.oppLen 2 ^ 2 := by
    have h1 : (N : ℝ) * D.model.oppLen 2 ^ 2
        = (μ * D.model.oppLen 0) ^ 2 + (μ * D.model.oppLen 1) ^ 2 := by
      rw [← hμ2, hpy]; ring
    rw [h1, e0, e1]; ring
  have hN' : (N : ℝ) = ((D.sideCount 0 2 : ℕ) : ℝ) ^ 2 + ((D.sideCount 1 2 : ℕ) : ℝ) ^ 2 :=
    mul_right_cancel₀ (pow_ne_zero 2 hc.ne') key
  have hμpos : 0 < μ := by
    have := (hside 0); have h1 := D.target.oppLen_pos 0; have h2 := D.model.oppLen_pos 0
    by_contra hc; push Not at hc; nlinarith
  refine ⟨_, _, by exact_mod_cast hN', hπ2, ?_⟩
  refine mul_left_cancel₀ hμpos.ne' ?_
  have hv0 := D.model.oppLen_pos 0
  linear_combination (D.sideCount 1 2 : ℝ) * e0 - (D.sideCount 0 2 : ℝ) * e1
theorem no_multiple_case {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hsq : ¬ IsSquare N)
    (hE : ∀ i j : Fin 3, i ≠ j → ∀ k : ℕ, D.model.angleAt j ≠ k * D.model.angleAt i) :
    ∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B := by
  have hscal : ∀ i j : Fin 3, i ≠ j → D.model.oppLen i ≠ D.model.oppLen j := fun i j hij hl => by
    have := D.model.angle_eq_of_oppLen_eq hij hl
    exact hE i j hij 1 (by rw [this]; simp)
  have hdist : ∀ i j : Fin 3, i ≠ j → D.model.angleAt i ≠ D.model.angleAt j := fun i j hij h =>
    hE i j hij 1 (by rw [h]; simp)
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin 3), Monotone (D.model.angleAt ∘ σ) :=
    ⟨_, Tuple.monotone_sort _⟩
  have h01 : D.model.angleAt (σ 0) < D.model.angleAt (σ 1) :=
    lt_of_le_of_ne (hmono (show (0 : Fin 3) ≤ 1 by decide))
      (hdist _ _ (σ.injective.ne (by decide)))
  have h12 : D.model.angleAt (σ 1) < D.model.angleAt (σ 2) :=
    lt_of_le_of_ne (hmono (show (1 : Fin 3) ≤ 2 by decide))
      (hdist _ _ (σ.injective.ne (by decide)))
  let D' : CongruentDissection N :=
    { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σ
      model := D.model.relabel σ
      tiles_congruent := fun i => (D.tiles_congruent i).relabel σ }
  have hTa := Row2.angleAt_comp D.target D'.target σ (fun k => rfl)
  have hMa := Row2.angleAt_comp D.model D'.model σ (fun k => rfl)
  have hsim' : ∀ k, D'.target.angleAt k = D'.model.angleAt k ∧
      D'.target.oppLen k = μ * D'.model.oppLen k := by
    intro k
    rw [(hTa k).1, (hMa k).1, (hTa k).2, (hMa k).2]
    exact hsim (σ k)
  obtain ⟨A, B, hAB, hr⟩ := sorted_general D' μ hsim' hsq
    (by rw [(hMa 0).1, (hMa 1).1]; exact h01) (by rw [(hMa 1).1, (hMa 2).1]; exact h12)
    (fun k => by rw [(hMa 1).1, (hMa 0).1]; exact hE (σ 0) (σ 1) (σ.injective.ne (by decide)) k)
    (fun k k' hkk' => by
      rw [(hMa k).2, (hMa k').2]
      exact hscal _ _ (σ.injective.ne hkk'))
  obtain ⟨hr, hleg⟩ := hr
  refine ⟨A, B, hAB, σ 0, σ 1, σ 2, σ.injective.ne (by decide), σ.injective.ne (by decide),
    σ.injective.ne (by decide), by rw [← (hMa 2).1]; exact hr, ?_⟩
  rw [← (hMa 0).2, ← (hMa 1).2]; exact hleg
theorem rat_of_multiple (θ : Fin 3 → ℝ) (hsum : θ 0 + θ 1 + θ 2 = π)
    (hπ : ∃ y ∈ AddSubgroup.closure ({θ 0, θ 1, π} : Set ℝ), π = 2 * y)
    {i j : Fin 3} (hij : i ≠ j) (k : ℕ) (hjk : θ j = k * θ i) : ∀ l, ∃ r : ℚ, θ l = r * π := by
  set H : AddSubgroup ℝ := AddSubgroup.zmultiples (θ i) ⊔ AddSubgroup.zmultiples π with hH
  have mem : ∀ a b : ℤ, (a : ℝ) * θ i + b * π ∈ H := by
    intro a b
    refine AddSubgroup.mem_sup.mpr ⟨a * θ i, ?_, b * π, ?_, rfl⟩
    · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨a, by rw [zsmul_eq_mul]⟩
    · exact AddSubgroup.mem_zmultiples_iff.mpr ⟨b, by rw [zsmul_eq_mul]⟩
  have hall : ∀ l, θ l ∈ H := by
    intro l
    by_cases hli : l = i
    · rw [hli]; simpa using mem 1 0
    by_cases hlj : l = j
    · rw [hlj, hjk]; simpa using mem k 0
    · rw [Row2.third_angle θ hsum hij hli hlj, hjk]
      have := mem (-(k : ℤ) - 1) 1
      convert this using 1
      push_cast; ring
  have hle : AddSubgroup.closure ({θ 0, θ 1, π} : Set ℝ) ≤ H := by
    rw [AddSubgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hall 0
    · exact hall 1
    · simpa using mem 0 1
  obtain ⟨y, hyΛ, hy⟩ := hπ
  obtain ⟨u, hu, w, hw, huw⟩ := AddSubgroup.mem_sup.mp (hle hyΛ)
  obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hu
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw
  rw [zsmul_eq_mul, zsmul_eq_mul] at huw
  rw [← huw] at hy
  have hm : m ≠ 0 := by
    rintro rfl
    have h0 : (1 - 2 * (n : ℝ)) * π = 0 := by push_cast at hy; linear_combination hy
    have h1 : (1 : ℝ) - 2 * n = 0 := (mul_eq_zero.mp h0).resolve_right Real.pi_ne_zero
    have h2 : (1 : ℤ) - 2 * n = 0 := by exact_mod_cast h1
    omega
  have hm' : (2 * (m : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast hm)
  have hφrat : θ i = (((1 - 2 * n : ℤ) : ℚ) / (2 * m) : ℚ) * π := by
    have e : (2 * (m : ℝ)) * θ i = (1 - 2 * n) * π := by linear_combination (-1 : ℝ) * hy
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff hm']
    linear_combination e
  intro l
  have hrat : ∀ l, ∃ r : ℚ, θ l = r * π := by
    intro l
    obtain ⟨u', hu', w', hw', huw'⟩ := AddSubgroup.mem_sup.mp (hall l)
    obtain ⟨a, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hu'
    obtain ⟨b, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hw'
    rw [zsmul_eq_mul, zsmul_eq_mul, hφrat] at huw'
    exact ⟨a * (((1 - 2 * n : ℤ) : ℚ) / (2 * m)) + b, by rw [← huw']; push_cast; ring⟩
  exact hrat l
theorem similar_partial {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : ¬ IsSquare N) :
    (∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 6) (2 * π / 3)) ∨
    ((∃ m : ℕ, N = 5 * m ^ 2) ∧ TileAngles D (π / 5) (2 * π / 5) (2 * π / 5)) ∨
    ((∃ m : ℕ, N = 5 * m ^ 2) ∧ TileAngles D (π / 5) (π / 5) (3 * π / 5)) := by
  obtain ⟨⟨hNμ, hμq⟩, hπ, -, hnot, hcos⟩ := similar_reduction D μ hsim hN
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  have hμ2 : μ ^ 2 = N := hNμ.symm
  by_cases hE : ∀ i j : Fin 3, i ≠ j → ∀ k : ℕ, D.model.angleAt j ≠ k * D.model.angleAt i
  · exact Or.inl (no_multiple_case D μ hsim hN hE)
  push Not at hE
  obtain ⟨i, j, hij, k, hjk⟩ := hE
  have hsum := angleAt_sum D.model
  have hrat := rat_of_multiple D.model.angleAt hsum hπ hij k hjk
  have htag : ∀ l, TagOK N (D.model.angleAt l) := by
    intro l
    have hl0 := D.model.angleAt_pos' l
    have hlπ : D.model.angleAt l < π := by
      have h0 := D.model.angleAt_pos' 0
      have h1 := D.model.angleAt_pos' 1
      have h2 := D.model.angleAt_pos' 2
      rcases (show l = 0 ∨ l = 1 ∨ l = 2 by fin_cases l <;> simp) with rfl | rfl | rfl <;> linarith
    exact tagOK_of_Q (lemmaQ_general hN hμ2 (hrat l) hl0 hlπ (hcos l))
  rcases class_of_rational D htag with hall | ⟨⟨m, hm⟩, hT⟩ | h | h | h | h
  · exfalso
    have hsin : Real.sin (π / 3) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
    have hs : ∀ i j, D.model.oppLen i = D.model.oppLen j := by
      intro i j
      have h := D.model.lawSin i j
      rw [hall i, hall j] at h
      exact (mul_left_cancel₀ hsin h).symm
    exact hnot ⟨⟨1, by rw [hs 0 2]; simp⟩, ⟨1, by rw [hs 1 2]; simp⟩⟩
  · left
    obtain ⟨σ, h0, h1, h2⟩ := hT
    refine ⟨m, m, by rw [hm]; ring, σ 0, σ 1, σ 2, σ.injective.ne (by decide),
      σ.injective.ne (by decide), σ.injective.ne (by decide), h2, ?_⟩
    have hl := D.model.lawSin (σ 0) (σ 1)
    rw [h0, h1] at hl
    have hsp : 0 < Real.sin (π / 4) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
    have := mul_left_cancel₀ hsp.ne' (by linarith : Real.sin (π / 4) * D.model.oppLen (σ 1) = Real.sin (π / 4) * D.model.oppLen (σ 0))
    rw [this]
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFinal
namespace Erdos634.Draft.LaczFormal
theorem golden_arith {N X a : ℕ} {μ : ℝ} (hNm : μ ^ 2 = N) (hμq : ¬ ∃ r : ℚ, μ = r)
    (h : μ = X + a * ((1 + Real.sqrt 5) / 2)) : False := by
  have h5 : ¬ IsSquare 5 := by
    rintro ⟨m, hm⟩
    have : m ≤ 2 := by nlinarith
    interval_cases m <;> omega
  have hirr5 : Irrational (Real.sqrt 5) := by
    have := irrational_sqrt_natCast_iff.mpr h5
    simpa using this
  have s2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  by_cases ha : a = 0
  · exact hμq ⟨X, by rw [h, ha]; simp⟩
  have hapos : (0 : ℝ) < a := by exact_mod_cast Nat.pos_of_ne_zero ha
  have hc : 0 < ((X : ℝ) + a / 2) * a := by positivity
  apply hirr5
  refine ⟨((N : ℚ) - ((X : ℚ) + a / 2) ^ 2 - 5 * (a : ℚ) ^ 2 / 4) / (((X : ℚ) + a / 2) * a), ?_⟩
  push_cast
  rw [div_eq_iff hc.ne']
  have hN' : (N : ℝ) = (X + a * ((1 + Real.sqrt 5) / 2)) ^ 2 := by rw [← h, hNm]
  linear_combination hN' + (a : ℝ) ^ 2 / 4 * s2
theorem kill_golden_acute {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) (hNm : μ ^ 2 = N)
    (hμq : ¬ ∃ r : ℚ, μ = r) (hT : TileAngles D (π / 5) (2 * π / 5) (2 * π / 5)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  have hpq : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have hpr : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have hqr : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have hpi := Real.pi_pos
  have sp : 0 < Real.sin (π / 5) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have s25 : Real.sin (2 * π / 5) = Real.sin (π / 5) * ((1 + Real.sqrt 5) / 2) := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.sin_two_mul, Real.cos_pi_div_five]; ring
  set p := σ 0; set q := σ 1; set r := σ 2
  have hvp := D.model.oppLen_pos p
  have rq : D.model.oppLen q = ((1 + Real.sqrt 5) / 2) * D.model.oppLen p := by
    have h := D.model.lawSin p q
    rw [h0, h1, s25] at h
    have : Real.sin (π / 5) * D.model.oppLen q =
        Real.sin (π / 5) * (((1 + Real.sqrt 5) / 2) * D.model.oppLen p) := by linarith
    exact mul_left_cancel₀ sp.ne' this
  have rr : D.model.oppLen r = ((1 + Real.sqrt 5) / 2) * D.model.oppLen p := by
    have h := D.model.lawSin p r
    rw [h0, h2, s25] at h
    have : Real.sin (π / 5) * D.model.oppLen r =
        Real.sin (π / 5) * (((1 + Real.sqrt 5) / 2) * D.model.oppLen p) := by linarith
    exact mul_left_cancel₀ sp.ne' this
  have hrow := Row2.sideCountT_eigen D μ hside p
  rw [Fin.sum_univ_three] at hrow
  have hs3 : ∀ f : Fin 3 → ℝ, f p + f q + f r = f 0 + f 1 + f 2 := fun f =>
    sum3 f p q r hpq hpr hqr
  rw [← hs3 (fun j => (D.sideCountT p j : ℝ) * D.model.oppLen j), ] at hrow
  simp only [rq, rr] at hrow
  refine golden_arith (N := N) (X := D.sideCountT p p) (a := D.sideCountT p q + D.sideCountT p r) hNm hμq ?_
  push_cast
  have := mul_right_cancel₀ hvp.ne' (by linarith : (↑(D.sideCountT p p) + (↑(D.sideCountT p q) + ↑(D.sideCountT p r)) * ((1 + Real.sqrt 5) / 2)) * D.model.oppLen p = μ * D.model.oppLen p)
  linarith
theorem kill_golden_obtuse {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k) (hNm : μ ^ 2 = N)
    (hμq : ¬ ∃ r : ℚ, μ = r) (hT : TileAngles D (π / 5) (π / 5) (3 * π / 5)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  have hpq : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have hpr : σ 0 ≠ σ 2 := σ.injective.ne (by decide)
  have hqr : σ 1 ≠ σ 2 := σ.injective.ne (by decide)
  have hpi := Real.pi_pos
  have sp : 0 < Real.sin (π / 5) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith)
  have s25 : Real.sin (2 * π / 5) = Real.sin (π / 5) * ((1 + Real.sqrt 5) / 2) := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, Real.sin_two_mul, Real.cos_pi_div_five]; ring
  have s35 : Real.sin (3 * π / 5) = Real.sin (π / 5) * ((1 + Real.sqrt 5) / 2) := by
    rw [show 3 * π / 5 = π - 2 * π / 5 by ring, Real.sin_pi_sub, s25]
  set p := σ 0; set q := σ 1; set r := σ 2
  have hvp := D.model.oppLen_pos p
  have rq : D.model.oppLen q = D.model.oppLen p := by
    have h := D.model.lawSin p q
    rw [h0, h1] at h
    exact mul_left_cancel₀ sp.ne' (by linarith)
  have rr : D.model.oppLen r = ((1 + Real.sqrt 5) / 2) * D.model.oppLen p := by
    have h := D.model.lawSin p r
    rw [h0, h2, s35] at h
    have : Real.sin (π / 5) * D.model.oppLen r =
        Real.sin (π / 5) * (((1 + Real.sqrt 5) / 2) * D.model.oppLen p) := by linarith
    exact mul_left_cancel₀ sp.ne' this
  have hrow := Row2.sideCountT_eigen D μ hside p
  rw [Fin.sum_univ_three] at hrow
  have hs3 : ∀ f : Fin 3 → ℝ, f p + f q + f r = f 0 + f 1 + f 2 := fun f =>
    sum3 f p q r hpq hpr hqr
  rw [← hs3 (fun j => (D.sideCountT p j : ℝ) * D.model.oppLen j)] at hrow
  simp only [rq, rr] at hrow
  refine golden_arith (N := N) (X := D.sideCountT p p + D.sideCountT p q) (a := D.sideCountT p r) hNm hμq ?_
  push_cast
  have := mul_right_cancel₀ hvp.ne' (by linarith : ((↑(D.sideCountT p p) + ↑(D.sideCountT p q)) + ↑(D.sideCountT p r) * ((1 + Real.sqrt 5) / 2)) * D.model.oppLen p = μ * D.model.oppLen p)
  linarith
theorem similar_partial2 {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : ¬ IsSquare N) :
    (∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 6) (2 * π / 3)) := by
  have hside : ∀ k, D.target.oppLen k = μ * D.model.oppLen k := fun k => (hsim k).2
  obtain ⟨⟨hNμ, hμq⟩, -⟩ := similar_reduction D μ hsim hN
  rcases similar_partial D μ hsim hN with h | h | h | ⟨-, hT⟩ | ⟨-, hT⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (kill_golden_acute D μ hside hNμ.symm hμq hT).elim
  · exact (kill_golden_obtuse D μ hside hNμ.symm hμq hT).elim
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
namespace Erdos634.Geometry
open Real
variable {N : ℕ}
theorem Row2.lemmaR_le (D : CongruentDissection N)
    (hang : ∀ k, D.target.angleAt k = D.model.angleAt k)
    (h01 : D.model.angleAt 0 ≤ D.model.angleAt 1) (h12 : D.model.angleAt 1 < D.model.angleAt 2)
    (hnoc : ∀ e ∈ D.sideEdges 0, D.eLen e ≠ D.model.oppLen 2) :
    2 * D.model.angleAt 2 = π := by
  classical
  have A_mem : D.target.pts 0 ∈ D.target.edge 0 := left_mem_segment ℝ _ _
  have B_mem : D.target.pts 1 ∈ D.target.edge 0 := right_mem_segment ℝ _ _
  have hnA : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ≠ D.target.pts 0 :=
    fun i k hk => Row2.no_gamma_corner D 0 i k hk (by rw [hang 0]; linarith)
  have hnB : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ≠ D.target.pts 1 :=
    fun i k hk => Row2.no_gamma_corner D 1 i k hk (by rw [hang 1]; exact h12)
  have tau_lt : ∀ i k, (D.tile i).angleAt k = D.model.angleAt 2 →
      (D.tile i).pts k ∈ D.target.edge 0 →
      0 < Row2.tau D.target ((D.tile i).pts k) ∧ Row2.tau D.target ((D.tile i).pts k) < 1 := by
    intro i k hk hmem
    obtain ⟨-, h0, h1, h2⟩ := Row2.edge0_coord D.target hmem
    constructor
    · rcases h1.lt_or_eq with h | h
      · exact h
      · exact absurd (Row2.tau_inj D.target hmem A_mem (h.symm.trans (Row2.tau_A D.target).symm))
          (hnA i k hk)
    · rcases (show Row2.tau D.target ((D.tile i).pts k) ≤ 1 by linarith).lt_or_eq with h | h
      · exact h
      · exact absurd (Row2.tau_inj D.target hmem B_mem (h.trans (Row2.tau_B D.target).symm))
          (hnB i k hk)
  have gend : ∀ e ∈ D.sideEdges 0, ∃ k, (D.tile e.1).angleAt k = D.model.angleAt 2 ∧
      (D.tile e.1).pts k ∈ D.eSet e ∧
      (Row2.tau D.target ((D.tile e.1).pts k) = Row2.lo D.toDissection e ∨
        Row2.tau D.target ((D.tile e.1).pts k) = Row2.hi D.toDissection e) := by
    intro e he
    obtain ⟨k, hk, hke⟩ := Row2.gamma_endpoint D (hnoc e he)
    obtain ⟨hX, hY⟩ := Row2.eq_inf_or_sup (Row2.tau D.target ((D.tile e.1).pts e.2))
      (Row2.tau D.target ((D.tile e.1).pts (e.2 + 1)))
    rcases hke with rfl | rfl
    · exact ⟨_, hk, left_mem_segment ℝ _ _, hX⟩
    · exact ⟨_, hk, right_mem_segment ℝ _ _, hY⟩
  obtain ⟨R, hR⟩ : ∃ R : Finset (Fin N × Fin 3), R = (D.sideEdges 0).filter (fun e =>
      ∃ k, (D.tile e.1).angleAt k = D.model.angleAt 2 ∧ (D.tile e.1).pts k ∈ D.eSet e ∧
        Row2.tau D.target ((D.tile e.1).pts k) = Row2.hi D.toDissection e) := ⟨_, rfl⟩
  obtain ⟨eA, heA, hAe⟩ := D.toDissection.exists_sideEdge_mem 0 A_mem
  have hReA : eA ∈ R := by
    obtain ⟨k, hk, hkm, hlh⟩ := gend eA heA
    have hpos := (tau_lt _ _ hk (Row2.sideEdge_sub D.toDissection heA hkm)).1
    have hlo : Row2.lo D.toDissection eA ≤ 0 := by
      have := ((Row2.mem_eSet_iff D.toDissection heA A_mem).mp hAe).1
      rwa [Row2.tau_A] at this
    rw [hR, Finset.mem_filter]
    refine ⟨heA, k, hk, hkm, ?_⟩
    rcases hlh with h | h
    · exfalso; linarith
    · exact h
  obtain ⟨eS, heSR, hmax⟩ := R.exists_max_image (Row2.hi D.toDissection) ⟨eA, hReA⟩
  rw [hR, Finset.mem_filter] at heSR
  obtain ⟨heS, kS, hkS, hkSm, hkSt⟩ := heSR
  obtain ⟨s, hs⟩ : ∃ s, s = Row2.hi D.toDissection eS := ⟨_, rfl⟩
  have hkSedge := Row2.sideEdge_sub D.toDissection heS hkSm
  have hs1 : s < 1 := by rw [hs, ← hkSt]; exact (tau_lt _ _ hkS hkSedge).2
  have hs0 : 0 < s := by rw [hs, ← hkSt]; exact (tau_lt _ _ hkS hkSedge).1
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin N × Fin 3),
      F = (D.sideEdges 0).filter (fun e => s < Row2.hi D.toDissection e) := ⟨_, rfl⟩
  obtain ⟨eB, heB, hBe⟩ := D.toDissection.exists_sideEdge_mem 0 B_mem
  have hFB : eB ∈ F := by
    rw [hF, Finset.mem_filter]
    refine ⟨heB, ?_⟩
    have := ((Row2.mem_eSet_iff D.toDissection heB B_mem).mp hBe).2
    rw [Row2.tau_B] at this
    linarith
  obtain ⟨e', he'F, hmin⟩ := F.exists_min_image (Row2.lo D.toDissection) ⟨eB, hFB⟩
  have he'F' := he'F
  rw [hF, Finset.mem_filter] at he'F'
  obtain ⟨he', he's⟩ := he'F'
  have hlo' : Row2.lo D.toDissection e' ≤ s := by
    by_contra hc
    push Not at hc
    obtain ⟨-, hhi1⟩ := Row2.lo_hi_bounds D.toDissection he'
    have hlohi := Row2.lo_lt_hi D.toDissection he'
    obtain ⟨z, hz, hzw⟩ := Row2.tau_surj D.target (s := (s + Row2.lo D.toDissection e') / 2)
      (by linarith) (by linarith)
    obtain ⟨e'', he'', hze''⟩ := D.toDissection.exists_sideEdge_mem 0 hz
    have hz'' := (Row2.mem_eSet_iff D.toDissection he'' hz).mp hze''
    rw [hzw] at hz''
    have he''F : e'' ∈ F := by
      rw [hF, Finset.mem_filter]; exact ⟨he'', by linarith [hz''.2]⟩
    have := hmin e'' he''F
    linarith [hz''.1]
  have hne : e' ≠ eS := by
    intro h; rw [h, ← hs] at he's; exact lt_irrefl _ he's
  have hlo'eq : Row2.lo D.toDissection e' = s := by
    by_contra hc
    have hlt : Row2.lo D.toDissection e' < s := lt_of_le_of_ne hlo' hc
    have hSlo := Row2.lo_lt_hi D.toDissection heS
    rw [← hs] at hSlo
    have hm1 := le_max_left (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e')
    have hm2 := le_max_right (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e')
    have hus : max (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e') < s := max_lt hSlo hlt
    exact Row2.interiors_disjoint D.toDissection heS he' hne.symm
      (s := (max (Row2.lo D.toDissection eS) (Row2.lo D.toDissection e') + s) / 2)
      (by linarith) (by rw [← hs]; linarith) (by linarith) (by linarith)
  obtain ⟨k', hk', hk'm, hk't⟩ := gend e' he'
  have hk's : Row2.tau D.target ((D.tile e'.1).pts k') = s := by
    rcases hk't with h | h
    · rw [h, hlo'eq]
    · exfalso
      have he'R : e' ∈ R := by
        rw [hR, Finset.mem_filter]; exact ⟨he', k', hk', hk'm, h⟩
      have := hmax e' he'R
      rw [← hs] at this
      linarith
  have hk'edge := Row2.sideEdge_sub D.toDissection he' hk'm
  have hP : (D.tile e'.1).pts k' = (D.tile eS.1).pts kS :=
    Row2.tau_inj D.target hk'edge hkSedge (hk's.trans (hs.trans hkSt.symm))
  have htiles : eS.1 ≠ e'.1 := Row2.distinct_tiles D.toDissection heS he' hne.symm
  have hPfr : (D.tile eS.1).pts kS ∈ frontier D.target.carrier :=
    Erdos634.SideWall.edge_subset_frontier D.target 0 hkSedge
  have hPnv : (D.tile eS.1).pts kS ∉ Set.range D.target.pts := by
    rintro ⟨m, hm⟩
    have hsP : Row2.tau D.target ((D.tile eS.1).pts kS) = s := hkSt.trans hs.symm
    rcases (show m = 0 ∨ m = 1 ∨ m = 2 by fin_cases m <;> simp) with rfl | rfl | rfl
    · rw [← hm, Row2.tau_A] at hsP; linarith
    · rw [← hm, Row2.tau_B] at hsP; linarith
    · have h2 := (Row2.edge0_coord D.target hkSedge).1
      rw [← hm] at h2
      have h1 : D.target.basis.coord 2 (D.target.pts 2) = 1 := D.target.basis.coord_apply_eq 2
      rw [h1] at h2; exact one_ne_zero h2
  have hsum := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hPfr hPnv
  have hS : (D.tile eS.1).localAngle ((D.tile eS.1).pts kS) = D.model.angleAt 2 := by
    rw [(D.tile eS.1).localAngle_vertex kS]; exact hkS
  have h' : (D.tile e'.1).localAngle ((D.tile eS.1).pts kS) = D.model.angleAt 2 := by
    rw [← hP, (D.tile e'.1).localAngle_vertex k']; exact hk'
  have h2π := Row2.angle2_lt_pi D.model
  refine Row2.two_gamma (fun i => (D.tile i).localAngle ((D.tile eS.1).pts kS))
    (θ0 := D.model.angleAt 0) (θ1 := D.model.angleAt 1)
    (fun i => (D.tile i).localAngle_nonneg _) ?_ hsum D.model.angleAt_sum h12 htiles hS h'
  intro i hi
  have hi' : (D.tile i).localAngle ((D.tile eS.1).pts kS) ≠ 0 := hi
  show D.model.angleAt 0 ≤ (D.tile i).localAngle ((D.tile eS.1).pts kS)
  have hα' : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = D.model.angleAt 0 := rfl
  have hβ' : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = D.model.angleAt 1 := rfl
  have hγ' : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = D.model.angleAt 2 := rfl
  have hv := Dissection.congruentDissection_localAngle_mem_boundary D
    (D.model.angleAt 0) (D.model.angleAt 1) (D.model.angleAt 2) hα' hβ' hγ' hPfr hPnv i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h | h | h | h | h
  · rw [h]
  · rw [h]; linarith
  · rw [h]; linarith
  · rw [h]; linarith
  · exact absurd h hi'
end Erdos634.Geometry
namespace Erdos634.Draft.LaczFormal
open Real Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFinal
theorem thirty_arith {N X Y : ℕ} {μ : ℝ} (hNm : μ ^ 2 = N) (hμq : ¬ ∃ r : ℚ, μ = r)
    (h : (X : ℝ) + Y * Real.sqrt 3 = μ * Real.sqrt 3) : Y = 0 := by
  have h3 : ¬ IsSquare 3 := by
    rintro ⟨m, hm⟩
    have : m ≤ 2 := by nlinarith
    interval_cases m <;> omega
  have hirr : Irrational (Real.sqrt 3) := by
    have := irrational_sqrt_natCast_iff.mpr h3
    simpa using this
  have s2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hμ : μ = (X : ℝ) / 3 * Real.sqrt 3 + Y := by
    have : μ * Real.sqrt 3 * Real.sqrt 3 = ((X : ℝ) + Y * Real.sqrt 3) * Real.sqrt 3 := by rw [h]
    have h33 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    linear_combination (1 / 3) * this - ((μ - Y) / 3) * h33
  by_contra hY
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast Nat.pos_of_ne_zero hY
  by_cases hX : X = 0
  · exact hμq ⟨Y, by rw [hμ, hX]; simp⟩
  have hXpos : (0 : ℝ) < X := by exact_mod_cast Nat.pos_of_ne_zero hX
  have hc : 0 < 2 * (X : ℝ) * Y / 3 := by positivity
  apply hirr
  refine ⟨((N : ℚ) - (X : ℚ) ^ 2 / 3 - (Y : ℚ) ^ 2) / (2 * (X : ℚ) * Y / 3), ?_⟩
  push_cast
  rw [div_eq_iff hc.ne']
  have hN' : (N : ℝ) = ((X : ℝ) / 3 * Real.sqrt 3 + Y) ^ 2 := by rw [← hμ, hNm]
  linear_combination hN' + ((X : ℝ) / 3) ^ 2 * s2
theorem noc_of_sideCountT {N : ℕ} (D : CongruentDissection N)
    (hv0 : D.model.oppLen 0 ≠ D.model.oppLen 2) (hv1 : D.model.oppLen 1 ≠ D.model.oppLen 2)
    (h : D.sideCountT 2 2 = 0) : ∀ e ∈ D.sideEdges 0, D.eLen e ≠ D.model.oppLen 2 := by
  intro e he heq
  have hty : D.eType e = 2 := by
    by_contra hne
    have := D.eLen_eType e
    rcases (show D.eType e = 0 ∨ D.eType e = 1 ∨ D.eType e = 2 by
      generalize D.eType e = k; fin_cases k <;> simp) with h' | h' | h'
    · rw [h'] at this; exact hv0 (this.symm.trans heq)
    · rw [h'] at this; exact hv1 (this.symm.trans heq)
    · exact hne h'
  have hcard : 0 < D.sideCountT 2 2 := by
    unfold CongruentDissection.sideCountT
    rw [show (2 : Fin 3) + 1 = 0 from rfl]
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hty⟩⟩
  omega
theorem kill_30_30_120 {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : ¬ IsSquare N) (hT : TileAngles D (π / 6) (π / 6) (2 * π / 3)) : False := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  let D' : CongruentDissection N :=
    { toDissection := Erdos634.NormalPosition.relabelTarget D.toDissection σ
      model := D.model.relabel σ
      tiles_congruent := fun i => (D.tiles_congruent i).relabel σ }
  have hTa := Row2.angleAt_comp D.target D'.target σ (fun k => rfl)
  have hMa := Row2.angleAt_comp D.model D'.model σ (fun k => rfl)
  have hsim' : ∀ k, D'.target.angleAt k = D'.model.angleAt k ∧
      D'.target.oppLen k = μ * D'.model.oppLen k := by
    intro k
    rw [(hTa k).1, (hMa k).1, (hTa k).2, (hMa k).2]
    exact hsim (σ k)
  have a0 : D'.model.angleAt 0 = π / 6 := by rw [(hMa 0).1]; exact h0
  have a1 : D'.model.angleAt 1 = π / 6 := by rw [(hMa 1).1]; exact h1
  have a2 : D'.model.angleAt 2 = 2 * π / 3 := by rw [(hMa 2).1]; exact h2
  have hside : ∀ k, D'.target.oppLen k = μ * D'.model.oppLen k := fun k => (hsim' k).2
  obtain ⟨⟨hNμ, hμq⟩, -⟩ := similar_reduction D' μ hsim' hN
  have hpi := Real.pi_pos
  have s6 : Real.sin (π / 6) = 1 / 2 := Real.sin_pi_div_six
  have s23 : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have hp3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hv0 := D'.model.oppLen_pos 0
  have v1 : D'.model.oppLen 1 = D'.model.oppLen 0 := by
    have h := D'.model.lawSin 0 1
    rw [a0, a1, s6] at h
    linarith
  have v2 : D'.model.oppLen 2 = Real.sqrt 3 * D'.model.oppLen 0 := by
    have h := D'.model.lawSin 0 2
    rw [a0, a2, s6, s23] at h
    linarith
  have hrow := Row2.sideCountT_eigen D' μ hside 2
  rw [Fin.sum_univ_three, v1, v2] at hrow
  have hY : D'.sideCountT 2 2 = 0 := by
    refine thirty_arith (N := N) (X := D'.sideCountT 2 0 + D'.sideCountT 2 1) hNμ.symm hμq ?_
    push_cast
    have := mul_right_cancel₀ hv0.ne' (by nlinarith [hrow] :
      ((↑(D'.sideCountT 2 0) + ↑(D'.sideCountT 2 1)) + ↑(D'.sideCountT 2 2) * Real.sqrt 3) * D'.model.oppLen 0
        = (μ * Real.sqrt 3) * D'.model.oppLen 0)
    linarith
  have hne0 : D'.model.oppLen 0 ≠ D'.model.oppLen 2 := by
    rw [v2]; intro h
    have : (1 - Real.sqrt 3) * D'.model.oppLen 0 = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · have : Real.sqrt 3 > 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    · exact hv0.ne' h'
  have hne1 : D'.model.oppLen 1 ≠ D'.model.oppLen 2 := by rw [v1]; exact hne0
  have hR := Row2.lemmaR_le D' (fun k => (hsim' k).1) (by rw [a0, a1])
    (by rw [a1, a2]; linarith) (noc_of_sideCountT D' hne0 hne1 hY)
  rw [a2] at hR
  linarith
theorem similar_reptile {N : ℕ} (D : CongruentDissection N) (μ : ℝ)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k ∧ D.target.oppLen k = μ * D.model.oppLen k)
    (hN : ¬ IsSquare N) :
    (∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) := by
  rcases similar_partial2 D μ hsim hN with h | h | ⟨-, hT⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (kill_30_30_120 D μ hsim hN hT).elim
theorem reptile_SWW {N : ℕ} (D : CongruentDissection N) (hs : SimilarTM D) :
    IsSquare N ∨ (∃ A B : ℕ, N = A ^ 2 + B ^ 2 ∧ RightLegs D A B) ∨
    ((∃ m : ℕ, N = 3 * m ^ 2) ∧ TileAngles D (π / 6) (π / 3) (π / 2)) := by
  by_cases hN : IsSquare N
  · exact Or.inl hN
  right
  obtain ⟨μ, τ, h⟩ := hs
  have hMa := Row2.angleAt_comp D.model (D.relabelModel τ).model τ (fun k => rfl)
  have hsim : ∀ k, (D.relabelModel τ).target.angleAt k = (D.relabelModel τ).model.angleAt k ∧
      (D.relabelModel τ).target.oppLen k = μ * (D.relabelModel τ).model.oppLen k := fun k => by
    rw [(hMa k).1, (hMa k).2]; exact h k
  rcases similar_reptile (D.relabelModel τ) μ hsim hN with ⟨A, B, hAB, i, j, k, hij, hik, hjk, hk, hl⟩ |
    ⟨m, σ, h0, h1, h2⟩
  · exact Or.inl ⟨A, B, hAB, τ i, τ j, τ k, τ.injective.ne hij, τ.injective.ne hik, τ.injective.ne hjk,
      by rw [← (hMa k).1]; exact hk, by rw [← (hMa i).2, ← (hMa j).2]; exact hl⟩
  · refine Or.inr ⟨m, σ.trans τ, ?_, ?_, ?_⟩
    · rw [Equiv.trans_apply, ← (hMa (σ 0)).1]; exact h0
    · rw [Equiv.trans_apply, ← (hMa (σ 1)).1]; exact h1
    · rw [Equiv.trans_apply, ← (hMa (σ 2)).1]; exact h2
end Erdos634.Draft.LaczFormal
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
variable {N : ℕ} (D : CongruentDissection N)
def TileSides (α β γ a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    D.model.angleAt (σ 0) = α ∧ D.model.angleAt (σ 1) = β ∧ D.model.angleAt (σ 2) = γ ∧
    D.model.oppLen (σ 0) = a ∧ D.model.oppLen (σ 1) = b ∧ D.model.oppLen (σ 2) = c
noncomputable def circumdiam (T : Tri) : ℝ := T.oppLen 0 / Real.sin (T.angleAt 0)
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.ThreeAlpha
open Erdos634.Geometry
theorem tri_angle_lt_pi (T : Tri) (k : Fin 3) : T.angleAt k < Real.pi := by
  have hs := T.angleAt_sum
  have h0 := T.angleAt_pos' 0
  have h1 := T.angleAt_pos' 1
  have h2 := T.angleAt_pos' 2
  fin_cases k <;> simp <;> linarith
theorem tri_sin_pos (T : Tri) (k : Fin 3) : 0 < Real.sin (T.angleAt k) :=
  Real.sin_pos_of_pos_of_lt_pi (T.angleAt_pos' k) (tri_angle_lt_pi T k)
theorem circumdiam_pos (T : Tri) : 0 < circumdiam T :=
  div_pos (T.oppLen_pos 0) (tri_sin_pos T 0)
theorem lawsin (T : Tri) (k : Fin 3) : T.oppLen k = circumdiam T * Real.sin (T.angleAt k) := by
  have hs0 := (tri_sin_pos T 0).ne'
  unfold circumdiam
  rw [div_mul_eq_mul_div, eq_div_iff hs0]
  have l0 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 0
  have l2 := Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T 2
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  rcases hk with rfl | rfl | rfl
  · ring
  · change Real.sin (T.angleAt 1) * T.oppLen 0 = Real.sin (T.angleAt 0) * T.oppLen 1 at l0
    linarith
  · change Real.sin (T.angleAt 0) * T.oppLen 2 = Real.sin (T.angleAt 2) * T.oppLen 0 at l2
    linarith
end TriangleTiling.ThreeAlpha
end

section
namespace TriangleTiling.Prime
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Real
open Erdos634.Draft.LaczFormal (TileAngles)
theorem similar_of_angles {N : ℕ} (D : CongruentDissection N) (σ : Equiv.Perm (Fin 3))
    (h : ∀ k, D.model.angleAt (σ k) = D.target.angleAt k) : SimilarTM D := by
  have hdm := ThreeAlpha.circumdiam_pos D.model
  refine ⟨ThreeAlpha.circumdiam D.target / ThreeAlpha.circumdiam D.model, σ, fun k => ⟨(h k).symm, ?_⟩⟩
  rw [ThreeAlpha.lawsin D.target k, ThreeAlpha.lawsin D.model (σ k), h k]
  field_simp
end TriangleTiling.Prime
end

section
namespace TriangleTiling.Prime
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles RightLegs)
theorem reptile {N : ℕ} (D : CongruentDissection N) (hs : SimilarTM D) :
    IsSquare N ∨ (∃ M K : ℕ, N = M ^ 2 + K ^ 2 ∧ RightLegs D M K) ∨
      ((∃ M : ℕ, N = 3 * M ^ 2) ∧ TileAngles D (Real.pi / 6) (Real.pi / 3) (Real.pi / 2)) :=
  Erdos634.Draft.LaczFormal.reptile_SWW D hs
theorem reptilenotprime {N : ℕ} (D : CongruentDissection N) (hs : SimilarTM D) (hN : N.Prime)
    (h2 : N ≠ 2) (h3 : N ≠ 3) :
    N % 4 = 1 ∧ ∃ M K : ℕ, N = M ^ 2 + K ^ 2 ∧ RightLegs D M K := by
  rcases reptile D hs with ⟨r, hr⟩ | ⟨M, K, hMK, hR⟩ | ⟨⟨M, hM⟩, -⟩
  · 
    exfalso
    rw [hr] at hN
    rcases Nat.prime_mul_iff.mp hN with ⟨hp, h1⟩ | ⟨hp, h1⟩
    · subst h1; exact Nat.not_prime_one hp
    · subst h1; exact Nat.not_prime_one hp
  · 
    refine ⟨?_, M, K, hMK, hR⟩
    have hodd : N % 2 = 1 := Nat.odd_iff.mp (hN.odd_of_ne_two h2)
    rw [hMK] at hodd ⊢
    have hM := Nat.mod_lt M (show 0 < 4 by norm_num)
    have hK := Nat.mod_lt K (show 0 < 4 by norm_num)
    have e : (M ^ 2 + K ^ 2) % 4 = ((M % 4) ^ 2 + (K % 4) ^ 2) % 4 := by
      simp [Nat.add_mod, Nat.pow_mod]
    have e2 : (M ^ 2 + K ^ 2) % 2 = ((M % 4) ^ 2 + (K % 4) ^ 2) % 2 := by
      rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 4 by norm_num), e, Nat.mod_mod_of_dvd _ (by norm_num)]
    rw [e]; rw [e2] at hodd
    interval_cases (M % 4) <;> interval_cases (K % 4) <;> simp_all
  · 
    exfalso
    rw [hM] at hN
    have hM1 : M ^ 2 = 1 := by
      rcases Nat.prime_mul_iff.mp hN with ⟨-, h⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h (by norm_num)
    exact h3 (by rw [hM, hM1])
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

end OMA.E634S


/-- Step H1 of erdos-634.R1: a prime tiling of a triangle similar to its tile has p = 1 mod 4. -/
theorem OMA.solution : OMA.R_erdos_634_R1.H1 := by
  intro p hp h3 T Ts hc hd hu t hs
  obtain ⟨σ, hσ⟩ := hs
  have hS : Erdos634.Draft.TheoremPConditional.SimilarTM (OMA.E634S.mk T Ts hc hd hu t) :=
    TriangleTiling.Prime.similar_of_angles _ σ (fun k => (hσ k).symm)
  exact (TriangleTiling.Prime.reptilenotprime _ hS hp (by omega) (by omega)).1
