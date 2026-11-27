import OMAReductions.R_erdos_634_R1_H3_R1

/-!
# Erdos 634, step erdos-634.R1.H3.R1.H3 (n 5-smooth, n > 200)

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
theorem sum_three_values {ι : Type*} (s : Finset ι) (len : ι → ℝ) (a b c : ℝ)
    (h : ∀ e ∈ s, len e = a ∨ len e = b ∨ len e = c) :
    ∃ P Q R : ℕ, ((P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c = ∑ e ∈ s, len e)
      ∧ P + Q + R = s.card := by
  classical
  refine ⟨(s.filter fun e => len e = a).card,
          (s.filter fun e => ¬ len e = a ∧ len e = b).card,
          (s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card, ?_, ?_⟩
  · have hsplit1 := Finset.sum_filter_add_sum_filter_not s (fun e => len e = a) len
    have hsplit2 := Finset.sum_filter_add_sum_filter_not
      (s.filter fun e => ¬ len e = a) (fun e => len e = b) len
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit2
    have hA : ∑ e ∈ s.filter (fun e => len e = a), len e
        = ((s.filter fun e => len e = a).card : ℝ) * a := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2),
        Finset.sum_const, nsmul_eq_mul]
    have hB : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ len e = b), len e
        = ((s.filter fun e => ¬ len e = a ∧ len e = b).card : ℝ) * b := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.mp he).2.2),
        Finset.sum_const, nsmul_eq_mul]
    have hC : ∑ e ∈ s.filter (fun e => ¬ len e = a ∧ ¬ len e = b), len e
        = ((s.filter fun e => ¬ len e = a ∧ ¬ len e = b).card : ℝ) * c := by
      rw [Finset.sum_congr rfl (fun e he => ?_), Finset.sum_const, nsmul_eq_mul]
      have hmem := Finset.mem_filter.mp he
      rcases h e hmem.1 with h' | h' | h'
      · exact absurd h' hmem.2.1
      · exact absurd h' hmem.2.2
      · exact h'
    rw [hA] at hsplit1
    rw [hB, hC] at hsplit2
    linarith [hsplit1, hsplit2]
  · have h1 := Finset.card_filter_add_card_filter_not
      (s := s) (p := fun e => len e = a)
    have h2 := Finset.card_filter_add_card_filter_not
      (s := s.filter fun e => ¬ len e = a) (p := fun e => len e = b)
    rw [Finset.filter_filter, Finset.filter_filter] at h2
    omega
theorem Dissection.side_walk_abc {N : ℕ} (D : Dissection N) (i : Fin 3) (a b c : ℝ)
    (habc : ∀ (j : Fin N) (k : Fin 3),
      dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = a
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = b
      ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = c) :
    ∃ P Q R : ℕ, (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c
      = dist (D.target.pts i) (D.target.pts (i + 1)) ∧ P + Q + R ≤ 3 * N := by
  classical
  obtain ⟨part, -, -, hsum⟩ := D.side_walk i
  obtain ⟨P, Q, R, hPQR, hcard⟩ := sum_three_values part
    (fun e => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1))) a b c
    (fun e _ => habc e.1 e.2)
  refine ⟨P, Q, R, by rw [hPQR, hsum], ?_⟩
  have hle : part.card ≤ Fintype.card (Fin N × Fin 3) := Finset.card_le_univ part
  simp only [Fintype.card_prod, Fintype.card_fin] at hle
  omega
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
theorem Tri.Congruent.dist_eq {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts (σ i)) (U.pts (σ j)) := by
  obtain ⟨f, σ, hf⟩ := h
  exact ⟨σ, fun i j => by rw [← hf i, ← hf j, f.dist_eq]⟩
theorem Tri.det_pos_or_neg (T : Tri) : 0 < T.det ∨ T.det < 0 :=
  (lt_or_gt_of_ne T.det_ne_zero).symm
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
theorem pb_apply_self (i j : Fin 2) : (pb i : Plane) j = if j = i then 1 else 0 := by
  rw [← pb_repr, Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]
theorem mem_stdCarrier_iff (x : Plane) :
    x ∈ stdCarrier ↔ 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1 := by
  constructor
  · intro hx
    have hlin0 : IsLinearMap ℝ (fun y : Plane => y 0) := ⟨fun a b => rfl, fun c a => rfl⟩
    have hlin1 : IsLinearMap ℝ (fun y : Plane => y 1) := ⟨fun a b => rfl, fun c a => rfl⟩
    have hlinsum : IsLinearMap ℝ (fun y : Plane => y 0 + y 1) :=
      ⟨fun a b => by show a 0 + b 0 + (a 1 + b 1) = a 0 + a 1 + (b 0 + b 1); ring,
       fun c a => by show c * a 0 + c * a 1 = c * (a 0 + a 1); ring⟩
    have hconv : Convex ℝ {y : Plane | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} := by
      have h0 : Convex ℝ {y : Plane | 0 ≤ y 0} := convex_halfSpace_ge hlin0 0
      have h1 : Convex ℝ {y : Plane | 0 ≤ y 1} := convex_halfSpace_ge hlin1 0
      have h2 : Convex ℝ {y : Plane | y 0 + y 1 ≤ 1} := convex_halfSpace_le hlinsum 1
      have := (h0.inter h1).inter h2
      convert this using 1
      ext y; simp [and_assoc]
    have hmem : (0:Plane) ∈ {y : Plane | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} ∧
        (pb 0 : Plane) ∈ {y : Plane | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} ∧
        (pb 1 : Plane) ∈ {y : Plane | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} := by
      refine ⟨?_, ?_, ?_⟩ <;> simp [pb_apply_self]
    have hsub : stdCarrier ⊆ {y : Plane | 0 ≤ y 0 ∧ 0 ≤ y 1 ∧ y 0 + y 1 ≤ 1} := by
      apply convexHull_min _ hconv
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact hmem.1
      · exact hmem.2.1
      · exact hmem.2.2
    exact hsub hx
  · rintro ⟨h0, h1, h2⟩
    refine mem_convexHull_of_exists_fintype (ι := Fin 3)
      ![1 - x 0 - x 1, x 0, x 1] ![(0:Plane), pb 0, pb 1]
      ?_ ?_ ?_ ?_
    · intro i; fin_cases i <;> simp_all <;> linarith
    · rw [Fin.sum_univ_three]
      show 1 - x 0 - x 1 + x 0 + x 1 = 1
      ring
    · intro i; fin_cases i <;> simp
    · rw [Fin.sum_univ_three]
      show (1 - x 0 - x 1) • (0:Plane) + x 0 • pb 0 + x 1 • pb 1 = x
      have hxrepr : x = x 0 • pb 0 + x 1 • pb 1 := by
        conv_lhs => rw [← pb.sum_repr x]
        rw [Fin.sum_univ_two]
        simp [pb_repr]
      conv_rhs => rw [hxrepr]
      module
theorem isCompact_stdCarrier : IsCompact stdCarrier :=
  (Set.finite_range _).isCompact_convexHull ℝ
end Erdos634.AreaDet
end

section
namespace Erdos634.CertCoord
open Erdos634.Geometry
noncomputable def mkPt (x y : ℝ) : Plane := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]
@[simp] theorem mkPt_zero (x y : ℝ) : mkPt x y 0 = x := by simp [mkPt, EuclideanSpace.equiv]
@[simp] theorem mkPt_one (x y : ℝ) : mkPt x y 1 = y := by simp [mkPt, EuclideanSpace.equiv]
def det3 (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) : ℝ := (x₁ - x₀) * (y₂ - y₀) - (x₂ - x₀) * (y₁ - y₀)
theorem not_collinear_of_det {x₀ y₀ x₁ y₁ x₂ y₂ : ℝ} (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) :
    ¬ Collinear ℝ ({mkPt x₀ y₀, mkPt x₁ y₁, mkPt x₂ y₂} : Set Plane) := by
  intro hc
  rw [collinear_iff_exists_forall_eq_smul_vadd] at hc
  obtain ⟨q, v, hv⟩ := hc
  obtain ⟨r₀, h₀⟩ := hv (mkPt x₀ y₀) (by simp)
  obtain ⟨r₁, h₁⟩ := hv (mkPt x₁ y₁) (by simp)
  obtain ⟨r₂, h₂⟩ := hv (mkPt x₂ y₂) (by simp)
  have hx : ∀ (a b : ℝ) (r : ℝ), mkPt a b = r • v +ᵥ q → a = r * v 0 + q 0 := by
    intro a b r h
    have := congrArg (fun pt : Plane => pt 0) h
    simpa [mkPt, EuclideanSpace.equiv] using this
  have hy : ∀ (a b : ℝ) (r : ℝ), mkPt a b = r • v +ᵥ q → b = r * v 1 + q 1 := by
    intro a b r h
    have := congrArg (fun pt : Plane => pt 1) h
    simpa [mkPt, EuclideanSpace.equiv] using this
  have e₀ := hx _ _ _ h₀; have f₀ := hy _ _ _ h₀
  have e₁ := hx _ _ _ h₁; have f₁ := hy _ _ _ h₁
  have e₂ := hx _ _ _ h₂; have f₂ := hy _ _ _ h₂
  apply hdet
  rw [det3, e₀, e₁, e₂, f₀, f₁, f₂]
  ring
noncomputable def mkTri (x₀ y₀ x₁ y₁ x₂ y₂ : ℝ) (hdet : det3 x₀ y₀ x₁ y₁ x₂ y₂ ≠ 0) : Tri where
  pts := ![mkPt x₀ y₀, mkPt x₁ y₁, mkPt x₂ y₂]
  indep := (affineIndependent_iff_not_collinear_of_ne
    (show (0 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide)).mpr (not_collinear_of_det hdet)
end Erdos634.CertCoord
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
end Erdos634.Geometry
end

section
namespace Erdos634.DissectionMap
open Erdos634.Geometry
noncomputable def mapTri (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) : Tri where
  pts := e ∘ T.pts
  indep := T.indep.map' e.toAffineMap e.injective
theorem mapTri_carrier (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    (mapTri e T).carrier = e '' T.carrier := by
  simp only [mapTri, Tri.carrier]
  rw [Set.range_comp]
  exact (AffineMap.image_convexHull (𝕜 := ℝ) e.toAffineMap (Set.range T.pts)).symm
noncomputable def mapDissection {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (D : Dissection N) :
    Dissection N where
  target := mapTri e D.target
  tile := fun i => mapTri e (D.tile i)
  covers := by
    simp only [mapTri_carrier]
    rw [← Set.image_iUnion, D.covers]
  interiors_disjoint := by
    intro i j hij
    have h := D.interiors_disjoint hij
    have hcont : Continuous e := AffineEquiv.continuous_of_finiteDimensional e
    have hcont' : Continuous e.symm := AffineEquiv.continuous_of_finiteDimensional e.symm
    let eh : Plane ≃ₜ Plane := ⟨e.toEquiv, hcont, hcont'⟩
    have himg : ∀ S : Set Plane, interior (e '' S) = e '' interior S := by
      intro S
      exact (eh.image_interior S).symm
    simp only [mapTri_carrier, himg]
    exact (Set.disjoint_image_iff e.injective).mpr h
theorem mapDissection_target {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (D : Dissection N) :
    (mapDissection e D).target = mapTri e D.target := rfl
theorem mapDissection_tile {N : ℕ} (e : Plane ≃ᵃ[ℝ] Plane) (D : Dissection N) (i : Fin N) :
    (mapDissection e D).tile i = mapTri e (D.tile i) := rfl
end Erdos634.DissectionMap
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
open Erdos634.Geometry Erdos634.CertCoord Erdos634.DissectionMap Erdos634.AreaDet
theorem edgeMap_mapTri (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    edgeMap (mapTri e T) = (e.linear : Plane →ₗ[ℝ] Plane).comp (edgeMap T) := by
  apply pb.ext
  intro i
  rw [LinearMap.comp_apply, edgeMap_basis, edgeMap_basis]
  show e (T.pts i.succ) - e (T.pts 0) = e.linear (T.pts i.succ - T.pts 0)
  rw [← vsub_eq_sub, ← vsub_eq_sub]
  exact (AffineMap.linearMap_vsub e.toAffineMap _ _).symm
theorem detTri_mapTri (e : Plane ≃ᵃ[ℝ] Plane) (T : Tri) :
    detTri (mapTri e T) = LinearMap.det (e.linear : Plane →ₗ[ℝ] Plane) * detTri T := by
  rw [detTri, edgeMap_mapTri, LinearMap.det_comp, detTri]
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
namespace Erdos634.VertexFigureReal
open Erdos634.Geometry Finset
theorem interior_localAngle_mem {N : ℕ} (D : Dissection N) (α β γ : ℝ)
    (hcorners : ∀ (i : Fin N) (j : Fin 3),
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        ∈ ({α, β, γ} : Finset ℝ))
    (v : Plane) (i : Fin N) :
    (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ) := by
  classical
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with ⟨j, _, hval⟩ | h2 | hpi | h0
  · have := hcorners i j
    rw [hval]
    simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
    tauto
  · simp [h2]
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
end Erdos634.MarchFlank
end

section
open Erdos634.Geometry
namespace Erdos634.Geometry
theorem Tri.Congruent.cornerAngle_perm {T U : Tri} (h : T.Congruent U) :
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
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry.A1Pos
open Set
theorem not_subsingleton_of_mem_Ioo {a b c d y : ℝ} (hcd : c < d) (hy : y ∈ Ioo a b)
    (hy2 : y ∈ Icc c d) (hsub : (Icc a b ∩ Icc c d).Subsingleton) : False := by
  have hyin : y ∈ Icc a b ∩ Icc c d := ⟨Ioo_subset_Icc_self hy, hy2⟩
  rcases lt_or_eq_of_le hy2.2 with hyd | hyd
  · have hmin : y < min b d := lt_min hy.2 hyd
    have hz : (y + min b d) / 2 ∈ Icc a b ∩ Icc c d := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · linarith [hy.1]
      · linarith [min_le_left b d]
      · linarith [hy2.1]
      · linarith [min_le_right b d]
    have := hsub hz hyin
    linarith
  · have hcy : c < y := hyd ▸ hcd
    have hmax : max a c < y := max_lt hy.1 hcy
    have hz : (max a c + y) / 2 ∈ Icc a b ∩ Icc c d := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · linarith [le_max_left a c]
      · linarith [hy.2]
      · linarith [le_max_right a c]
      · linarith [hy2.2]
    have := hsub hz hyin
    linarith
theorem endpoint_of_subsingleton {a b c d y : ℝ} (hab : a < b) (hcd : c < d)
    (hsub : (Icc a b ∩ Icc c d).Subsingleton) (h1 : y ∈ Icc a b) (h2 : y ∈ Icc c d) :
    (y = a ∨ y = b) ∧ (y = c ∨ y = d) := by
  constructor
  · by_contra h
    push Not at h
    exact not_subsingleton_of_mem_Ioo hcd
      ⟨lt_of_le_of_ne h1.1 (Ne.symm h.1), lt_of_le_of_ne h1.2 h.2⟩ h2 hsub
  · by_contra h
    push Not at h
    rw [inter_comm] at hsub
    exact not_subsingleton_of_mem_Ioo hab
      ⟨lt_of_le_of_ne h2.1 (Ne.symm h.1), lt_of_le_of_ne h2.2 h.2⟩ h1 hsub
variable {ι Q : Type*}
def chainUnion (S : Finset ι) (a b : ι → ℝ) : Set ℝ := ⋃ e ∈ S, Icc (a e) (b e)
theorem isClosed_chainUnion (S : Finset ι) (a b : ι → ℝ) : IsClosed (chainUnion S a b) :=
  S.finite_toSet.isClosed_biUnion fun _ _ => isClosed_Icc
theorem isCompact_chainUnion (S : Finset ι) (a b : ι → ℝ) : IsCompact (chainUnion S a b) :=
  S.finite_toSet.isCompact_biUnion fun _ _ => isCompact_Icc
structure IsChain (S : Finset ι) (a b : ι → ℝ) (φ : ℝ → Q) : Prop where
  lt : ∀ e ∈ S, a e < b e
  disj : ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → (Icc (a e) (b e) ∩ Icc (a e') (b e')).Subsingleton
  cls : ∀ e ∈ S, φ (a e) = φ (b e)
theorem anchor {S : Finset ι} {a b : ι → ℝ} {φ : ℝ → Q} (hS : IsChain S a b φ) {t₀ : ℝ}
    (ht₀ : t₀ ∈ chainUnion S a b) :
    ∃ p ≤ t₀, Icc p t₀ ⊆ chainUnion S a b ∧
      (∀ p', p' ≤ t₀ → Icc p' t₀ ⊆ chainUnion S a b → p ≤ p') ∧
      ∀ e ∈ S, t₀ ∈ Icc (a e) (b e) → φ (a e) = φ p := by
  classical
  set U := chainUnion S a b with hU
  set C := connectedComponentIn U t₀ with hC
  have hUc : IsClosed U := isClosed_chainUnion S a b
  have hCpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have ht₀C : t₀ ∈ C := mem_connectedComponentIn ht₀
  have hCU : C ⊆ U := connectedComponentIn_subset U t₀
  have hCclosed : IsClosed C := by
    have hcl : closure C ⊆ C :=
      hCpre.closure.subset_connectedComponentIn (subset_closure ht₀C)
        (closure_minimal hCU hUc)
    exact closure_subset_iff_isClosed.mp hcl
  have hCbdd : BddBelow C := ((isCompact_chainUnion S a b).bddBelow).mono hCU
  have hCne : C.Nonempty := ⟨t₀, ht₀C⟩
  set p := sInf C with hp
  have hpC : p ∈ C := hCclosed.csInf_mem hCne hCbdd
  have hpt : p ≤ t₀ := csInf_le hCbdd ht₀C
  have hsubC : ∀ s : Set ℝ, IsPreconnected s → s ⊆ U → ∀ y ∈ s, y ∈ C → s ⊆ C := by
    intro s hs hsU y hys hyC
    have := hs.subset_connectedComponentIn hys hsU
    rwa [← connectedComponentIn_eq hyC] at this
  have hIcc : Icc p t₀ ⊆ C := hCpre.Icc_subset hpC ht₀C
  refine ⟨p, hpt, hIcc.trans hCU, ?_, ?_⟩
  · intro p' hp' hsub
    have : Icc p' t₀ ⊆ C :=
      hsubC _ isPreconnected_Icc hsub t₀ ⟨hp', le_rfl⟩ ht₀C
    exact csInf_le hCbdd (this ⟨le_rfl, hp'⟩)
  obtain ⟨e₀, he₀S, hpe₀⟩ : ∃ e ∈ S, p ∈ Icc (a e) (b e) := by
    have := hCU hpC
    simp only [hU, chainUnion, mem_iUnion] at this
    obtain ⟨e, he, hpe⟩ := this
    exact ⟨e, he, hpe⟩
  have hae₀ : a e₀ = p := by
    have hsub : Icc (a e₀) (b e₀) ⊆ C := by
      refine hsubC _ isPreconnected_Icc ?_ p hpe₀ hpC
      intro z hz
      simp only [hU, chainUnion, mem_iUnion]
      exact ⟨e₀, he₀S, hz⟩
    have h1 : p ≤ a e₀ := csInf_le hCbdd (hsub ⟨le_rfl, (hS.lt e₀ he₀S).le⟩)
    exact le_antisymm hpe₀.1 h1
  intro e heS he₀
  by_contra hbad
  let G : Set ℝ := ⋃ e' ∈ S.filter (fun e' => φ (a e') = φ p), Icc (a e') (b e')
  let B : Set ℝ := ⋃ e' ∈ S.filter (fun e' => φ (a e') ≠ φ p), Icc (a e') (b e')
  have hGc : IsClosed G := (Finset.finite_toSet _).isClosed_biUnion fun _ _ => isClosed_Icc
  have hBc : IsClosed B := (Finset.finite_toSet _).isClosed_biUnion fun _ _ => isClosed_Icc
  have hcov : C ⊆ G ∪ B := by
    intro z hz
    have := hCU hz
    simp only [hU, chainUnion, mem_iUnion] at this
    obtain ⟨e', he', hz'⟩ := this
    by_cases hg : φ (a e') = φ p
    · left
      exact mem_biUnion (Finset.mem_filter.mpr ⟨he', hg⟩) hz'
    · right
      exact mem_biUnion (Finset.mem_filter.mpr ⟨he', hg⟩) hz'
  have hG : (C ∩ G).Nonempty :=
    ⟨p, hpC, mem_biUnion (Finset.mem_filter.mpr ⟨he₀S, by rw [hae₀]⟩) hpe₀⟩
  have hB : (C ∩ B).Nonempty :=
    ⟨t₀, ht₀C, mem_biUnion (Finset.mem_filter.mpr ⟨heS, hbad⟩) he₀⟩
  obtain ⟨y, -, hyG, hyB⟩ := isPreconnected_closed_iff.mp hCpre G B hGc hBc hcov hG hB
  obtain ⟨e₁, he₁, hy₁⟩ := mem_iUnion₂.mp hyG
  obtain ⟨e₂, he₂, hy₂⟩ := mem_iUnion₂.mp hyB
  rw [Finset.mem_filter] at he₁ he₂
  have hne : e₁ ≠ e₂ := by
    rintro rfl
    exact he₂.2 he₁.2
  obtain ⟨hy1, hy2⟩ := endpoint_of_subsingleton (hS.lt e₁ he₁.1) (hS.lt e₂ he₂.1)
    (hS.disj e₁ he₁.1 e₂ he₂.1 hne) hy₁ hy₂
  have hφ1 : φ y = φ (a e₁) := by
    rcases hy1 with h | h
    · rw [h]
    · rw [h, hS.cls e₁ he₁.1]
  have hφ2 : φ y = φ (a e₂) := by
    rcases hy2 with h | h
    · rw [h]
    · rw [h, hS.cls e₂ he₂.1]
  exact he₂.2 (hφ2.symm.trans (hφ1.trans he₁.2))
theorem class_eq {S T : Finset ι} {a b : ι → ℝ} {φ : ℝ → Q} (hS : IsChain S a b φ)
    (hT : IsChain T a b φ) {t₀ : ℝ}
    (htr₁ : ∀ p < t₀, Icc p t₀ ⊆ chainUnion S a b → Icc p t₀ ⊆ chainUnion T a b)
    (htr₂ : ∀ p < t₀, Icc p t₀ ⊆ chainUnion T a b → Icc p t₀ ⊆ chainUnion S a b)
    {e e' : ι} (he : e ∈ S ∨ e ∈ T) (he' : e' ∈ S ∨ e' ∈ T)
    (h0 : t₀ ∈ Icc (a e) (b e)) (h0' : t₀ ∈ Icc (a e') (b e')) :
    φ (a e) = φ (a e') := by
  have memU : ∀ {R : Finset ι} {g : ι}, g ∈ R → t₀ ∈ Icc (a g) (b g) → t₀ ∈ chainUnion R a b :=
    fun hg h => mem_biUnion hg h
  have key : t₀ ∈ chainUnion S a b → t₀ ∈ chainUnion T a b →
      ∃ p, (∀ g ∈ S, t₀ ∈ Icc (a g) (b g) → φ (a g) = φ p) ∧
        (∀ g ∈ T, t₀ ∈ Icc (a g) (b g) → φ (a g) = φ p) := by
    intro hs ht
    obtain ⟨p, hp, hpU, hpmin, hpcls⟩ := anchor hS hs
    obtain ⟨q, hq, hqU, hqmin, hqcls⟩ := anchor hT ht
    have hqp : q ≤ p := by
      rcases lt_or_eq_of_le hp with h | h
      · exact hqmin p hp (htr₁ p h hpU)
      · rw [h]; exact hq
    have hpq : p ≤ q := by
      rcases lt_or_eq_of_le hq with h | h
      · exact hpmin q hq (htr₂ q h hqU)
      · rw [h]; exact hp
    have heq : p = q := le_antisymm hpq hqp
    exact ⟨p, hpcls, fun g hg h => by rw [hqcls g hg h, heq]⟩
  rcases he with he | he <;> rcases he' with he' | he'
  · obtain ⟨p, -, -, -, hcls⟩ := anchor hS (memU he h0)
    rw [hcls e he h0, hcls e' he' h0']
  · obtain ⟨p, h1, h2⟩ := key (memU he h0) (memU he' h0')
    rw [h1 e he h0, h2 e' he' h0']
  · obtain ⟨p, h1, h2⟩ := key (memU he' h0') (memU he h0)
    rw [h2 e he h0, h1 e' he' h0']
  · obtain ⟨p, -, -, -, hcls⟩ := anchor hT (memU he h0)
    rw [hcls e he h0, hcls e' he' h0']
end Erdos634.Geometry.A1Pos
end

section
namespace Erdos634.Geometry.CaseA.LemmaV
open Complex NumberField
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * I / (4 * n : ℕ))
theorem zeta_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (zeta n) (4 * n) :=
  Complex.isPrimitiveRoot_exp (4 * n) (by omega)
theorem zeta_pow (n k : ℕ) : zeta n ^ k = Complex.exp (k * (2 * Real.pi * I / (4 * n : ℕ))) := by
  rw [zeta, ← Complex.exp_nat_mul]
theorem zeta_pow_n {n : ℕ} (hn : 0 < n) : zeta n ^ n = I := by
  rw [zeta_pow]
  have : (n : ℂ) * (2 * Real.pi * I / (4 * n : ℕ)) = (Real.pi / 2 : ℝ) * I := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast; field_simp; ring
  rw [this, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp
theorem zeta_pow_two_mul {n : ℕ} (hn : 0 < n) (j : ℕ) :
    zeta n ^ (2 * j) = Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) := by
  rw [zeta_pow]; congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast; field_simp; ring
theorem two_sin_eq {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : 2 * j ≤ 4 * n) :
    ((2 * Real.sin ((j : ℝ) * Real.pi / n) : ℝ) : ℂ)
      = zeta n ^ (3 * n) * zeta n ^ (4 * n - 2 * j) * (zeta n ^ (4 * j) - 1) := by
  set θ : ℝ := (j : ℝ) * Real.pi / n
  have hE := zeta_pow_two_mul hn j
  have h1 : zeta n ^ (4 * n - 2 * j) * zeta n ^ (2 * j) = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hj]; exact (zeta_prim hn).pow_eq_one
  have hinv : zeta n ^ (4 * n - 2 * j) = Complex.exp (-(θ : ℂ) * I) := by
    have h2 : Complex.exp (-(θ : ℂ) * I) * Complex.exp ((θ : ℂ) * I) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [hE] at h1
    exact mul_right_cancel₀ (Complex.exp_ne_zero _) (h1.trans h2.symm)
  have h3n : zeta n ^ (3 * n) = -I := by
    rw [mul_comm, pow_mul, zeta_pow_n hn]; simp [pow_three, Complex.I_mul_I]
  have h4j : zeta n ^ (4 * j) = Complex.exp ((θ : ℂ) * I) ^ 2 := by
    rw [← hE, ← pow_mul]; ring_nf
  rw [h3n, hinv, h4j]
  push_cast
  rw [Complex.sin]
  have h2 : Complex.exp (-(θ : ℂ) * I) * Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  linear_combination (I * Complex.exp ((θ : ℂ) * I)) * h2
section Field
variable {n : ℕ} [NeZero n]
noncomputable abbrev Kf (n : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {zeta n}
end Field
end Erdos634.Geometry.CaseA.LemmaV
end

section
open scoped Classical
namespace Erdos634.Geometry
open MeasureTheory Set
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
namespace Dissection
noncomputable def eDir (D : Dissection N) (e : Fin N × Fin 3) : Dir := (D.tile e.1).leftUnit e.2
def eSet (D : Dissection N) (e : Fin N × Fin 3) : Set Plane := (D.tile e.1).edge e.2
end Dissection
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
open scoped Classical
namespace Erdos634.Geometry.Row3.RP
open Real Erdos634.Geometry Erdos634.Geometry.Row3
theorem oppLen_pos (T : Tri) (k : Fin 3) : 0 < T.oppLen k := by
  unfold Tri.oppLen
  apply dist_pos.mpr
  intro h
  have := T.indep.injective h
  revert this; fin_cases k <;> decide
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
theorem edge_length_trichotomy (D : CongruentDissection N) (j : Fin N) (k : Fin 3) :
    dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = sideLen D 0
    ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = sideLen D 1
    ∨ dist ((D.tile j).pts k) ((D.tile j).pts (k + 1)) = sideLen D 2 := by
  obtain ⟨i, hi⟩ := chain_edge_length_mem_model D (j, k)
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)
theorem side_walk_congruent (D : CongruentDissection N) (i : Fin 3) :
    ∃ P Q R : ℕ,
      (P : ℝ) * sideLen D 0 + (Q : ℝ) * sideLen D 1 + (R : ℝ) * sideLen D 2
        = dist (D.target.pts i) (D.target.pts (i + 1)) ∧ P + Q + R ≤ 3 * N :=
  D.toDissection.side_walk_abc i _ _ _ (edge_length_trichotomy D)
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
theorem CongruentDissection.oppLen_word (D : CongruentDissection N) (j : Fin 3) :
    ∃ n : Fin 3 → ℕ, D.target.oppLen j = ∑ k, (n k : ℝ) * D.model.oppLen k := by
  obtain ⟨P, Q, R, h, -⟩ := Erdos634.EdgeWordConversion.side_walk_congruent D (j + 1)
  rw [D.sideLen_eq_oppLen, D.sideLen_eq_oppLen, D.sideLen_eq_oppLen] at h
  refine ⟨![Q, R, P], ?_⟩
  have hj : D.target.oppLen j = dist (D.target.pts (j + 1)) (D.target.pts (j + 1 + 1)) := by
    unfold Tri.oppLen
    rw [show j + 1 + 1 = j + 2 by fin_cases j <;> rfl]
  rw [hj, ← h, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [show (0 : Fin 3) + 2 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 2 = 1 from rfl]
  ring
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
namespace Erdos634.Geometry.CaseA.LemmaV
open Erdos634.Geometry
theorem angle_pos (T : Tri) (k : Fin 3) : 0 < T.angleAt k := Erdos634.MarchFlank.cornerAngle_pos T k
theorem angle_lt_pi (T : Tri) (k : Fin 3) : T.angleAt k < Real.pi :=
  Erdos634.RouteOneVertexKill.cornerAngle_lt_pi T k
theorem law_sines (T : Tri) (j : Fin 3) :
    Real.sin (T.angleAt (j + 1)) * T.oppLen j = Real.sin (T.angleAt j) * T.oppLen (j + 1) :=
  Erdos634.TriLawSin.sin_angleAt_mul_sideOpp T j
theorem nat_bounds {n : ℕ} (hn : 0 < n) {u : ℕ} {x : ℝ} (hx : x = u * Real.pi / n) (h0 : 0 < x)
    (hπ : x < Real.pi) : 0 < u ∧ u < n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp := Real.pi_pos
  rw [hx] at h0 hπ
  constructor
  · have : (0 : ℝ) < u := by
      by_contra hc; push Not at hc
      have : (u : ℝ) * Real.pi / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hc hp.le) hn'.le
      linarith
    exact_mod_cast this
  · rw [div_lt_iff₀ hn'] at hπ
    have : (u : ℝ) < n := by nlinarith
    exact_mod_cast this
theorem target_angle_nat {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (k : Fin 3) :
    ∃ u : ℕ, D.target.angleAt k = u * Real.pi / n := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcorners : ∀ (i : Fin N) (j : Fin 3),
      cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
        ∈ ({D.model.angleAt 0, D.model.angleAt 1, D.model.angleAt 2} : Finset ℝ) := by
    intro i j
    obtain ⟨k', hk'⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
    rw [hk']
    show D.model.angleAt k' ∈ _
    fin_cases k' <;> simp
  have hval : ∀ i, ∃ u : ℕ, (D.tile i).localAngle (D.target.pts k) = u * Real.pi / n := by
    intro i
    have hm := Erdos634.VertexFigureReal.interior_localAngle_mem D.toDissection _ _ _ hcorners
      (D.target.pts k) i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h | h | h <;> rw [h]
    · exact ⟨a 0, ha 0⟩
    · exact ⟨a 1, ha 1⟩
    · exact ⟨a 2, ha 2⟩
    · exact ⟨n, by field_simp⟩
    · exact ⟨2 * n, by push_cast; field_simp⟩
    · exact ⟨0, by simp⟩
  choose u hu using hval
  refine ⟨∑ i, u i, ?_⟩
  have hs := D.toDissection.sum_localAngle_eq (D.target.pts k)
  rw [D.target.localAngle_vertex k] at hs
  show cornerAngle _ _ _ = _
  rw [← hs, Finset.sum_congr rfl (fun i _ => hu i)]
  push_cast
  rw [Finset.sum_mul, Finset.sum_div]
theorem star {N : ℕ} (D : CongruentDissection N) :
    ∃ c : Fin 3 → ℕ,
      (N : ℝ) * Real.sin (D.model.angleAt 0) * Real.sin (D.model.angleAt 1) *
        Real.sin (D.model.angleAt 2) * Real.sin (D.target.angleAt 0)
      = (∑ k, (c k : ℝ) * Real.sin (D.model.angleAt k)) ^ 2 *
        Real.sin (D.target.angleAt 1) * Real.sin (D.target.angleAt 2) := by
  obtain ⟨c, hc⟩ := D.oppLen_word 0
  refine ⟨c, ?_⟩
  set M := D.model; set T := D.target
  have sp : ∀ (U : Tri) k, 0 < Real.sin (U.angleAt k) := fun U k =>
    Real.sin_pos_of_pos_of_lt_pi (angle_pos U k) (angle_lt_pi U k)
  have hM0 := law_sines M 0; have hM1 := law_sines M 1
  have hT0 := law_sines T 0; have hT1 := law_sines T 1
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl] at hM0 hM1 hT0 hT1
  have harea := Row3.RP.abs_det_target D
  rw [Row3.RP.abs_det_eq, Row3.RP.abs_det_eq] at harea
  rw [Fin.sum_univ_three] at hc ⊢
  set a0 := Real.sin (M.angleAt 0); set a1 := Real.sin (M.angleAt 1)
  set a2 := Real.sin (M.angleAt 2)
  set b0 := Real.sin (T.angleAt 0); set b1 := Real.sin (T.angleAt 1)
  set b2 := Real.sin (T.angleAt 2)
  have ha1 : 0 < a1 := sp M 1
  have hb0 : 0 < b0 := sp T 0; have hb1 : 0 < b1 := sp T 1
  set m0 := M.oppLen 0; set m1 := M.oppLen 1; set m2 := M.oppLen 2
  set t0 := T.oppLen 0; set t1 := T.oppLen 1; set t2 := T.oppLen 2
  set X := (c 0 : ℝ) * a0 + c 1 * a1 + c 2 * a2 with hX
  have hm0 : 0 < m0 := Row3.RP.oppLen_pos M 0
  have f1 : a2 * m0 = a0 * m2 := by
    apply mul_left_cancel₀ ha1.ne'
    linear_combination a2 * hM0 + a0 * hM1
  have g2 : b2 * t0 = b0 * t2 := by
    apply mul_left_cancel₀ hb1.ne'
    linear_combination b2 * hT0 + b0 * hT1
  have f2 : m0 * X = a0 * t0 := by
    rw [hX, hc]; linear_combination (c 1 : ℝ) * hM0 + (c 2 : ℝ) * f1
  have key : (m0 ^ 2 * b0) * ((N : ℝ) * a0 * a1 * a2 * b0 - X ^ 2 * b1 * b2) = 0 := by
    linear_combination (-(X * m0 + a0 * t0) * b1 * b2 * b0) * f2
      - (a0 ^ 2 * b0 * b2 * t0) * hT0 - (a0 ^ 2 * b0 * b0 * t1) * g2
      - (a0 ^ 2 * b0 ^ 2) * harea + ((N : ℝ) * a0 * b0 ^ 2 * a0 * m2) * hM0
      + ((N : ℝ) * a0 * b0 ^ 2 * a1 * m0) * f1
  have := (mul_eq_zero.mp key).resolve_left (by positivity)
  linarith
end Erdos634.Geometry.CaseA.LemmaV
end

section
open scoped Classical
namespace Erdos634.Geometry
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry.A1Dir
open Erdos634.Geometry Set
noncomputable def H (n : ℕ) : AddSubgroup Real.Angle :=
  AddSubgroup.zmultiples (((Real.pi / n : ℝ)) : Real.Angle)
theorem natmul_mem (n a : ℕ) : ((a * Real.pi / n : ℝ) : Real.Angle) ∈ H n := by
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨(a : ℤ), ?_⟩
  rw [← Real.Angle.coe_zsmul, zsmul_eq_mul]
  congr 1
  push_cast
  ring
theorem pi_mem {n : ℕ} (hn : 0 < n) : ((Real.pi : ℝ) : Real.Angle) ∈ H n := by
  have h := natmul_mem n n
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rwa [show (n : ℝ) * Real.pi / n = Real.pi by field_simp] at h
theorem turn_mem {n : ℕ} (hn : 0 < n) (T : Tri)
    (hT : ∀ k, ∃ a : ℕ, T.angleAt k = a * Real.pi / n) (k : Fin 3) :
    (T.leftUnit (k + 1)).angle - (T.leftUnit k).angle ∈ H n := by
  obtain ⟨a, ha⟩ := hT (k + 1)
  have hmem : ((Real.pi - T.angleAt (k + 1) : ℝ) : Real.Angle) ∈ H n := by
    rw [Real.Angle.coe_sub, ha]
    exact sub_mem (pi_mem hn) (natmul_mem n a)
  rcases T.det_pos_or_neg with h | h
  · rw [T.leftUnit_turn_of_pos h k]
    simpa using hmem
  · rw [T.leftUnit_turn_of_neg h k]
    simpa using neg_mem hmem
theorem tile_local {n : ℕ} (hn : 0 < n) (T : Tri)
    (hT : ∀ k, ∃ a : ℕ, T.angleAt k = a * Real.pi / n) (k : Fin 3) :
    (T.leftUnit k).angle - (T.leftUnit 0).angle ∈ H n := by
  have h01 : (T.leftUnit 1).angle - (T.leftUnit 0).angle ∈ H n := turn_mem hn T hT 0
  have h12 : (T.leftUnit 2).angle - (T.leftUnit 1).angle ∈ H n := turn_mem hn T hT 1
  have hk : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  rcases hk k with rfl | rfl | rfl
  · simp
  · exact h01
  · have := add_mem h12 h01
    rwa [sub_add_sub_cancel] at this
theorem pt_cases (T : Tri) {x : Plane} (hx : x ∈ T.carrier) (hv : ∀ m, x ≠ T.pts m) :
    (∀ i, 0 < T.basis.coord i x) ∨
      ∃ m, T.basis.coord m x = 0 ∧ ∀ j, j ≠ m → 0 < T.basis.coord j x := by
  rw [T.carrier_eq_nonneg_coord] at hx
  by_cases h : ∃ m, T.basis.coord m x = 0
  · obtain ⟨m, hm⟩ := h
    refine Or.inr ⟨m, hm, fun j hj => lt_of_le_of_ne (hx j) (fun h0 => ?_)⟩
    obtain ⟨p, hp⟩ := T.eq_vertex_of_two_coords_zero hj h0.symm hm
    exact hv p hp
  · push Not at h
    exact Or.inl fun i => lt_of_le_of_ne (hx i) (Ne.symm (h i))
theorem mem_interior_of_pos (T : Tri) {x : Plane} (hpos : ∀ i, 0 < T.basis.coord i x) :
    x ∈ interior T.carrier := by
  obtain ⟨r, hr, hsub⟩ := T.ball_subset_of_pos hpos
  exact mem_interior.mpr ⟨_, hsub, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
theorem interior_meets {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ interior (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) : False := by
  have hcl : (D.tile j).carrier ⊆ closure (interior (D.tile j).carrier) := by
    rw [(D.tile j).convex.closure_interior_eq_closure_of_nonempty_interior
      (D.tile j).interior_nonempty]
    exact subset_closure
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp (hcl hxj) _ isOpen_interior hxi
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hy1 hy2
theorem shared_point {N : ℕ} (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) (hxv : x ∉ D.vertexSet) :
    ∃ k k', (D.tile j).leftUnit k' = Dir.neg ((D.tile i).leftUnit k) := by
  have hnv := D.notMem_vertexSet hxv
  rcases pt_cases _ hxi (hnv i) with hp | ⟨m, hm, ho⟩
  · exact (interior_meets D hij (mem_interior_of_pos _ hp) hxj).elim
  rcases pt_cases _ hxj (hnv j) with hp' | ⟨m', hm', ho'⟩
  · exact (interior_meets D hij.symm (mem_interior_of_pos _ hp') hxi).elim
  exact ⟨m + 1, m' + 1, D.leftUnit_neg hij hm ho hm' ho'⟩
theorem boundary_point {N : ℕ} (D : Dissection N) {i : Fin N} {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxv : x ∉ D.vertexSet)
    (hxint : x ∉ interior D.target.carrier) :
    ∃ k j, (D.tile i).leftUnit k = D.target.leftUnit j := by
  have hnv := D.notMem_vertexSet hxv
  rcases pt_cases _ hxi (hnv i) with hp | ⟨m, hm, ho⟩
  · exact absurd (interior_mono (tile_subset_target D i) (mem_interior_of_pos _ hp)) hxint
  have hxe : x ∈ D.eSet (i, m + 1) := (D.tile i).mem_edge_of_coord_zero hm ho
  rcases D.edge_interior_or_side (i, m + 1) hxe (hnv i _) (hnv i _) with h | ⟨j, hj⟩
  · exact absurd h hxint
  · have h2 := D.eDir_of_side hj
    unfold Dissection.eDir at h2
    exact ⟨_, _, h2⟩
theorem tile_angles {N : ℕ} (D : CongruentDissection N) {n : ℕ} (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) (k : Fin 3) :
    ∃ b : ℕ, (D.tile i).angleAt k = b * Real.pi / n := by
  obtain ⟨k', hk'⟩ := congruent_corner_angles (D.tiles_congruent i).symm k
  refine ⟨a k', ?_⟩
  have h := ha k'
  unfold Tri.angleAt at h ⊢
  rw [hk']
  exact h
theorem edge_iff {n : ℕ} (hn : 0 < n) (T : Tri)
    (hT : ∀ k, ∃ a : ℕ, T.angleAt k = a * Real.pi / n) (θ : Real.Angle) (k : Fin 3) :
    (T.leftUnit k).angle - θ ∈ H n ↔ (T.leftUnit 0).angle - θ ∈ H n := by
  have hl := tile_local hn T hT k
  constructor
  · intro h
    have := sub_mem h hl
    rwa [sub_sub_sub_cancel_left] at this
  · intro h
    have := add_mem hl h
    rwa [sub_add_sub_cancel] at this
theorem one_lt_rank : 1 < Module.rank ℝ Plane := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
  norm_num
theorem tile_dir_coset {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n)
    (a : Fin 3 → ℕ) (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) :
    ((D.tile i).leftUnit 0).angle - (D.target.leftUnit 0).angle ∈ H n := by
  set θ₀ := (D.target.leftUnit 0).angle with hθ₀
  have htile := tile_angles D a ha
  have htgt : ∀ j, (D.target.leftUnit j).angle - θ₀ ∈ H n :=
    tile_local hn D.target (CaseA.LemmaV.target_angle_nat D hn a ha)
  let good : Fin N → Prop := fun i => ((D.tile i).leftUnit 0).angle - θ₀ ∈ H n
  have hedge : ∀ i k, ((D.tile i).leftUnit k).angle - θ₀ ∈ H n ↔ good i :=
    fun i k => edge_iff hn (D.tile i) (htile i) θ₀ k
  by_contra hbad0
  let U : Set Plane := ⋃ i ∈ {i | ¬ good i}, (D.tile i).carrier
  let W : Set Plane := (⋃ i ∈ {i | good i}, (D.tile i).carrier) ∪ (interior D.target.carrier)ᶜ
  have hUc : IsClosed U :=
    (Set.toFinite _).isClosed_biUnion fun i _ => (D.tile i).isCompact.isClosed
  have hWc : IsClosed W :=
    ((Set.toFinite _).isClosed_biUnion fun i _ => (D.tile i).isCompact.isClosed).union
      isOpen_interior.isClosed_compl
  have hcov : (D.vertexSet)ᶜ ⊆ U ∪ W := by
    intro x _
    by_cases hx : x ∈ interior D.target.carrier
    · have hx' : x ∈ ⋃ i, (D.tile i).carrier := by
        rw [D.covers]; exact interior_subset hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx'
      by_cases hg : good j
      · exact Or.inr (Or.inl (Set.mem_biUnion (x := j) hg hj))
      · exact Or.inl (Set.mem_biUnion (x := j) hg hj)
    · exact Or.inr (Or.inr hx)
  have hconn : IsPreconnected (D.vertexSet)ᶜ :=
    (D.vertexSet_finite.countable.isConnected_compl_of_one_lt_rank one_lt_rank).isPreconnected
  have hUne : ((D.vertexSet)ᶜ ∩ U).Nonempty := by
    have hns : ¬ (D.tile i).carrier ⊆ D.vertexSet := fun h =>
      (D.tile i).volume_pos.ne'
        (MeasureTheory.measure_mono_null h (D.vertexSet_finite.countable.measure_zero _))
    obtain ⟨x, hx, hxv⟩ := Set.not_subset.mp hns
    exact ⟨x, hxv, Set.mem_biUnion (x := i) hbad0 hx⟩
  have hWne : ((D.vertexSet)ᶜ ∩ W).Nonempty := by
    have hK : IsCompact (D.target.carrier ∪ D.vertexSet) :=
      D.target.isCompact.union D.vertexSet_finite.isCompact
    obtain ⟨x, hx⟩ : (D.target.carrier ∪ D.vertexSet)ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      intro h
      rw [h] at hK
      exact noncompact_univ Plane hK
    exact ⟨x, fun h => hx (Or.inr h), Or.inr fun hi => hx (Or.inl (interior_subset hi))⟩
  obtain ⟨x, hxv, hxU, hxW⟩ := isPreconnected_closed_iff.mp hconn U W hUc hWc hcov hUne hWne
  obtain ⟨i', hi', hxi⟩ := Set.mem_iUnion₂.mp hxU
  rcases hxW with hA | hB
  · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hA
    have hij : i' ≠ j := fun h => hi' (h ▸ hj)
    obtain ⟨k, k', hkk⟩ := shared_point D.toDissection hij hxi hxj hxv
    have h1 := (hedge j k').mpr hj
    rw [hkk, Dir.angle_neg] at h1
    apply hi'
    rw [← hedge i' k]
    have := sub_mem h1 (pi_mem hn)
    convert this using 1
    abel
  · obtain ⟨k, j, hkj⟩ := boundary_point D.toDissection hxi hxv hB
    apply hi'
    rw [← hedge i' k, hkj]
    exact htgt j
theorem edge_dir_coset {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n)
    (a : Fin 3 → ℕ) (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) (k : Fin 3) :
    ((D.tile i).leftUnit k).angle - (D.target.leftUnit 0).angle ∈ H n :=
  (edge_iff hn (D.tile i) (tile_angles D a ha i) _ k).mpr (tile_dir_coset D hn a ha i)
end Erdos634.Geometry.A1Dir
end

section
open scoped Classical
namespace Erdos634.Geometry.A1Pos
open Erdos634.Geometry Set
variable {N : ℕ}
noncomputable def tileCls (D : Dissection N) (L : AddSubgroup Plane) (k : Fin N) : Plane ⧸ L :=
  ((D.tile k).pts 0 : Plane ⧸ L)
theorem vertex_cls (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L) (k : Fin N) (m : Fin 3) :
    ((D.tile k).pts m : Plane ⧸ L) = tileCls D L k := by
  unfold tileCls
  rw [QuotientAddGroup.eq]
  have h0 := hL k 0
  have h1 := hL k 1
  have h2 := hL k 2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl] at h0 h1 h2
  fin_cases m
  · simp
  · have := neg_mem h0
    simpa [neg_sub, sub_eq_neg_add] using this
  · have := h2
    simpa [sub_eq_neg_add] using this
theorem cross_perp_pos {d : Plane} (hd : d ≠ 0) :
    0 < cross d (EuclideanSpace.single 0 (-(d 1)) + EuclideanSpace.single 1 (d 0)) := by
  have hval : cross d (EuclideanSpace.single 0 (-(d 1)) + EuclideanSpace.single 1 (d 0))
      = d 0 * d 0 + d 1 * d 1 := by
    simp [cross]
  rw [hval]
  by_contra hle
  push Not at hle
  have h0 : d 0 = 0 := by nlinarith [mul_self_nonneg (d 0), mul_self_nonneg (d 1)]
  have h1 : d 1 = 0 := by nlinarith [mul_self_nonneg (d 0), mul_self_nonneg (d 1)]
  apply hd
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
theorem shared_coords (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) (hxv : x ∉ D.vertexSet) :
    ∃ m m', (D.tile i).basis.coord m x = 0 ∧ (∀ l, l ≠ m → 0 < (D.tile i).basis.coord l x) ∧
      (D.tile j).basis.coord m' x = 0 ∧ (∀ l, l ≠ m' → 0 < (D.tile j).basis.coord l x) := by
  have hnv := D.notMem_vertexSet hxv
  rcases A1Dir.pt_cases _ hxi (hnv i) with hp | ⟨m, hm, ho⟩
  · exact (A1Dir.interior_meets D hij (A1Dir.mem_interior_of_pos _ hp) hxj).elim
  rcases A1Dir.pt_cases _ hxj (hnv j) with hp' | ⟨m', hm', ho'⟩
  · exact (A1Dir.interior_meets D hij.symm (A1Dir.mem_interior_of_pos _ hp') hxi).elim
  exact ⟨m, m', hm, ho, hm', ho'⟩
theorem shared_interior (D : Dissection N) {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) (hxv : x ∉ D.vertexSet) :
    x ∈ interior D.target.carrier := by
  by_contra hx
  have hnv := D.notMem_vertexSet hxv
  obtain ⟨m, m', hm, ho, hm', ho'⟩ := shared_coords D hij hxi hxj hxv
  have hxe : x ∈ D.eSet (i, m + 1) := (D.tile i).mem_edge_of_coord_zero hm ho
  rcases D.edge_interior_or_side (i, m + 1) hxe (hnv i _) (hnv i _) with h | ⟨j', hj'⟩
  · exact hx h
  set g := D.target.basis.coord (j' + 2) with hgdef
  have hg0 : g x = 0 := D.target.coord_eq_zero_of_mem_edge j' (hj' hxe)
  set w := (D.tile i).leftDir (m + 1) with hw
  have hw0 : w ≠ 0 := (D.tile i).leftDir_ne_zero _
  set v : Plane := EuclideanSpace.single 0 (-(w 1)) + EuclideanSpace.single 1 (w 0) with hv
  have hv1 : 0 < cross w v := cross_perp_pos hw0
  obtain ⟨c, hc, hcw⟩ := D.leftDir_antiparallel hij hm ho hm' ho'
  have hv2 : 0 < cross ((D.tile j).leftDir (m' + 1)) (-v) := by
    rw [hcw, ← hw]
    have : cross (c • w) (-v) = -c * cross w v := by
      simp only [cross, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
      ring
    rw [this]
    exact mul_pos (neg_pos.mpr hc) hv1
  obtain ⟨ε₁, hε₁, h₁⟩ := (D.tile i).mem_interior_of_cross_pos hm ho hv1
  obtain ⟨ε₂, hε₂, h₂⟩ := (D.tile j).mem_interior_of_cross_pos hm' ho' hv2
  set ε := min ε₁ ε₂ / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hε1 : ε < ε₁ := by have := min_le_left ε₁ ε₂; linarith
  have hε2 : ε < ε₂ := by have := min_le_right ε₁ ε₂; linarith
  have hy1 := interior_mono (tile_subset_target D i) (h₁ ε hεpos hε1)
  have hy2 := interior_mono (tile_subset_target D j) (h₂ ε hεpos hε2)
  have hp1 := D.target.interior_coord_pos hy1 (j' + 2)
  have hp2 := D.target.interior_coord_pos hy2 (j' + 2)
  have hg : ∀ u : Plane, g (x + u) = g.linear u + g x := fun u => by
    rw [add_comm x u, ← vadd_eq_add, AffineMap.map_vadd, vadd_eq_add]
  rw [← hgdef, hg] at hp1 hp2
  have hsum : g.linear (ε • v) + g.linear (ε • -v) = 0 := by
    rw [smul_neg, map_neg, add_neg_cancel]
  linarith
section Line
variable (x w : Plane)
noncomputable def ell : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap x (x + w)
theorem ell_apply (t : ℝ) : ell x w t = x + t • w := by
  simp [ell, AffineMap.lineMap_apply, add_comm]
variable {x w}
theorem ell_injective (hw : w ≠ 0) : Function.Injective (ell x w) := by
  intro s t h
  rw [ell_apply, ell_apply] at h
  have h2 : (s - t) • w = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (add_left_cancel h)
  rcases smul_eq_zero.mp h2 with h3 | h3
  · linarith [sub_eq_zero.mp h3]
  · exact absurd h3 hw
theorem f_ell (t : ℝ) : crossL w (ell x w t) = crossL w x := by
  rw [ell_apply, map_add, map_smul, crossL_apply w w, cross_self, smul_zero, add_zero]
theorem exists_param (hw : w ≠ 0) {y : Plane} (hy : crossL w y = crossL w x) :
    ∃ t, ell x w t = y := by
  have h0 : cross w (y - x) = 0 := by
    rw [cross_sub_right]
    simpa [crossL_apply] using sub_eq_zero.mpr hy
  obtain ⟨τ, hτ⟩ := parallel_of_cross_eq_zero hw h0
  exact ⟨τ, by rw [ell_apply, ← hτ]; abel⟩
variable (x w)
noncomputable def par (y : Plane) : ℝ :=
  if h : ∃ t, ell x w t = y then h.choose else 0
variable {x w}
theorem ell_par (hw : w ≠ 0) {y : Plane} (hy : crossL w y = crossL w x) :
    ell x w (par x w y) = y := by
  have h := exists_param hw hy
  unfold par
  rw [dif_pos h]
  exact h.choose_spec
variable (x w)
noncomputable def aP (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  min (par x w ((D.tile e.1).pts e.2)) (par x w ((D.tile e.1).pts (e.2 + 1)))
noncomputable def bP (D : Dissection N) (e : Fin N × Fin 3) : ℝ :=
  max (par x w ((D.tile e.1).pts e.2)) (par x w ((D.tile e.1).pts (e.2 + 1)))
variable {x w}
theorem edge_param (hw : w ≠ 0) (D : Dissection N) {e : Fin N × Fin 3}
    (h1 : crossL w ((D.tile e.1).pts e.2) = crossL w x)
    (h2 : crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x) (t : ℝ) :
    ell x w t ∈ (D.tile e.1).edge e.2 ↔ t ∈ Icc (aP x w D e) (bP x w D e) := by
  have hseg : (D.tile e.1).edge e.2 = ell x w '' segment ℝ (par x w ((D.tile e.1).pts e.2))
      (par x w ((D.tile e.1).pts (e.2 + 1))) := by
    rw [image_segment, ell_par hw h1, ell_par hw h2]
    rfl
  rw [hseg, (ell_injective hw).mem_set_image, segment_eq_uIcc, aP, bP]
  rcases le_total (par x w ((D.tile e.1).pts e.2)) (par x w ((D.tile e.1).pts (e.2 + 1))) with h | h
  · rw [uIcc_of_le h, min_eq_left h, max_eq_right h]
  · rw [uIcc_of_ge h, min_eq_right h, max_eq_left h]
theorem aP_lt_bP (hw : w ≠ 0) (D : Dissection N) {e : Fin N × Fin 3}
    (h1 : crossL w ((D.tile e.1).pts e.2) = crossL w x)
    (h2 : crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x) :
    aP x w D e < bP x w D e := by
  have hsucc : ∀ l : Fin 3, l ≠ l + 1 := by decide
  have hne : par x w ((D.tile e.1).pts e.2) ≠ par x w ((D.tile e.1).pts (e.2 + 1)) := by
    intro h
    have := congrArg (ell x w) h
    rw [ell_par hw h1, ell_par hw h2] at this
    exact hsucc e.2 ((D.tile e.1).indep.injective this)
  exact min_lt_max.mpr hne
theorem cls_aP (hw : w ≠ 0) (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L) {e : Fin N × Fin 3}
    (h1 : crossL w ((D.tile e.1).pts e.2) = crossL w x)
    (h2 : crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x) :
    ((ell x w (aP x w D e) : Plane) : Plane ⧸ L) = tileCls D L e.1 := by
  unfold aP
  rcases min_choice (par x w ((D.tile e.1).pts e.2)) (par x w ((D.tile e.1).pts (e.2 + 1)))
    with h | h <;> rw [h]
  · rw [ell_par hw h1, vertex_cls D L hL]
  · rw [ell_par hw h2, vertex_cls D L hL]
theorem cls_bP (hw : w ≠ 0) (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L) {e : Fin N × Fin 3}
    (h1 : crossL w ((D.tile e.1).pts e.2) = crossL w x)
    (h2 : crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x) :
    ((ell x w (bP x w D e) : Plane) : Plane ⧸ L) = tileCls D L e.1 := by
  unfold bP
  rcases max_choice (par x w ((D.tile e.1).pts e.2)) (par x w ((D.tile e.1).pts (e.2 + 1)))
    with h | h <;> rw [h]
  · rw [ell_par hw h1, vertex_cls D L hL]
  · rw [ell_par hw h2, vertex_cls D L hL]
theorem isChain_lineChain (hw : w ≠ 0) (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L)
    (g : Plane →ₗ[ℝ] ℝ) (d : ℝ) (hg : g ≠ 0)
    (hon : ∀ e ∈ D.lineChain g d, crossL w ((D.tile e.1).pts e.2) = crossL w x ∧
      crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x) :
    IsChain (D.lineChain g d) (aP x w D) (bP x w D)
      (fun t => ((ell x w t : Plane) : Plane ⧸ L)) where
  lt e he := aP_lt_bP hw D (hon e he).1 (hon e he).2
  disj e he e' he' hne := by
    have hle : ∀ {e}, e ∈ D.lineChain g d → ∀ y ∈ (D.tile e.1).carrier, g y ≤ d := fun he =>
      Tri.carrier_subset_halfplane _ g d (Dissection.mem_lineChain.mp he).2.2
    have hsub := D.sameside_edges_subsingleton g d hg hne (hle he) (hle he')
      (D.lineChain_edge_subset he) (D.lineChain_edge_subset he')
    intro s hs t ht
    have hs1 := (edge_param hw D (hon e he).1 (hon e he).2 s).mpr hs.1
    have hs2 := (edge_param hw D (hon e' he').1 (hon e' he').2 s).mpr hs.2
    have ht1 := (edge_param hw D (hon e he).1 (hon e he).2 t).mpr ht.1
    have ht2 := (edge_param hw D (hon e' he').1 (hon e' he').2 t).mpr ht.2
    exact ell_injective hw (hsub ⟨hs1, hs2⟩ ⟨ht1, ht2⟩)
  cls e he := by
    rw [cls_aP hw D L hL (hon e he).1 (hon e he).2, cls_bP hw D L hL (hon e he).1 (hon e he).2]
theorem transfer (hw : w ≠ 0) (D : Dissection N) (hx : x ∈ interior D.target.carrier)
    (g : Plane →ₗ[ℝ] ℝ) (d : ℝ)
    (hon : ∀ e ∈ D.lineChain g d, crossL w ((D.tile e.1).pts e.2) = crossL w x ∧
      crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x)
    (g' : Plane →ₗ[ℝ] ℝ) (d' : ℝ) (hg' : g' ≠ 0)
    (hon' : ∀ e ∈ D.lineChain g' d', crossL w ((D.tile e.1).pts e.2) = crossL w x ∧
      crossL w ((D.tile e.1).pts (e.2 + 1)) = crossL w x)
    (hline : ∀ t, g' (ell x w t) = d') {p : ℝ} (hp : p < 0)
    (hcov : Icc p 0 ⊆ chainUnion (D.lineChain g d) (aP x w D) (bP x w D)) :
    Icc p 0 ⊆ chainUnion (D.lineChain g' d') (aP x w D) (bP x w D) := by
  have hmem : ∀ t ∈ Icc p 0, ∃ e ∈ D.lineChain g d, ell x w t ∈ (D.tile e.1).edge e.2 := by
    intro t ht
    obtain ⟨e, he, hte⟩ := mem_iUnion₂.mp (hcov ht)
    exact ⟨e, he, (edge_param hw D (hon e he).1 (hon e he).2 t).mpr hte⟩
  have hx0 : ell x w 0 = x := by rw [ell_apply, zero_smul, add_zero]
  have hne : ell x w p ≠ ell x w 0 := fun h => hp.ne (ell_injective hw h)
  have hseg : segment ℝ (ell x w p) (ell x w 0) = ell x w '' Icc p 0 := by
    rw [← image_segment, segment_eq_Icc hp.le]
  have hoseg : openSegment ℝ (ell x w p) (ell x w 0) = ell x w '' Ioo p 0 := by
    rw [← image_openSegment, openSegment_eq_Ioo hp]
  have hS : segment ℝ (ell x w p) (ell x w 0) ⊆ {y | g' y = d'} := by
    rw [hseg]
    rintro _ ⟨t, -, rfl⟩
    exact hline t
  have hpT : ell x w p ∈ D.target.carrier := by
    obtain ⟨e, -, he⟩ := hmem p ⟨le_rfl, hp.le⟩
    exact tile_subset_target D e.1 ((D.tile e.1).edge_subset_carrier e.2 he)
  have hint : openSegment ℝ (ell x w p) (ell x w 0) ⊆ interior D.target.carrier := by
    rw [hx0]
    exact D.target.convex.openSegment_closure_interior_subset_interior (subset_closure hpT) hx
  have hwall : ∀ y ∈ openSegment ℝ (ell x w p) (ell x w 0), ∀ i,
      y ∉ interior (D.tile i).carrier := by
    rw [hoseg]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨e, -, he⟩ := hmem t (Ioo_subset_Icc_self ht)
    exact D.edge_point_not_interior he
  set Z : Set ℝ := ell x w ⁻¹' D.vertexSet with hZ
  have hZfin : Z.Finite := D.vertexSet_finite.preimage (ell_injective hw).injOn
  have hgood : Ioo p 0 ∩ Zᶜ ⊆ chainUnion (D.lineChain g' d') (aP x w D) (bP x w D) := by
    rintro t ⟨ht, htZ⟩
    have hy : ell x w t ∈ openSegment ℝ (ell x w p) (ell x w 0) := by
      rw [hoseg]; exact ⟨t, ht, rfl⟩
    obtain ⟨e, he, hte⟩ := D.wall_cover g' d' hg' hne hS hint hwall hy htZ
    exact mem_biUnion he ((edge_param hw D (hon' e he).1 (hon' e he).2 t).mp hte)
  have hdense : Dense Zᶜ := hZfin.countable.dense_compl ℝ
  calc Icc p 0 = closure (Ioo p 0) := (closure_Ioo hp.ne).symm
    _ ⊆ closure (closure (Ioo p 0 ∩ Zᶜ)) :=
        closure_mono (hdense.open_subset_closure_inter isOpen_Ioo)
    _ = closure (Ioo p 0 ∩ Zᶜ) := closure_closure
    _ ⊆ _ := closure_minimal hgood (isClosed_chainUnion _ _ _)
end Line
theorem mem_side_chains (D : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (k : Fin N) (m : Fin 3)
    (h1 : f ((D.tile k).pts (m + 1)) = c) (h2 : f ((D.tile k).pts (m + 2)) = c)
    (h3 : f ((D.tile k).pts m) ≠ c) :
    (k, m + 1) ∈ D.lineChain f c ∨ (k, m + 1) ∈ D.lineChain (-f) (-c) := by
  have hidx : m + 1 + 1 = m + 2 := by fin_cases m <;> rfl
  have hall : ∀ l : Fin 3, l = m ∨ l = m + 1 ∨ l = m + 2 := by
    have : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
    exact fun l => this m l
  rcases lt_or_gt_of_ne h3 with hlt | hgt
  · left
    refine Dissection.mem_lineChain.mpr ⟨h1, by simpa [hidx] using h2, fun l => ?_⟩
    rcases hall l with rfl | rfl | rfl
    · exact hlt.le
    · exact h1.le
    · exact h2.le
  · right
    refine Dissection.mem_lineChain.mpr ⟨by simp [h1], by simp [hidx, h2], fun l => ?_⟩
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    rcases hall l with rfl | rfl | rfl
    · exact hgt.le
    · exact h1.ge
    · exact h2.ge
theorem shared_cls (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L)
    {i j : Fin N} (hij : i ≠ j) {x : Plane}
    (hxi : x ∈ (D.tile i).carrier) (hxj : x ∈ (D.tile j).carrier) (hxv : x ∉ D.vertexSet) :
    tileCls D L i = tileCls D L j := by
  obtain ⟨m, m', hm, ho, hm', ho'⟩ := shared_coords D hij hxi hxj hxv
  have hx := shared_interior D hij hxi hxj hxv
  set w := (D.tile i).leftDir (m + 1) with hwdef
  have hw : w ≠ 0 := (D.tile i).leftDir_ne_zero _
  set f := crossL w with hfdef
  have hf : f ≠ 0 := crossL_ne_zero hw
  have hfw : f w = 0 := by rw [hfdef, crossL_apply, cross_self]
  obtain ⟨hi1, hi2, hi3⟩ := (D.tile i).edge_on_line f (f x) hf hm ho rfl hw hfw
    (by rw [← hwdef, cross_self])
  obtain ⟨c, -, hcw⟩ := D.leftDir_antiparallel hij hm ho hm' ho'
  obtain ⟨hj1, hj2, hj3⟩ := (D.tile j).edge_on_line f (f x) hf hm' ho' rfl hw hfw
    (by rw [hcw, ← hwdef, cross_smul_left, cross_self, mul_zero])
  set S := D.lineChain f (f x)
  set T := D.lineChain (-f) (-(f x))
  have honS : ∀ e ∈ S, f ((D.tile e.1).pts e.2) = f x ∧ f ((D.tile e.1).pts (e.2 + 1)) = f x :=
    fun e he => ⟨(Dissection.mem_lineChain.mp he).1, (Dissection.mem_lineChain.mp he).2.1⟩
  have honT : ∀ e ∈ T, f ((D.tile e.1).pts e.2) = f x ∧ f ((D.tile e.1).pts (e.2 + 1)) = f x := by
    intro e he
    obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
    simp only [LinearMap.neg_apply, neg_inj] at h1 h2
    exact ⟨h1, h2⟩
  have hSc := isChain_lineChain hw D L hL f (f x) hf honS
  have hTc := isChain_lineChain hw D L hL (-f) (-(f x)) (neg_ne_zero.mpr hf) honT
  have hlineS : ∀ t, f (ell x w t) = f x := f_ell
  have hlineT : ∀ t, (-f) (ell x w t) = -(f x) := fun t => by
    rw [LinearMap.neg_apply, f_ell]
  have htr₁ := fun p (hp : p < 0) =>
    transfer hw D hx f (f x) honS (-f) (-(f x)) (neg_ne_zero.mpr hf) honT hlineT hp
  have htr₂ := fun p (hp : p < 0) =>
    transfer hw D hx (-f) (-(f x)) honT f (f x) hf honS hlineS hp
  have hidx : ∀ m : Fin 3, m + 1 + 1 = m + 2 := by decide
  have hx0 : ell x w 0 = x := by rw [ell_apply, zero_smul, add_zero]
  have hmemi : (0 : ℝ) ∈ Icc (aP x w D (i, m + 1)) (bP x w D (i, m + 1)) := by
    refine (edge_param hw D hi1 (by simpa [hidx, hfdef, crossL_apply] using hi2) 0).mp ?_
    rw [hx0]
    exact (D.tile i).mem_edge_of_coord_zero hm ho
  have hmemj : (0 : ℝ) ∈ Icc (aP x w D (j, m' + 1)) (bP x w D (j, m' + 1)) := by
    refine (edge_param hw D hj1 (by simpa [hidx, hfdef, crossL_apply] using hj2) 0).mp ?_
    rw [hx0]
    exact (D.tile j).mem_edge_of_coord_zero hm' ho'
  have hkey := class_eq hSc hTc htr₁ htr₂ (mem_side_chains D f (f x) i m hi1 hi2 hi3)
    (mem_side_chains D f (f x) j m' hj1 hj2 hj3) hmemi hmemj
  rw [cls_aP hw D L hL hi1 (by simpa [hidx, hfdef, crossL_apply] using hi2),
    cls_aP hw D L hL hj1 (by simpa [hidx, hfdef, crossL_apply] using hj2)] at hkey
  exact hkey
end Erdos634.Geometry.A1Pos
end

section
open scoped Classical
namespace Erdos634.Geometry.A1Pos
open Erdos634.Geometry Set MeasureTheory
variable {N : ℕ}
theorem volume_line_eq_zero {v p : Plane} (hv : v ≠ 0) :
    volume {y : Plane | cross v (y - p) = 0} = 0 := by
  have hset : {y : Plane | cross v (y - p) = 0} =
      (AffineSubspace.mk' p (LinearMap.ker (crossL v)) : Set Plane) := by
    ext y
    simp [AffineSubspace.mem_mk', LinearMap.mem_ker, crossL_apply]
  rw [hset]
  refine Measure.addHaar_affineSubspace volume _ ?_
  intro htop
  have hmem : (EuclideanSpace.single 0 (-(v 1)) + EuclideanSpace.single 1 (v 0)) + p ∈
      AffineSubspace.mk' p (LinearMap.ker (crossL v)) := by
    rw [htop]; exact AffineSubspace.mem_top ℝ Plane _
  rw [AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_right, LinearMap.mem_ker,
    crossL_apply] at hmem
  exact (cross_perp_pos hv).ne' hmem
theorem cross_eq_zero_of_mem_segment {a c f : Plane} (hf : f ∈ segment ℝ a c) :
    cross (f - a) (c - a) = 0 := by
  rw [segment_eq_image'] at hf
  obtain ⟨θ, -, rfl⟩ := hf
  rw [add_sub_cancel_left, cross_smul_left, cross_self, mul_zero]
theorem convex_diff_finite_isPreconnected {K : Set Plane} (hK : Convex ℝ K)
    (hint : (interior K).Nonempty) {F : Set Plane} (hF : F.Finite) : IsPreconnected (K \ F) := by
  refine isPreconnected_of_forall_pair fun a ha b hb => ?_
  set Z : Set Plane :=
    ⋃ f ∈ F, ({y | cross (f - a) (y - a) = 0} ∪ {y | cross (f - b) (y - b) = 0}) with hZdef
  have hZ : volume Z = 0 := by
    refine (measure_biUnion_null_iff hF.countable).mpr fun f hf => ?_
    have hfa : f - a ≠ 0 := sub_ne_zero.mpr fun h => ha.2 (h ▸ hf)
    have hfb : f - b ≠ 0 := sub_ne_zero.mpr fun h => hb.2 (h ▸ hf)
    exact measure_union_null (volume_line_eq_zero hfa) (volume_line_eq_zero hfb)
  obtain ⟨c, hcK, hcZ⟩ : ∃ c ∈ interior K, c ∉ Z := by
    by_contra h
    push Not at h
    have hpos := isOpen_interior.measure_pos volume hint
    have := measure_mono (μ := volume) (show interior K ⊆ Z from h)
    rw [hZ] at this
    exact (lt_of_lt_of_le hpos this).ne rfl
  have hc : c ∈ K := interior_subset hcK
  have hA : segment ℝ a c ⊆ K \ F := by
    intro y hy
    refine ⟨hK.segment_subset ha.1 hc hy, fun hyF => hcZ ?_⟩
    exact mem_iUnion₂.mpr ⟨y, hyF, Or.inl (cross_eq_zero_of_mem_segment hy)⟩
  have hB : segment ℝ b c ⊆ K \ F := by
    intro y hy
    refine ⟨hK.segment_subset hb.1 hc hy, fun hyF => hcZ ?_⟩
    exact mem_iUnion₂.mpr ⟨y, hyF, Or.inr (cross_eq_zero_of_mem_segment hy)⟩
  refine ⟨segment ℝ a c ∪ segment ℝ b c, union_subset hA hB, Or.inl (left_mem_segment ℝ a c),
    Or.inr (left_mem_segment ℝ b c), ?_⟩
  exact IsPreconnected.union c (right_mem_segment ℝ a c) (right_mem_segment ℝ b c)
    (convex_segment a c).isPreconnected (convex_segment b c).isPreconnected
theorem exists_nonvertex (D : Dissection N) (i : Fin N) :
    ∃ x ∈ (D.tile i).carrier, x ∉ D.vertexSet := by
  have hns : ¬ (D.tile i).carrier ⊆ D.vertexSet := fun h =>
    (D.tile i).volume_pos.ne'
      (measure_mono_null h (D.vertexSet_finite.countable.measure_zero _))
  obtain ⟨x, hx, hxv⟩ := Set.not_subset.mp hns
  exact ⟨x, hx, hxv⟩
theorem all_cls_eq (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L) (i j : Fin N) :
    tileCls D L i = tileCls D L j := by
  by_contra hij
  set κ := tileCls D L i
  let U : Set Plane := ⋃ k ∈ {k | tileCls D L k ≠ κ}, (D.tile k).carrier
  let W : Set Plane := ⋃ k ∈ {k | tileCls D L k = κ}, (D.tile k).carrier
  have hUc : IsClosed U :=
    (Set.toFinite _).isClosed_biUnion fun k _ => (D.tile k).isCompact.isClosed
  have hWc : IsClosed W :=
    (Set.toFinite _).isClosed_biUnion fun k _ => (D.tile k).isCompact.isClosed
  have hconn : IsPreconnected (D.target.carrier \ D.vertexSet) :=
    convex_diff_finite_isPreconnected D.target.convex D.target.interior_nonempty
      D.vertexSet_finite
  have hcov : D.target.carrier \ D.vertexSet ⊆ U ∪ W := by
    rintro x ⟨hx, -⟩
    rw [← D.covers] at hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    by_cases hg : tileCls D L k = κ
    · exact Or.inr (mem_biUnion (x := k) hg hk)
    · exact Or.inl (mem_biUnion (x := k) hg hk)
  have hW : ((D.target.carrier \ D.vertexSet) ∩ W).Nonempty := by
    obtain ⟨x, hx, hxv⟩ := exists_nonvertex D i
    exact ⟨x, ⟨tile_subset_target D i hx, hxv⟩, mem_biUnion (x := i) (rfl : tileCls D L i = κ) hx⟩
  have hU : ((D.target.carrier \ D.vertexSet) ∩ U).Nonempty := by
    obtain ⟨x, hx, hxv⟩ := exists_nonvertex D j
    exact ⟨x, ⟨tile_subset_target D j hx, hxv⟩, mem_biUnion (x := j) (Ne.symm hij) hx⟩
  obtain ⟨x, ⟨-, hxv⟩, hxU, hxW⟩ :=
    isPreconnected_closed_iff.mp hconn U W hUc hWc hcov hU hW
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxU
  obtain ⟨k', hk', hxk'⟩ := mem_iUnion₂.mp hxW
  have hkk : k ≠ k' := fun h => hk (h ▸ hk')
  exact hk ((shared_cls D L hL hkk hxk hxk' hxv).trans hk')
theorem target_vertex_extreme (T : Tri) (k : Fin 3) :
    T.pts k ∈ T.carrier.extremePoints ℝ := by
  have hb : ∀ i : Fin 3, T.pts i = (T.basis : Fin 3 → Plane) i := fun _ => rfl
  refine mem_extremePoints.mpr ⟨subset_convexHull ℝ _ ⟨k, rfl⟩, fun y hy z hz hk => ?_⟩
  obtain ⟨α, β, hα, hβ, hαβ, hyz⟩ := hk
  rw [T.carrier_eq_nonneg_coord] at hy hz
  have hzero : ∀ l, l ≠ k → T.basis.coord l y = 0 ∧ T.basis.coord l z = 0 := by
    intro l hl
    have h1 : T.basis.coord l (α • y + β • z) = α * T.basis.coord l y + β * T.basis.coord l z := by
      rw [Convex.combo_affine_apply hαβ]; rfl
    rw [hyz, hb, AffineBasis.coord_apply_ne _ hl] at h1
    have hy0 := hy l
    have hz0 := hz l
    constructor <;> nlinarith [mul_nonneg hα.le hy0, mul_nonneg hβ.le hz0]
  have hvert : ∀ w : Plane, (∀ l, l ≠ k → T.basis.coord l w = 0) → w = T.pts k := by
    intro w hw
    have hne : k + 1 ≠ k + 2 := by fin_cases k <;> decide
    have h1 : k + 1 ≠ k := by fin_cases k <;> decide
    have h2 : k + 2 ≠ k := by fin_cases k <;> decide
    obtain ⟨p, hp⟩ := T.eq_vertex_of_two_coords_zero hne (hw _ h1) (hw _ h2)
    have hall : ∀ q : Fin 3, q = k ∨ q = k + 1 ∨ q = k + 2 := by
      have : ∀ u v : Fin 3, v = u ∨ v = u + 1 ∨ v = u + 2 := by decide
      exact fun q => this k q
    rcases hall p with rfl | rfl | rfl
    · exact hp
    · have := hw _ h1
      rw [hp, hb, AffineBasis.coord_apply_eq] at this
      exact absurd this one_ne_zero
    · have := hw _ h2
      rw [hp, hb, AffineBasis.coord_apply_eq] at this
      exact absurd this one_ne_zero
  exact ⟨hvert y fun l hl => (hzero l hl).1, hvert z fun l hl => (hzero l hl).2⟩
theorem target_vertex_is_tile_vertex (D : Dissection N) (k : Fin 3) :
    ∃ i m, D.target.pts k = (D.tile i).pts m := by
  have hk : D.target.pts k ∈ D.target.carrier := subset_convexHull ℝ _ ⟨k, rfl⟩
  rw [← D.covers] at hk
  obtain ⟨i, hi⟩ := mem_iUnion.mp hk
  have hext : D.target.pts k ∈ (D.tile i).carrier.extremePoints ℝ :=
    inter_extremePoints_subset_extremePoints_of_subset (tile_subset_target D i)
      ⟨hi, target_vertex_extreme D.target k⟩
  obtain ⟨m, hm⟩ := extremePoints_convexHull_subset hext
  exact ⟨i, m, hm.symm⟩
noncomputable def edgeSpan (D : Dissection N) : AddSubgroup Plane :=
  AddSubgroup.closure {v | ∃ k : Fin N, ∃ m : Fin 3, v = (D.tile k).pts (m + 1) - (D.tile k).pts m}
theorem corner_mem_of_edges (D : Dissection N) (L : AddSubgroup Plane)
    (hL : ∀ k (m : Fin 3), (D.tile k).pts (m + 1) - (D.tile k).pts m ∈ L) (i : Fin N) (k : Fin 3) :
    (D.tile i).pts k - D.target.pts 0 ∈ L := by
  obtain ⟨i₀, m₀, hA⟩ := target_vertex_is_tile_vertex D 0
  have h1 := vertex_cls D L hL i k
  have h2 := vertex_cls D L hL i₀ m₀
  rw [all_cls_eq D L hL i i₀, ← h2, ← hA, QuotientAddGroup.eq] at h1
  have := neg_mem h1
  simpa [neg_add_eq_sub, sub_eq_add_neg, add_comm] using this
noncomputable def Lform (D : CongruentDissection N) (n : ℕ) : AddSubgroup Plane :=
  AddSubgroup.closure {v | ∃ (k : Fin 3) (d : Dir),
    d.angle - (D.target.leftUnit 0).angle ∈ A1Dir.H n ∧
      v = dist (D.model.pts k) (D.model.pts (k + 1)) • d.1}
theorem side_length_model (D : CongruentDissection N) (i : Fin N) (m : Fin 3) :
    ∃ k : Fin 3, ‖(D.tile i).pts (m + 1) - (D.tile i).pts m‖
      = dist (D.model.pts k) (D.model.pts (k + 1)) := by
  obtain ⟨σ, hσ⟩ := (D.tiles_congruent i).dist_eq
  have hsucc : ∀ l : Fin 3, l + 1 ≠ l := by decide
  have hneq : σ (m + 1) ≠ σ m := fun h => hsucc m (σ.injective h)
  have key : ∀ p q : Fin 3, p ≠ q → q = p + 1 ∨ p = q + 1 := by decide
  rw [← dist_eq_norm, hσ]
  rcases key _ _ hneq with h | h
  · exact ⟨σ (m + 1), by rw [h]⟩
  · exact ⟨σ m, by rw [dist_comm, h]⟩
theorem edge_mem_Lform (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) (m : Fin 3) :
    (D.tile i).pts (m + 1) - (D.tile i).pts m ∈ Lform D n := by
  set v := (D.tile i).pts (m + 1) - (D.tile i).pts m with hvdef
  have hsucc : ∀ l : Fin 3, l + 1 ≠ l := by decide
  have hv : v ≠ 0 := sub_ne_zero.mpr fun h => hsucc m ((D.tile i).indep.injective h)
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let dv : Dir := ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv]⟩
  have hvd : v = ‖v‖ • dv.1 := by
    show v = ‖v‖ • (‖v‖⁻¹ • v)
    rw [smul_smul, mul_inv_cancel₀ hnv, one_smul]
  have hcos := A1Dir.edge_dir_coset D hn a ha i m
  have hang : dv.angle - (D.target.leftUnit 0).angle ∈ A1Dir.H n := by
    rcases (D.tile i).leftDir_eq_or m with h | h
    · have hdu : (D.tile i).leftUnit m = dv := by
        apply Subtype.ext
        simp only [Tri.leftUnit, dv, h, hvdef]
      rwa [hdu] at hcos
    · have hdu : (D.tile i).leftUnit m = Dir.neg dv := by
        apply Subtype.ext
        simp only [Tri.leftUnit, Dir.neg, dv, h, hvdef, norm_neg, smul_neg]
      rw [hdu, Dir.angle_neg] at hcos
      have := sub_mem hcos (A1Dir.pi_mem hn)
      convert this using 1
      abel
  obtain ⟨k, hk⟩ := side_length_model D i m
  refine AddSubgroup.subset_closure ⟨k, dv, hang, ?_⟩
  rw [← hk]
  exact hvd
theorem lemma1_positions (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) (k : Fin 3) :
    (D.tile i).pts k - D.target.pts 0 ∈ Lform D n :=
  corner_mem_of_edges D.toDissection _ (edge_mem_Lform D hn a ha) i k
theorem lemma1_positions_target (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (k : Fin 3) :
    D.target.pts k - D.target.pts 0 ∈ Lform D n := by
  obtain ⟨i, m, h⟩ := target_vertex_is_tile_vertex D.toDissection k
  rw [h]
  exact lemma1_positions D hn a ha i m
end Erdos634.Geometry.A1Pos
end

section
open scoped Classical
namespace Erdos634.Geometry.A1Field
open Erdos634.Geometry Complex
open Erdos634.Geometry.CaseA.LemmaV (zeta Kf zeta_pow_n law_sines angle_pos angle_lt_pi)
variable {N : ℕ}
theorem zeta_mem (n : ℕ) : zeta n ∈ Kf n := IntermediateField.mem_adjoin_simple_self ℚ _
theorem exp_int_mem {n : ℕ} (hn : 0 < n) (j : ℤ) :
    Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) ∈ Kf n := by
  have h : Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) = zeta n ^ (2 * j) := by
    rw [zeta, ← Complex.exp_int_mul]
    congr 1
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast; field_simp; ring
  rw [h]; exact zpow_mem (zeta_mem n) _
theorem sin_mem {n : ℕ} (hn : 0 < n) (a : ℕ) :
    ((Real.sin ((a : ℝ) * Real.pi / n) : ℝ) : ℂ) ∈ Kf n := by
  have hI : I ∈ Kf n := by rw [← zeta_pow_n hn]; exact pow_mem (zeta_mem n) n
  have e1 := exp_int_mem hn (a : ℤ)
  have e2 := exp_int_mem hn (-(a : ℤ))
  have h : ((Real.sin ((a : ℝ) * Real.pi / n) : ℝ) : ℂ)
      = (Complex.exp ((((-(a : ℤ) : ℤ) : ℝ) * Real.pi / n : ℝ) * I)
          - Complex.exp ((((a : ℤ) : ℝ) * Real.pi / n : ℝ) * I)) * I * (1 + 1)⁻¹ := by
    rw [Complex.ofReal_sin, Complex.sin]; push_cast; ring_nf
  rw [h]
  exact mul_mem (mul_mem (sub_mem e2 e1) hI) (inv_mem (add_mem (one_mem _) (one_mem _)))
noncomputable def circD (T : Tri) : ℝ := T.oppLen 0 / Real.sin (T.angleAt 0)
theorem sin_angle_pos (T : Tri) (k : Fin 3) : 0 < Real.sin (T.angleAt k) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos T k) (angle_lt_pi T k)
theorem circD_pos (T : Tri) : 0 < circD T := by
  have h12 : T.pts 1 ≠ T.pts 2 := fun h => absurd (T.indep.injective h) (by decide)
  exact div_pos (dist_pos.mpr h12) (sin_angle_pos T 0)
theorem oppLen_eq (T : Tri) (k : Fin 3) : T.oppLen k = circD T * Real.sin (T.angleAt k) := by
  have hs := (sin_angle_pos T 0).ne'
  have h0 : Real.sin (T.angleAt 1) * T.oppLen 0 = Real.sin (T.angleAt 0) * T.oppLen 1 :=
    law_sines T 0
  have h2 := law_sines T 2
  have e : (2 : Fin 3) + 1 = 0 := rfl
  rw [e] at h2
  unfold circD
  fin_cases k
  · show T.oppLen 0 = T.oppLen 0 / Real.sin (T.angleAt 0) * Real.sin (T.angleAt 0)
    field_simp
  · show T.oppLen 1 = T.oppLen 0 / Real.sin (T.angleAt 0) * Real.sin (T.angleAt 1)
    field_simp; linarith
  · show T.oppLen 2 = T.oppLen 0 / Real.sin (T.angleAt 0) * Real.sin (T.angleAt 2)
    field_simp; linarith
noncomputable def wAB (D : CongruentDissection N) : ℂ :=
  ((‖D.target.pts 1 - D.target.pts 0‖⁻¹ : ℝ) : ℂ) * toC (D.target.pts 1 - D.target.pts 0)
noncomputable def zc (D : CongruentDissection N) (P : Plane) : ℂ :=
  toC (P - D.target.pts 0) * ((wAB D)⁻¹ / ((circD D.model : ℝ) : ℂ))
noncomputable def Lpaper (n : ℕ) (a : Fin 3 → ℕ) : AddSubgroup ℂ :=
  AddSubgroup.closure {x | ∃ (k : Fin 3) (j : ℤ),
    x = ((Real.sin ((a k : ℝ) * Real.pi / n) : ℝ) : ℂ) * Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I)}
theorem AB_ne (D : CongruentDissection N) : D.target.pts 1 - D.target.pts 0 ≠ 0 :=
  sub_ne_zero.mpr fun h => absurd (D.target.indep.injective h) (by decide)
theorem norm_wAB (D : CongruentDissection N) : ‖wAB D‖ = 1 := by
  have hx : ‖D.target.pts 1 - D.target.pts 0‖ ≠ 0 := norm_ne_zero_iff.mpr (AB_ne D)
  rw [wAB, norm_mul, Complex.norm_real, LinearIsometryEquiv.norm_map, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hx]
theorem wAB_ne (D : CongruentDissection N) : wAB D ≠ 0 := by
  intro h; have := norm_wAB D; rw [h, norm_zero] at this; norm_num at this
theorem arg_wAB (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) :
    ((arg (wAB D) : ℝ) : Real.Angle) - (D.target.leftUnit 0).angle ∈ A1Dir.H n := by
  have hpos : 0 < ‖D.target.pts 1 - D.target.pts 0‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (AB_ne D))
  rw [wAB, Complex.arg_real_mul _ hpos, Tri.leftUnit_angle]
  have e01 : (0 : Fin 3) + 1 = 1 := rfl
  rcases D.target.leftDir_eq_or 0 with h | h <;> rw [e01] at h
  · rw [h]; simp
  · rw [h, map_neg, Complex.arg_neg_coe_angle (toC_ne_zero (AB_ne D))]
    have := neg_mem (A1Dir.pi_mem hn)
    convert this using 1
    abel
theorem exp_eq_of_angle {x y : ℝ} (h : (x : Real.Angle) = y) :
    Complex.exp ((x : ℂ) * I) = Complex.exp ((y : ℂ) * I) := by
  have hc : Real.cos x = Real.cos y := by rw [← Real.Angle.cos_coe, h, Real.Angle.cos_coe]
  have hs : Real.sin x = Real.sin y := by rw [← Real.Angle.sin_coe, h, Real.Angle.sin_coe]
  rw [Complex.exp_mul_I, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos,
    ← ofReal_sin, hc, hs]
theorem unit_eq_exp {u : ℂ} (hu : ‖u‖ = 1) : u = Complex.exp ((arg u : ℂ) * I) := by
  have := Complex.norm_mul_exp_arg_mul_I u
  rw [hu] at this
  simpa using this.symm
theorem rot_eq {n : ℕ} {u w : ℂ} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (h : ((arg u : ℝ) : Real.Angle) - (arg w : Real.Angle) ∈ A1Dir.H n) :
    ∃ j : ℤ, u * w⁻¹ = Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) := by
  obtain ⟨j, hj⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  refine ⟨j, ?_⟩
  rw [unit_eq_exp hu, unit_eq_exp hw, ← Complex.exp_neg, ← Complex.exp_add]
  have hang : ((arg u - arg w : ℝ) : Real.Angle) = (((j : ℝ) * Real.pi / n : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, ← hj, ← Real.Angle.coe_zsmul, zsmul_eq_mul]
    congr 1; ring
  have := exp_eq_of_angle hang
  rw [← this]; congr 1; push_cast; ring
theorem Lform_map (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    ∀ v ∈ A1Pos.Lform D n, toC v * ((wAB D)⁻¹ / ((circD D.model : ℝ) : ℂ)) ∈ Lpaper n a := by
  set c : ℂ := (wAB D)⁻¹ / ((circD D.model : ℝ) : ℂ) with hcdef
  let f : Plane →+ ℂ := AddMonoidHom.mk' (fun v => toC v * c) (fun x y => by
    simp only [map_add, add_mul])
  have hL : ((circD D.model : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (circD_pos D.model).ne'
  have hle : A1Pos.Lform D n ≤ (Lpaper n a).comap f := by
    rw [A1Pos.Lform, AddSubgroup.closure_le]
    rintro _ ⟨k, d, hd, rfl⟩
    show toC (dist (D.model.pts k) (D.model.pts (k + 1)) • d.1) * c ∈ Lpaper n a
    have hsd : dist (D.model.pts k) (D.model.pts (k + 1)) = D.model.oppLen (k + 2) := by
      have e1 : k + 2 + 1 = k := by revert k; decide
      have e2 : k + 2 + 2 = k + 1 := by revert k; decide
      rw [Tri.oppLen, e1, e2]
    have hu : ‖toC d.1‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact d.2
    have hdiff : ((arg (toC d.1) : ℝ) : Real.Angle) - (arg (wAB D) : Real.Angle) ∈ A1Dir.H n := by
      have := sub_mem hd (arg_wAB D hn)
      convert this using 1
      show _ = (Dir.angle d) - _ - _
      unfold Dir.angle; abel
    obtain ⟨j, hj⟩ := rot_eq hu (norm_wAB D) hdiff
    have hval : toC (dist (D.model.pts k) (D.model.pts (k + 1)) • d.1) * c
        = ((Real.sin ((a (k + 2) : ℝ) * Real.pi / n) : ℝ) : ℂ)
            * Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) := by
      rw [map_smul, Complex.real_smul, hsd, oppLen_eq, ha, ← hj, hcdef]
      push_cast
      field_simp
    rw [hval]
    exact AddSubgroup.subset_closure ⟨k + 2, j, rfl⟩
  intro v hv
  exact hle hv
theorem Lpaper_le {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ) : ∀ x ∈ Lpaper n a, x ∈ Kf n := by
  intro x hx
  have hle : Lpaper n a ≤ (Kf n).toSubfield.toSubring.toAddSubgroup := by
    rw [Lpaper, AddSubgroup.closure_le]
    rintro _ ⟨k, j, rfl⟩
    exact (show _ ∈ Kf n from mul_mem (sin_mem hn (a k)) (exp_int_mem hn j))
  exact hle hx
theorem zc_A (D : CongruentDissection N) : zc D (D.target.pts 0) = 0 := by
  simp [zc]
theorem zc_B (D : CongruentDissection N) :
    zc D (D.target.pts 1)
      = ((dist (D.target.pts 1) (D.target.pts 0) / circD D.model : ℝ) : ℂ) := by
  have hx := AB_ne D
  have hn : (‖D.target.pts 1 - D.target.pts 0‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hx
  have hz := toC_ne_zero hx
  have hL : ((circD D.model : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (circD_pos D.model).ne'
  rw [zc, wAB, dist_eq_norm]
  push_cast
  field_simp
theorem lemma1_full (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    0 < circD D.model ∧
    (∀ k, D.model.oppLen k = circD D.model * Real.sin ((a k : ℝ) * Real.pi / n)) ∧
    zc D (D.target.pts 0) = 0 ∧
    zc D (D.target.pts 1) = ((dist (D.target.pts 1) (D.target.pts 0) / circD D.model : ℝ) : ℂ) ∧
    0 < dist (D.target.pts 1) (D.target.pts 0) / circD D.model ∧
    (∀ i k, (D.tile i).pts k - D.target.pts 0 ∈ A1Pos.Lform D n) ∧
    (∀ i k, zc D ((D.tile i).pts k) ∈ Lpaper n a) ∧
    (∀ k, zc D (D.target.pts k) ∈ Lpaper n a) ∧
    (∀ x ∈ Lpaper n a, x ∈ Kf n) := by
  refine ⟨circD_pos _, fun k => by rw [oppLen_eq, ha], zc_A D, zc_B D, ?_,
    A1Pos.lemma1_positions D hn a ha, fun i k => ?_, fun k => ?_, Lpaper_le hn a⟩
  · exact div_pos (dist_pos.mpr fun h => absurd (D.target.indep.injective h) (by decide))
      (circD_pos _)
  · exact Lform_map D hn a ha _ (A1Pos.lemma1_positions D hn a ha i k)
  · exact Lform_map D hn a ha _ (A1Pos.lemma1_positions_target D hn a ha k)
end Erdos634.Geometry.A1Field
end

section
open scoped BigOperators
namespace Erdos634.LemmaKStar
variable (n : ℕ) (a : Fin 3 → ℕ) (f : Fin 3 → Fin 3 → ℕ)
def yv (k : ℤ) (i : Fin 3) : ℚ := Int.fract (((k * (a i : ℤ) : ℤ) : ℚ) / n)
def sT (k : ℤ) : ℚ := ∑ i, yv n a k i
def uu (j : Fin 3) : ℕ := ∑ i, f j i * a i
def xv (k : ℤ) (j : Fin 3) : ℚ := Int.fract (((k * (uu a f j : ℤ) : ℤ) : ℚ) / n)
def sABC (k : ℤ) : ℚ := ∑ j, xv n a f k j
def xp (k : ℤ) (i : Fin 3) : ℚ := if sT n a k = 1 then yv n a k i else 1 - yv n a k i
def xpu (k : ℤ) (j : Fin 3) : ℚ := if sT n a k = 1 then xv n a f k j else 1 - xv n a f k j
def K1 (k : ℤ) : Prop := sT n a k = sABC n a f k
def K2 (k : ℤ) : Prop := ∀ j, ∑ i, (f j i : ℚ) * xp n a k i = xpu n a f k j
def FF (i : Fin 3) : ℕ := ∑ j, f j i
variable {n a f}
theorem a_lt (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) (i : Fin 3) : a i < n := by
  have h0 := ha 0; have h1 := ha 1; have h2 := ha 2
  rw [Fin.sum_univ_three] at hsum
  fin_cases i <;> simp <;> omega
theorem yv_ne (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) {k : ℤ} (hk : Int.gcd k n = 1)
    (i : Fin 3) : yv n a k i ≠ 0 := by
  intro h
  unfold yv at h
  have hn : (0 : ℚ) < n := by
    have := a_lt hsum ha i; exact_mod_cast (show 0 < n by omega)
  set x : ℚ := (((k * (a i : ℤ) : ℤ) : ℚ) / n)
  have hx : x = ⌊x⌋ := by have := Int.floor_add_fract x; rw [h] at this; linarith
  have hq : ((k * (a i : ℤ) : ℤ) : ℚ) = ((⌊x⌋ * (n : ℤ) : ℤ) : ℚ) := by
    have hxn : ((k * (a i : ℤ) : ℤ) : ℚ) = x * n := by simp only [x]; field_simp
    rw [hxn]; push_cast; rw [← hx]
  have hz : k * (a i : ℤ) = ⌊x⌋ * (n : ℤ) := by exact_mod_cast hq
  have hdvd : (n : ℤ) ∣ (a i : ℤ) * k := ⟨⌊x⌋, by rw [mul_comm, hz, mul_comm]⟩
  have hcop : IsCoprime (n : ℤ) k := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hk
  have := Int.le_of_dvd (by have := ha i; omega) (hcop.dvd_of_dvd_mul_right hdvd)
  have := a_lt hsum ha i
  omega
theorem sum_raw (hsum : ∑ i, a i = n) (hn : 0 < n) (k : ℤ) :
    ∑ i, (((k * (a i : ℤ) : ℤ) : ℚ) / n) = k := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : ((a 0 : ℚ) + a 1 + a 2) = n := by
    rw [Fin.sum_univ_three] at hsum; exact_mod_cast hsum
  rw [Fin.sum_univ_three]; push_cast
  field_simp
  rw [hs]
theorem sT_int (hsum : ∑ i, a i = n) (hn : 0 < n) (k : ℤ) : ∃ z : ℤ, sT n a k = z := by
  refine ⟨k - ∑ i, ⌊(((k * (a i : ℤ) : ℤ) : ℚ) / n)⌋, ?_⟩
  unfold sT yv
  simp only [← Int.self_sub_floor, Finset.sum_sub_distrib, sum_raw hsum hn]
  push_cast; ring
theorem sT_12 (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) {k : ℤ} (hk : Int.gcd k n = 1) :
    sT n a k = 1 ∨ sT n a k = 2 := by
  have hn : 0 < n := by have := a_lt hsum ha 0; omega
  obtain ⟨z, hz⟩ := sT_int hsum hn k
  have hpos : ∀ i, 0 < yv n a k i := fun i =>
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (yv_ne hsum ha hk i))
  have hlt : ∀ i, yv n a k i < 1 := fun i => Int.fract_lt_one _
  have h1 : (0 : ℚ) < z := by
    rw [← hz]; unfold sT; rw [Fin.sum_univ_three]; linarith [hpos 0, hpos 1, hpos 2]
  have h2 : (z : ℚ) < 3 := by
    rw [← hz]; unfold sT; rw [Fin.sum_univ_three]; linarith [hlt 0, hlt 1, hlt 2]
  have h1' : 0 < z := by exact_mod_cast h1
  have h2' : z < 3 := by exact_mod_cast h2
  rw [hz]
  rcases (show z = 1 ∨ z = 2 by omega) with h | h <;> simp [h]
theorem gcd_neg' {k : ℤ} (hk : Int.gcd k n = 1) : Int.gcd (-k) n = 1 := by
  rwa [Int.neg_gcd]
theorem fract_neg_raw (m : ℤ) : (((-m : ℤ) : ℚ) / n) = -(((m : ℤ) : ℚ) / n) := by
  push_cast; ring
theorem yv_neg (hsum : ∑ i, a i = n) (ha : ∀ i, 1 ≤ a i) {k : ℤ} (hk : Int.gcd k n = 1)
    (i : Fin 3) : yv n a (-k) i = 1 - yv n a k i := by
  have := yv_ne hsum ha hk i
  unfold yv at this ⊢
  rw [neg_mul, fract_neg_raw, Int.fract_neg this]
end Erdos634.LemmaKStar
end

section
open scoped BigOperators
namespace Erdos634.LemmaF
open Erdos634.LemmaKStar
def Similar (a : Fin 3 → ℕ) (f : Fin 3 → Fin 3 → ℕ) : Prop :=
  ∀ x : ℕ, ∑ j, (if uu a f j = x then 1 else 0 : ℕ) = ∑ i, (if a i = x then 1 else 0 : ℕ)
def HalfIso (n : ℕ) (a : Fin 3 → ℕ) (f : Fin 3 → Fin 3 → ℕ) : Prop :=
  ∃ k l : Fin 3, 2 * a k = n ∧ l ≠ k ∧
    ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ uu a f j₁ = a l ∧ uu a f j₂ = a l
variable {n : ℕ} {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ}
theorem cover : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → ∀ l, l = i ∨ l = j ∨ l = k := by
  decide
theorem sum3 {M : Type*} [AddCommMonoid M] (g : Fin 3 → M) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : ∑ l, g l = g i + g j + g k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [Fin.sum_univ_three] <;> abel
theorem row_ne (hf : ∀ j, f j ≠ 0) (j : Fin 3) : 1 ≤ ∑ i, f j i := by
  by_contra h
  apply hf j
  funext i
  have h0 : ∑ i, f j i = 0 := by omega
  exact (Finset.sum_eq_zero_iff.mp h0) i (Finset.mem_univ _)
theorem mass_eq (f : Fin 3 → Fin 3 → ℕ) : ∑ i, FF f i = ∑ j, ∑ i, f j i := by
  simp only [FF]; exact Finset.sum_comm
theorem mass_ge (hf : ∀ j, f j ≠ 0) : 3 ≤ ∑ i, FF f i := by
  rw [mass_eq, Fin.sum_univ_three]
  have := row_ne hf 0; have := row_ne hf 1; have := row_ne hf 2
  omega
theorem row_count (r : Fin 3 → ℕ) (hr : ∑ i, r i = 1) (x : ℕ) :
    (if ∑ i, r i * a i = x then 1 else 0 : ℕ) = ∑ i, r i * (if a i = x then 1 else 0) := by
  simp only [Fin.sum_univ_three] at *
  have : (r 0 = 1 ∧ r 1 = 0 ∧ r 2 = 0) ∨ (r 0 = 0 ∧ r 1 = 1 ∧ r 2 = 0) ∨
      (r 0 = 0 ∧ r 1 = 0 ∧ r 2 = 1) := by omega
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> simp [h0, h1, h2]
theorem count_mass3 (hf : ∀ j, f j ≠ 0) (hM : ∑ i, FF f i = 3) (x : ℕ) :
    ∑ j, (if uu a f j = x then 1 else 0 : ℕ) = ∑ i, FF f i * (if a i = x then 1 else 0) := by
  rw [mass_eq, Fin.sum_univ_three] at hM
  have h0 := row_ne hf 0; have h1 := row_ne hf 1; have h2 := row_ne hf 2
  have hr : ∑ i, f 0 i = 1 ∧ ∑ i, f 1 i = 1 ∧ ∑ i, f 2 i = 1 := by omega
  have hrow : ∀ j, ∑ i, f j i = 1 := by
    intro j; fin_cases j
    exacts [hr.1, hr.2.1, hr.2.2]
  calc ∑ j, (if uu a f j = x then 1 else 0 : ℕ)
      = ∑ j, ∑ i, f j i * (if a i = x then 1 else 0) :=
        Finset.sum_congr rfl fun j _ => row_count (f j) (hrow j) x
    _ = ∑ i, FF f i * (if a i = x then 1 else 0) := by
        rw [Finset.sum_comm]; simp only [FF, Finset.sum_mul]
theorem right_core (x0 x1 x2 y0 y1 y2 A B : ℕ)
    (hx : x0 + x1 + x2 = 2) (hy : y0 + y1 + y2 = 2)
    (h0 : 1 ≤ x0 + y0) (h1 : 1 ≤ x1 + y1) (h2 : 1 ≤ x2 + y2) :
    (∀ z : ℕ, (if x0 * A + y0 * B = z then 1 else 0 : ℕ) + (if x1 * A + y1 * B = z then 1 else 0)
        + (if x2 * A + y2 * B = z then 1 else 0) =
        (if A = z then 1 else 0) + (if B = z then 1 else 0) + (if A + B = z then 1 else 0)) ∨
    ((x0 * A + y0 * B = B ∧ x1 * A + y1 * B = B) ∨ (x0 * A + y0 * B = B ∧ x2 * A + y2 * B = B) ∨
      (x1 * A + y1 * B = B ∧ x2 * A + y2 * B = B)) ∨
    ((x0 * A + y0 * B = A ∧ x1 * A + y1 * B = A) ∨ (x0 * A + y0 * B = A ∧ x2 * A + y2 * B = A) ∨
      (x1 * A + y1 * B = A ∧ x2 * A + y2 * B = A)) := by
  have : x0 ≤ 2 := by omega
  have : x1 ≤ 2 := by omega
  have : x2 ≤ 2 := by omega
  have : y0 ≤ 2 := by omega
  have : y1 ≤ 2 := by omega
  have : y2 ≤ 2 := by omega
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> try omega
  all_goals (interval_cases y0 <;> interval_cases y1 <;> interval_cases y2 <;> try omega)
  all_goals first
    | (left; intro z; (try simp only [zero_mul, one_mul, zero_add, add_zero]);
        (try (split_ifs <;> omega)); done)
    | (right; left; simp; done)
    | (right; right; simp; done)
theorem right_case {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : 2 * a k = n) (hrel : a i + a j = a k) (hf : ∀ j, f j ≠ 0)
    (hFk : FF f k = 0) (hFi : FF f i = 2) (hFj : FF f j = 2) : Similar a f ∨ HalfIso n a f := by
  have hz : ∀ r, f r k = 0 := fun r =>
    (Finset.sum_eq_zero_iff.mp hFk) r (Finset.mem_univ _)
  have hu : ∀ r, uu a f r = f r i * a i + f r j * a j := by
    intro r
    simp only [uu]
    rw [sum3 (fun l => f r l * a l) hij hik hjk, hz r]
    simp
  have hx : f 0 i + f 1 i + f 2 i = 2 := by
    have := hFi; simp only [FF, Fin.sum_univ_three] at this; exact this
  have hy : f 0 j + f 1 j + f 2 j = 2 := by
    have := hFj; simp only [FF, Fin.sum_univ_three] at this; exact this
  have hne : ∀ r, 1 ≤ f r i + f r j := by
    intro r
    have := row_ne hf r
    rw [sum3 (fun l => f r l) hij hik hjk, hz r] at this
    simpa using this
  rcases right_core (f 0 i) (f 1 i) (f 2 i) (f 0 j) (f 1 j) (f 2 j) (a i) (a j) hx hy
    (hne 0) (hne 1) (hne 2) with h | h | h
  · left
    intro z
    rw [Fin.sum_univ_three, hu 0, hu 1, hu 2, sum3 (fun l => if a l = z then 1 else 0) hij hik hjk,
      ← hrel]
    exact h z
  · right
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨k, j, hk, hjk, 0, 1, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
    · exact ⟨k, j, hk, hjk, 0, 2, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
    · exact ⟨k, j, hk, hjk, 1, 2, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
  · right
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨k, i, hk, hik, 0, 1, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
    · exact ⟨k, i, hk, hik, 0, 2, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
    · exact ⟨k, i, hk, hik, 1, 2, by decide, by rw [hu]; exact h1, by rw [hu]; exact h2⟩
end Erdos634.LemmaF
end

section
namespace Erdos634.Geometry.CaseA.LemmaK1
open Erdos634.Geometry Complex Erdos634.Geometry.CaseA.LemmaV Erdos634.LemmaKStar
theorem exists_sigma {n : ℕ} (hn : 0 < n) {k : ℕ} (hk : k.Coprime (4 * n)) :
    ∃ σ : Kf n →ₐ[ℚ] ℂ,
      σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ k := by
  have hζ := zeta_prim hn
  have hint : IsIntegral ℚ (zeta n) := (hζ.isIntegral (by omega)).tower_top
  have hroot : zeta n ^ k ∈ (minpoly ℚ (zeta n)).aroots ℂ := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ (by omega)]
    have h := (Polynomial.isRoot_cyclotomic_iff_charZero (R := ℂ) (by omega : 0 < 4 * n)).mpr
      (hζ.pow_of_coprime k hk)
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact h
  exact ⟨(IntermediateField.algHomAdjoinIntegralEquiv ℚ hint).symm ⟨_, hroot⟩,
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint _⟩
noncomputable def eS (n j : ℕ) : Kf n :=
  let g := IntermediateField.AdjoinSimple.gen ℚ (zeta n)
  g ^ (3 * n) * g ^ (4 * n - 2 * j) * (g ^ (4 * j) - 1)
theorem coe_eS {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : 2 * j ≤ 4 * n) :
    ((eS n j : Kf n) : ℂ) = ((2 * Real.sin ((j : ℝ) * Real.pi / n) : ℝ) : ℂ) := by
  rw [two_sin_eq hn hj, eS]
  simp
theorem conj_core {n : ℕ} (hn : 0 < n) (k : ℕ) {j : ℕ} (hj : 2 * j ≤ 4 * n) :
    (zeta n ^ k) ^ (4 * n - 2 * j) * ((zeta n ^ k) ^ (4 * j) - 1)
      = I * ((2 * Real.sin (((j * k : ℕ) : ℝ) * Real.pi / n) : ℝ) : ℂ) := by
  set θ : ℝ := ((j * k : ℕ) : ℝ) * Real.pi / n
  have hE : (zeta n ^ k) ^ (2 * j) = Complex.exp ((θ : ℂ) * I) := by
    rw [← pow_mul, show k * (2 * j) = 2 * (j * k) by ring, zeta_pow_two_mul hn]
  have h1 : (zeta n ^ k) ^ (4 * n - 2 * j) * (zeta n ^ k) ^ (2 * j) = 1 := by
    rw [← pow_mul, ← pow_mul, ← pow_add, ← mul_add, Nat.sub_add_cancel hj, pow_mul',
      (zeta_prim hn).pow_eq_one, one_pow]
  rw [hE] at h1
  have h4 : (zeta n ^ k) ^ (4 * j) = Complex.exp ((θ : ℂ) * I) ^ 2 := by
    rw [← hE, ← pow_mul]; ring_nf
  have h2 : Complex.exp (-(θ : ℂ) * I) * Complex.exp ((θ : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp
  have hW : (zeta n ^ k) ^ (4 * n - 2 * j) = Complex.exp (-(θ : ℂ) * I) :=
    mul_right_cancel₀ (Complex.exp_ne_zero _) (h1.trans h2.symm)
  rw [h4, hW]
  push_cast
  rw [Complex.sin]
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination (Complex.exp ((θ : ℂ) * I)) * h2
    + (-(Complex.exp (-(θ : ℂ) * I)) + Complex.exp ((θ : ℂ) * I)) * hI
theorem sigma_eS {n : ℕ} (hn : 0 < n) {k : ℕ} (σ : Kf n →ₐ[ℚ] ℂ)
    (hσ : σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ k) {j : ℕ}
    (hj : 2 * j ≤ 4 * n) :
    σ (eS n j) = ((zeta n ^ k) ^ (3 * n) * I)
      * ((2 * Real.sin (((j * k : ℕ) : ℝ) * Real.pi / n) : ℝ) : ℂ) := by
  simp only [eS, map_mul, map_pow, map_sub, map_one, hσ]
  rw [mul_assoc, conj_core hn k hj]; ring
def Ψ {R : Type*} [CommRing R] (N : ℕ) (c : Fin 3 → ℕ) (s t : Fin 3 → R) : R :=
  (N : R) * s 0 * s 1 * s 2 * t 0 - (∑ k, (c k : R) * s k) ^ 2 * t 1 * t 2
theorem Ψ_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) (c : Fin 3 → ℕ)
    (s t : Fin 3 → R) : f (Ψ N c s t) = Ψ N c (fun i => f (s i)) (fun i => f (t i)) := by
  simp [Ψ, map_sub, map_mul, map_pow, map_sum, map_natCast]
theorem Ψ_smul {R : Type*} [CommRing R] (N : ℕ) (c : Fin 3 → ℕ) (u : R) (s t : Fin 3 → R) :
    Ψ N c (fun i => u * s i) (fun i => u * t i) = u ^ 4 * Ψ N c s t := by
  simp only [Ψ, Fin.sum_univ_three]; ring
theorem conj_star {n : ℕ} (hn : 0 < n) {N : ℕ} (c a b : Fin 3 → ℕ) (ha : ∀ i, a i < n)
    (hb : ∀ i, b i < n)
    (h : (N : ℝ) * Real.sin (a 0 * Real.pi / n) * Real.sin (a 1 * Real.pi / n) *
        Real.sin (a 2 * Real.pi / n) * Real.sin (b 0 * Real.pi / n)
      = (∑ k, (c k : ℝ) * Real.sin (a k * Real.pi / n)) ^ 2 *
        Real.sin (b 1 * Real.pi / n) * Real.sin (b 2 * Real.pi / n))
    {k : ℕ} (hk : k.Coprime (4 * n)) :
    Ψ N c (fun i => 2 * Real.sin (((a i * k : ℕ) : ℝ) * Real.pi / n))
      (fun i => 2 * Real.sin (((b i * k : ℕ) : ℝ) * Real.pi / n)) = 0 := by
  obtain ⟨σ, hσ⟩ := exists_sigma hn hk
  have hle : ∀ {j : ℕ}, j < n → 2 * j ≤ 4 * n := fun h => by omega
  have hR : Ψ N c (fun i => 2 * Real.sin ((a i : ℝ) * Real.pi / n))
      (fun i => 2 * Real.sin ((b i : ℝ) * Real.pi / n)) = 0 := by
    simp only [Ψ, Fin.sum_univ_three] at h ⊢
    linear_combination 16 * h
  have hK : Ψ N c (fun i => eS n (a i)) (fun i => eS n (b i)) = 0 := by
    apply (algebraMap (Kf n) ℂ).injective
    rw [Ψ_map, map_zero]
    have e1 : (fun i => algebraMap (Kf n) ℂ (eS n (a i)))
        = fun i => Complex.ofRealHom (2 * Real.sin ((a i : ℝ) * Real.pi / n)) := by
      funext i; exact coe_eS hn (hle (ha i))
    have e2 : (fun i => algebraMap (Kf n) ℂ (eS n (b i)))
        = fun i => Complex.ofRealHom (2 * Real.sin ((b i : ℝ) * Real.pi / n)) := by
      funext i; exact coe_eS hn (hle (hb i))
    have hm := Ψ_map Complex.ofRealHom N c (fun i => 2 * Real.sin ((a i : ℝ) * Real.pi / n))
      (fun i => 2 * Real.sin ((b i : ℝ) * Real.pi / n))
    rw [e1, e2, ← hm, hR, map_zero]
  have hC := congrArg σ.toRingHom hK
  rw [Ψ_map, map_zero] at hC
  have e3 : (fun i => σ.toRingHom (eS n (a i))) = fun i => ((zeta n ^ k) ^ (3 * n) * I) *
      Complex.ofRealHom (2 * Real.sin (((a i * k : ℕ) : ℝ) * Real.pi / n)) := by
    funext i; exact sigma_eS hn σ hσ (hle (ha i))
  have e4 : (fun i => σ.toRingHom (eS n (b i))) = fun i => ((zeta n ^ k) ^ (3 * n) * I) *
      Complex.ofRealHom (2 * Real.sin (((b i * k : ℕ) : ℝ) * Real.pi / n)) := by
    funext i; exact sigma_eS hn σ hσ (hle (hb i))
  have hm := Ψ_map Complex.ofRealHom N c
    (fun i => 2 * Real.sin (((a i * k : ℕ) : ℝ) * Real.pi / n))
    (fun i => 2 * Real.sin (((b i * k : ℕ) : ℝ) * Real.pi / n))
  rw [e3, e4, Ψ_smul, ← hm] at hC
  have hc : ((zeta n ^ k) ^ (3 * n) * I) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (Complex.exp_ne_zero _))) Complex.I_ne_zero
  have := (mul_eq_zero.mp hC).resolve_left (pow_ne_zero _ hc)
  exact Complex.ofReal_eq_zero.mp this
theorem two_sin_sign {n : ℕ} (hn : 0 < n) (m : ℤ) :
    2 * Real.sin ((m : ℝ) * Real.pi / n)
      = (-1 : ℝ) ^ ⌊((m : ℚ) / n)⌋ * (2 * Real.sin (((Int.fract ((m : ℚ) / n) : ℚ) : ℝ) * Real.pi)) := by
  have hq := Int.fract_add_floor ((m : ℚ) / n)
  have hr : (m : ℝ) / n = ((Int.fract ((m : ℚ) / n) : ℚ) : ℝ) + ((⌊((m : ℚ) / n)⌋ : ℤ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hq
    simp only [Rat.cast_add, Rat.cast_intCast, Rat.cast_div, Rat.cast_natCast] at this
    exact this.symm
  have : (m : ℝ) * Real.pi / n = ((Int.fract ((m : ℚ) / n) : ℚ) : ℝ) * Real.pi
      + ((⌊((m : ℚ) / n)⌋ : ℤ) : ℝ) * Real.pi := by
    rw [mul_div_right_comm, hr]; ring
  rw [this, Real.sin_add_int_mul_pi]; ring
theorem sin_fract_pos {q : ℚ} (h : Int.fract q ≠ 0) :
    0 < 2 * Real.sin (((Int.fract q : ℚ) : ℝ) * Real.pi) := by
  have h0 : (0 : ℝ) < ((Int.fract q : ℚ) : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (Int.fract_nonneg q) (Ne.symm h)
  have h1 : ((Int.fract q : ℚ) : ℝ) < 1 := by exact_mod_cast Int.fract_lt_one q
  have := Real.sin_pos_of_pos_of_lt_pi (mul_pos h0 Real.pi_pos) (by nlinarith [Real.pi_pos])
  linarith
variable {n : ℕ} {a : Fin 3 → ℕ}
theorem yv_congr {k k' : ℤ} (h : (n : ℤ) ∣ k' - k) (hn : 0 < n) (i : Fin 3) :
    yv n a k' i = yv n a k i := by
  obtain ⟨t, ht⟩ := h
  unfold yv
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (((k' * (a i : ℤ) : ℤ) : ℚ) / n) = (((k * (a i : ℤ) : ℤ) : ℚ) / n) + ((t * a i : ℤ) : ℚ) := by
    have hk' : k' = k + n * t := by linarith
    rw [hk']; push_cast; field_simp
  rw [this, Int.fract_add_intCast]
theorem floor_sum (hsum : ∑ i, a i = n) (hn : 0 < n) (k : ℤ) :
    ((∑ i, ⌊(((k * (a i : ℤ) : ℤ) : ℚ) / n)⌋ : ℤ) : ℚ) = k - sT n a k := by
  have h := sum_raw hsum hn k
  unfold sT yv
  have e : ∀ i, ((⌊(((k * (a i : ℤ) : ℤ) : ℚ) / n)⌋ : ℤ) : ℚ)
      = (((k * (a i : ℤ) : ℤ) : ℚ) / n) - Int.fract ((((k * (a i : ℤ) : ℤ) : ℚ) / n)) :=
    fun i => (Int.self_sub_fract _).symm
  rw [Int.cast_sum, Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, h]
theorem exists_lift (hn : 0 < n) {k : ℤ} (hk : Int.gcd k n = 1) :
    ∃ k' : ℕ, k'.Coprime (4 * n) ∧ (n : ℤ) ∣ (k' : ℤ) - k := by
  classical
  set k0 : ℤ := k + 2 * n * (|k| + 1) + (if Even k then (n : ℤ) else 0) with hk0
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hpos : 0 ≤ k0 := by
    have habs := neg_abs_le k
    have : (0 : ℤ) ≤ (if Even k then (n : ℤ) else 0) := by split_ifs <;> omega
    nlinarith [abs_nonneg k, neg_abs_le k, mul_nonneg (sub_nonneg.mpr hn1) (abs_nonneg k)]
  have hodd : Odd k0 := by
    by_cases he : Even k
    · simp only [hk0, he, if_true]
      have hno : Odd (n : ℤ) := by
        rcases Int.even_or_odd (n : ℤ) with h | h
        · exfalso
          have h2k : (2 : ℤ) ∣ k := he.two_dvd
          have h2n : (2 : ℤ) ∣ (n : ℤ) := h.two_dvd
          have := Int.dvd_gcd h2k h2n
          rw [hk] at this; norm_num at this
        · exact h
      have : Even (k + 2 * n * (|k| + 1)) := he.add (by exact ⟨n * (|k| + 1), by ring⟩)
      exact this.add_odd hno
    · simp only [hk0, he, if_false, add_zero]
      rw [Int.not_even_iff_odd] at he
      exact he.add_even ⟨n * (|k| + 1), by ring⟩
  refine ⟨k0.toNat, ?_, ?_⟩
  · have hc : ((k0.toNat : ℕ) : ℤ) = k0 := Int.toNat_of_nonneg hpos
    have hoddN : Odd k0.toNat := by rw [← Int.odd_coe_nat, hc]; exact hodd
    have h4 : k0.toNat.Coprime 4 := by
      have : k0.toNat.Coprime 2 := Nat.coprime_two_right.mpr hoddN
      simpa using Nat.Coprime.pow_right 2 this
    have hcn : k0.toNat.Coprime n := by
      rw [← Nat.isCoprime_iff_coprime, hc]
      have hcop : IsCoprime k (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hk
      have := hcop.add_mul_left_left (2 * (|k| + 1) + (if Even k then 1 else 0))
      convert this using 1 <;> (try rfl) <;> (rw [hk0]; split_ifs <;> ring)
    exact Nat.Coprime.mul_right h4 hcn
  · rw [Int.toNat_of_nonneg hpos, hk0]
    refine ⟨2 * (|k| + 1) + (if Even k then 1 else 0), ?_⟩
    split_ifs <;> ring
theorem sT_eq_of_star {N : ℕ} (hN : N ≠ 0) (hn : 0 < n) (c b : Fin 3 → ℕ)
    (ha1 : ∀ i, 1 ≤ a i) (hsa : ∑ i, a i = n) (hb1 : ∀ i, 1 ≤ b i) (hsb : ∑ i, b i = n)
    (h : (N : ℝ) * Real.sin (a 0 * Real.pi / n) * Real.sin (a 1 * Real.pi / n) *
        Real.sin (a 2 * Real.pi / n) * Real.sin (b 0 * Real.pi / n)
      = (∑ k, (c k : ℝ) * Real.sin (a k * Real.pi / n)) ^ 2 *
        Real.sin (b 1 * Real.pi / n) * Real.sin (b 2 * Real.pi / n))
    {k : ℤ} (hk : Int.gcd k n = 1) : sT n a k = sT n b k := by
  obtain ⟨k', hk'c, hk'd⟩ := exists_lift hn hk
  have hΨ := conj_star hn c a b (fun i => a_lt hsa ha1 i) (fun i => a_lt hsb hb1 i) h hk'c
  have hcast : ∀ j : ℕ, (((j * k' : ℕ) : ℝ)) = (((k' : ℤ) * (j : ℤ) : ℤ) : ℝ) := by
    intro j; push_cast; ring
  set fa : Fin 3 → ℤ := fun i => ⌊((((k' : ℤ) * (a i : ℤ) : ℤ) : ℚ) / n)⌋
  set fb : Fin 3 → ℤ := fun i => ⌊((((k' : ℤ) * (b i : ℤ) : ℤ) : ℚ) / n)⌋
  set pa : Fin 3 → ℝ := fun i => 2 * Real.sin (((yv n a k i : ℚ) : ℝ) * Real.pi)
  set pb : Fin 3 → ℝ := fun i => 2 * Real.sin (((yv n b k i : ℚ) : ℝ) * Real.pi)
  have hSa : ∀ i, 2 * Real.sin ((((a i * k' : ℕ)) : ℝ) * Real.pi / n) = (-1 : ℝ) ^ fa i * pa i := by
    intro i
    rw [hcast, two_sin_sign hn]
    have h' := yv_congr (a := a) hk'd hn i
    unfold yv at h'
    rw [h']
    rfl
  have hSb : ∀ i, 2 * Real.sin ((((b i * k' : ℕ)) : ℝ) * Real.pi / n) = (-1 : ℝ) ^ fb i * pb i := by
    intro i
    rw [hcast, two_sin_sign hn]
    have h' := yv_congr (a := b) hk'd hn i
    unfold yv at h'
    rw [h']
    rfl
  have hpa : ∀ i, 0 < pa i := fun i => sin_fract_pos (yv_ne hsa ha1 hk i)
  have hpb : ∀ i, 0 < pb i := fun i => sin_fract_pos (yv_ne hsb hb1 hk i)
  unfold Ψ at hΨ
  simp only [hSa, hSb] at hΨ
  set Y := ∑ j, (c j : ℝ) * ((-1 : ℝ) ^ fa j * pa j)
  set sgn : ℝ := (-1 : ℝ) ^ (fa 0 + fa 1 + fa 2 + fb 0 + fb 1 + fb 2) with hsgn_def
  have hsgn : sgn * (pa 0 * pa 1 * pa 2 * pb 0 * pb 1 * pb 2) * N
      = (Y * ((-1 : ℝ) ^ fb 1 * pb 1) * ((-1 : ℝ) ^ fb 2 * pb 2)) ^ 2 := by
    have hz : ∀ x y : ℤ, (-1 : ℝ) ^ (x + y) = (-1 : ℝ) ^ x * (-1 : ℝ) ^ y :=
      fun x y => zpow_add₀ (by norm_num) x y
    rw [hsgn_def]
    simp only [hz]
    linear_combination ((-1 : ℝ) ^ fb 1 * pb 1 * ((-1 : ℝ) ^ fb 2 * pb 2)) * hΨ
  have hP : 0 < pa 0 * pa 1 * pa 2 * pb 0 * pb 1 * pb 2 * N := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have := hpa 0; have := hpa 1; have := hpa 2; have := hpb 0; have := hpb 1; have := hpb 2
    positivity
  have hsgn_nn : 0 ≤ sgn := by
    by_contra hneg; push Not at hneg
    have : sgn * (pa 0 * pa 1 * pa 2 * pb 0 * pb 1 * pb 2 * N) < 0 := mul_neg_of_neg_of_pos hneg hP
    nlinarith [sq_nonneg (Y * ((-1 : ℝ) ^ fb 1 * pb 1) * ((-1 : ℝ) ^ fb 2 * pb 2))]
  have hFa := floor_sum hsa hn (k' : ℤ)
  have hFb := floor_sum hsb hn (k' : ℤ)
  have hTa : sT n a (k' : ℤ) = sT n a k := by
    unfold sT; exact Finset.sum_congr rfl (fun i _ => yv_congr hk'd hn i)
  have hTb : sT n b (k' : ℤ) = sT n b k := by
    unfold sT; exact Finset.sum_congr rfl (fun i _ => yv_congr hk'd hn i)
  rw [hTa] at hFa; rw [hTb] at hFb
  rw [Fin.sum_univ_three] at hFa hFb
  rcases sT_12 hsa ha1 hk with h1 | h1 <;> rcases sT_12 hsb hb1 hk with h2 | h2
  · rw [h1, h2]
  · exfalso
    rw [h1] at hFa; rw [h2] at hFb
    have hA : fa 0 + fa 1 + fa 2 = (k' : ℤ) - 1 := by
      have t : ((fa 0 + fa 1 + fa 2 : ℤ) : ℚ) = ((k' : ℤ) : ℚ) - 1 := hFa
      apply Int.cast_injective (α := ℚ); rw [t]; push_cast; ring
    have hB : fb 0 + fb 1 + fb 2 = (k' : ℤ) - 2 := by
      have t : ((fb 0 + fb 1 + fb 2 : ℤ) : ℚ) = ((k' : ℤ) : ℚ) - 2 := hFb
      apply Int.cast_injective (α := ℚ); rw [t]; push_cast; ring
    have hodd : Odd (fa 0 + fa 1 + fa 2 + fb 0 + fb 1 + fb 2) :=
      ⟨(k' : ℤ) - 2, by linarith⟩
    have : sgn = -1 := hodd.neg_one_zpow
    linarith
  · exfalso
    rw [h1] at hFa; rw [h2] at hFb
    have hA : fa 0 + fa 1 + fa 2 = (k' : ℤ) - 2 := by
      have t : ((fa 0 + fa 1 + fa 2 : ℤ) : ℚ) = ((k' : ℤ) : ℚ) - 2 := hFa
      apply Int.cast_injective (α := ℚ); rw [t]; push_cast; ring
    have hB : fb 0 + fb 1 + fb 2 = (k' : ℤ) - 1 := by
      have t : ((fb 0 + fb 1 + fb 2 : ℤ) : ℚ) = ((k' : ℤ) : ℚ) - 1 := hFb
      apply Int.cast_injective (α := ℚ); rw [t]; push_cast; ring
    have hodd : Odd (fa 0 + fa 1 + fa 2 + fb 0 + fb 1 + fb 2) :=
      ⟨(k' : ℤ) - 2, by linarith⟩
    have : sgn = -1 := hodd.neg_one_zpow
    linarith
  · rw [h1, h2]
theorem lemmaK_K1 {N : ℕ} (D : CongruentDissection N) (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ i, D.model.angleAt i = a i * Real.pi / n) (f : Fin 3 → Fin 3 → ℕ)
    (hf : ∀ j, D.target.angleAt j = (uu a f j : ℕ) * Real.pi / n)
    {k : ℤ} (hk : Int.gcd k n = 1) : K1 n a f k := by
  obtain ⟨c, hc⟩ := star D
  have hN : N ≠ 0 := D.toDissection.pos.ne'
  have hA := fun i => nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)
  have hB := fun j => nat_bounds hn (hf j) (angle_pos _ j) (angle_lt_pi _ j)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have sum_of : ∀ (T : Tri) (b : Fin 3 → ℕ), (∀ i, T.angleAt i = b i * Real.pi / n) →
      ∑ i, b i = n := by
    intro T b hb
    have hs := T.angleAt_sum
    rw [hb 0, hb 1, hb 2] at hs
    have hnn : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
    have key : (((b 0 + b 1 + b 2 : ℕ) : ℝ) - n) * (Real.pi / n) = 0 := by
      push_cast; linear_combination hs - hnn
    have hpn : Real.pi / n ≠ 0 := div_ne_zero Real.pi_ne_zero hn'
    have := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hpn)
    rw [Fin.sum_univ_three]; exact_mod_cast this
  have hsa := sum_of _ a ha
  have hsb := sum_of _ (uu a f) hf
  simp only [ha, hf] at hc
  exact sT_eq_of_star hN hn c (uu a f) (fun i => (hA i).1) hsa (fun j => (hB j).1) hsb hc hk
end Erdos634.Geometry.CaseA.LemmaK1
end

section
open Complex
namespace Erdos634.KConj
open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.Geometry.CaseA.LemmaK1
open Erdos634.Geometry.A1Field
variable {n : ℕ}
theorem coprime_of (m n : ℕ) (hm : m % 2 = 1) (hmn : m.Coprime n) : m.Coprime (4 * n) := by
  have h2 : m.Coprime 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
  have h4 : m.Coprime 4 := by simpa using Nat.Coprime.pow_right 2 h2
  exact Nat.Coprime.mul_right h4 hmn
theorem exists_m (hn : 0 < n) {k : ℤ} (hk : Int.gcd k n = 1) :
    ∃ m : ℕ, m.Coprime (4 * n) ∧ m % 4 = 1 ∧ ((n : ℤ) ∣ (m : ℤ) - k ∨ (n : ℤ) ∣ (m : ℤ) + k) := by
  obtain ⟨k', hc, hd⟩ := exists_lift hn hk
  have hc4 : k'.Coprime 4 := Nat.Coprime.coprime_mul_right_right hc
  have hcn : k'.Coprime n := Nat.Coprime.coprime_mul_left_right hc
  have hodd : k' % 2 = 1 := by
    by_contra h
    have : 2 ∣ Nat.gcd k' 4 := Nat.dvd_gcd (by omega) (by norm_num)
    rw [hc4] at this; norm_num at this
  by_cases h1 : k' % 4 = 1
  · exact ⟨k', hc, h1, Or.inl hd⟩
  · have h3 : k' % 4 = 3 := by omega
    by_cases hn2 : n % 2 = 1
    · refine ⟨k' + 2 * n, coprime_of _ _ (by omega)
        ((Nat.coprime_add_mul_right_left k' n 2).mpr hcn), by omega, Or.inl ?_⟩
      obtain ⟨t, ht⟩ := hd
      exact ⟨t + 2, by push_cast; linarith⟩
    · by_cases hn4 : n % 4 = 2
      · refine ⟨k' + 1 * n, coprime_of _ _ (by omega)
          ((Nat.coprime_add_mul_right_left k' n 1).mpr hcn), by omega, Or.inl ?_⟩
        obtain ⟨t, ht⟩ := hd
        exact ⟨t + 1, by push_cast; linarith⟩
      · have h4n : (4 : ℤ) ∣ n := by
          have : 4 ∣ n := by omega
          exact_mod_cast this
        obtain ⟨k'', hc', hd'⟩ := exists_lift hn (LemmaKStar.gcd_neg' hk)
        have hsum : (n : ℤ) ∣ (k'' : ℤ) + k' := by
          have := dvd_add hd' hd
          rwa [show (k'' : ℤ) - -k + ((k' : ℤ) - k) = (k'' : ℤ) + k' by ring] at this
        have h4 : (4 : ℤ) ∣ (k'' : ℤ) + k' := dvd_trans h4n hsum
        refine ⟨k'', hc', by omega, Or.inr ?_⟩
        convert hd' using 1; ring
theorem zeta_mem' : zeta n ∈ Kf n := IntermediateField.mem_adjoin_simple_self ℚ _
theorem conj_zeta : (starRingEnd ℂ) (zeta n) = (zeta n)⁻¹ := by
  rw [zeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp [map_div₀, Complex.conj_ofReal, map_ofNat]
  ring
noncomputable def cQ : ℂ →ₐ[ℚ] ℂ := (Complex.conjAe.toAlgHom).restrictScalars ℚ
theorem cQ_apply (z : ℂ) : cQ z = (starRingEnd ℂ) z := rfl
theorem conj_mem {x : ℂ} (hx : x ∈ Kf n) : (starRingEnd ℂ) x ∈ Kf n := by
  have hmap : (Kf n).map cQ ≤ Kf n := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_simple_le_iff,
      cQ_apply, conj_zeta]
    exact inv_mem zeta_mem'
  exact hmap ⟨x, hx, rfl⟩
noncomputable def conjK (n : ℕ) : Kf n →ₐ[ℚ] Kf n where
  toFun x := ⟨(starRingEnd ℂ) (x : ℂ), conj_mem x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' q := by ext; simp
theorem coe_conjK (x : Kf n) : ((conjK n x : Kf n) : ℂ) = (starRingEnd ℂ) (x : ℂ) := rfl
theorem I_mem (hn : 0 < n) : I ∈ Kf n := by rw [← zeta_pow_n hn]; exact pow_mem zeta_mem' n
theorem exp_eq_zeta (hn : 0 < n) (j : ℤ) :
    Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) = zeta n ^ (2 * j) := by
  rw [zeta, ← Complex.exp_int_mul]
  congr 1
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast; field_simp; ring
section Sigma
variable {m : ℕ} (σ : Kf n →ₐ[ℚ] ℂ)
  (hσ : σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ m)
include hσ
theorem sigma_conj (x : Kf n) : σ (conjK n x) = (starRingEnd ℂ) (σ x) := by
  have h : σ.comp (conjK n) = cQ.comp σ := by
    apply IntermediateField.adjoin_algHom_ext ℚ
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have e1 : conjK n ⟨zeta n, zeta_mem'⟩ = (IntermediateField.AdjoinSimple.gen ℚ (zeta n))⁻¹ := by
      ext; rw [coe_conjK]
      show (starRingEnd ℂ) (zeta n) = _
      rw [conj_zeta, IntermediateField.coe_inv, IntermediateField.AdjoinSimple.coe_gen]
    have e2 : (⟨zeta n, zeta_mem'⟩ : Kf n) = IntermediateField.AdjoinSimple.gen ℚ (zeta n) := rfl
    show σ (conjK n ⟨zeta n, zeta_mem'⟩) = cQ (σ ⟨zeta n, zeta_mem'⟩)
    rw [e1, map_inv₀, e2, hσ, cQ_apply, map_pow, conj_zeta, inv_pow]
  exact congrArg (fun φ : Kf n →ₐ[ℚ] ℂ => φ x) h
theorem sigma_real (x : Kf n) (hx : (starRingEnd ℂ) (x : ℂ) = x) :
    (starRingEnd ℂ) (σ x) = σ x := by
  rw [← sigma_conj σ hσ]
  congr 1
  ext; rw [coe_conjK, hx]
theorem sigma_I (hn : 0 < n) (hm4 : m % 4 = 1) : σ ⟨I, I_mem hn⟩ = I := by
  have e : (⟨I, I_mem hn⟩ : Kf n) = (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) ^ n := by
    ext; simp [zeta_pow_n hn]
  rw [e, map_pow, hσ, ← pow_mul, mul_comm, pow_mul, zeta_pow_n hn]
  obtain ⟨q, hq⟩ : ∃ q, m = 4 * q + 1 := ⟨m / 4, by omega⟩
  rw [hq, pow_succ, pow_mul, Complex.I_pow_four, one_pow, one_mul]
theorem sigma_exp (hn : 0 < n) (j : ℤ) :
    σ ⟨Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I), exp_int_mem hn j⟩
      = Complex.exp ((((j * m : ℤ) : ℝ) * Real.pi / n : ℝ) * I) := by
  have e : (⟨Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I), exp_int_mem hn j⟩ : Kf n)
      = (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) ^ (2 * j) := by
    ext
    show Complex.exp (((j : ℝ) * Real.pi / n : ℝ) * I) = _
    rw [exp_eq_zeta hn]
    exact (map_zpow₀ ((Kf n).val) (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) (2 * j)).symm
  rw [e, map_zpow₀, hσ, exp_eq_zeta hn, ← zpow_natCast, ← zpow_mul]
  congr 1; ring
end Sigma
end Erdos634.KConj
end

section
open MeasureTheory Set
namespace Erdos634.KMoment
open Erdos634.Geometry Erdos634.AreaDet
def qstd (i j : ℕ) : ℚ :=
  ∑ l ∈ Finset.range (j + 2), ((j + 1).choose l : ℚ) * (-1) ^ l / (((j : ℚ) + 1) * ((i : ℚ) + l + 1))
noncomputable def E2 : Plane ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
theorem E2_mp : MeasurePreserving E2 volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)
theorem E2_apply (x : Plane) : E2 x = (x 0, x 1) := rfl
def Tset : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}
theorem stdCarrier_eq : stdCarrier = E2 ⁻¹' Tset := by
  ext x; rw [mem_stdCarrier_iff]; rfl
theorem Tset_closed : IsClosed Tset := by
  apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
  apply IsClosed.inter (isClosed_le continuous_const continuous_snd)
  exact isClosed_le (continuous_fst.add continuous_snd) continuous_const
theorem Tset_compact : IsCompact Tset := by
  apply ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))).of_isClosed_subset Tset_closed
  rintro ⟨x, y⟩ ⟨h1, h2, h3⟩
  simp only at h1 h2 h3
  exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩⟩
theorem inner_int (i j : ℕ) (x : ℝ) :
    ∫ y, Tset.indicator (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j) (x, y)
      = (Icc (0 : ℝ) 1).indicator (fun x => x ^ i * ((1 - x) ^ (j + 1) / (j + 1))) x := by
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hx]
    have e : (fun y => Tset.indicator (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j) (x, y))
        = (Icc (0 : ℝ) (1 - x)).indicator (fun y => x ^ i * y ^ j) := by
      funext y
      by_cases hy : y ∈ Icc (0 : ℝ) (1 - x)
      · rw [indicator_of_mem hy, indicator_of_mem]
        exact ⟨hx.1, hy.1, by linarith [hy.2]⟩
      · rw [indicator_of_notMem hy, indicator_of_notMem]
        rintro ⟨_, h2, h3⟩; exact hy ⟨h2, by simp only at h3; linarith⟩
    rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [hx.2]), intervalIntegral.integral_const_mul,
      integral_pow]
    congr 1; ring
  · rw [indicator_of_notMem hx]
    have e : (fun y => Tset.indicator (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j) (x, y)) = fun _ => 0 := by
      funext y
      rw [indicator_of_notMem]
      rintro ⟨h1, h2, h3⟩; exact hx ⟨h1, by simp only at h2 h3; linarith⟩
    rw [e, integral_zero]
theorem outer_int (i j : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ i * ((1 - x) ^ (j + 1) / (j + 1)) = (qstd i j : ℝ) := by
  have hexp : ∀ x : ℝ, x ^ i * ((1 - x) ^ (j + 1) / (j + 1))
      = ∑ l ∈ Finset.range (j + 2),
          (((j + 1).choose l : ℝ) * (-1) ^ l / ((j : ℝ) + 1)) * x ^ (i + l) := by
    intro x
    have hb : (1 - x) ^ (j + 1) = ∑ l ∈ Finset.range (j + 1 + 1),
        (-x) ^ l * 1 ^ (j + 1 - l) * ((j + 1).choose l : ℝ) := by
      rw [← add_pow]; ring
    rw [hb, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [neg_pow, one_pow, pow_add]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum (fun l _ => by
    exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _)]
  unfold qstd; push_cast
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  have h1 : (j : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (i : ℝ) + l + 1 ≠ 0 := by positivity
  field_simp
  simp
theorem integral_std (i j : ℕ) :
    ∫ x in stdCarrier, (x 0) ^ i * (x 1) ^ j = (qstd i j : ℝ) := by
  rw [stdCarrier_eq]
  have h := E2_mp.setIntegral_preimage_emb E2.measurableEmbedding
    (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j) Tset
  simp only [E2_apply] at h
  rw [h, ← integral_indicator Tset_closed.measurableSet]
  have hint : Integrable (Tset.indicator (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j)) volume := by
    rw [integrable_indicator_iff Tset_closed.measurableSet]
    exact ((continuous_fst.pow i).mul (continuous_snd.pow j)).continuousOn.integrableOn_compact
      Tset_compact
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  simp_rw [inner_int]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, outer_int]
end Erdos634.KMoment
end

section
open MeasureTheory Set MvPolynomial
namespace Erdos634.KMoment
open Erdos634.Geometry Erdos634.AreaDet
section Alg
variable {R S : Type*} [Field R] [CharZero R] [Field S] [CharZero S]
noncomputable def Lf (c : Fin 3 → Fin 2 → R) (v : Fin 2) : MvPolynomial (Fin 2) R :=
  C (c 0 v) + X 0 * C (c 1 v - c 0 v) + X 1 * C (c 2 v - c 0 v)
noncomputable def Qm (c : Fin 3 → Fin 2 → R) (i j : ℕ) : MvPolynomial (Fin 2) R :=
  Lf c 0 ^ i * Lf c 1 ^ j
noncomputable def Λ (Q : MvPolynomial (Fin 2) R) : R :=
  ∑ m ∈ Q.support, coeff m Q * ((qstd (m 0) (m 1) : ℚ) : R)
def detc (c : Fin 3 → Fin 2 → R) : R :=
  (c 1 0 - c 0 0) * (c 2 1 - c 0 1) - (c 1 1 - c 0 1) * (c 2 0 - c 0 0)
theorem map_Qm (φ : R →+* S) (c : Fin 3 → Fin 2 → R) (i j : ℕ) :
    map φ (Qm c i j) = Qm (fun k v => φ (c k v)) i j := by
  simp [Qm, Lf, map_mul, map_pow, map_add, map_C, map_X, map_sub]
theorem map_Λ (φ : R →+* S) (Q : MvPolynomial (Fin 2) R) : φ (Λ Q) = Λ (map φ Q) := by
  unfold Λ
  rw [support_map_of_injective Q φ.injective, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_mul, coeff_map, map_ratCast]
theorem map_detc (φ : R →+* S) (c : Fin 3 → Fin 2 → R) :
    φ (detc c) = detc (fun k v => φ (c k v)) := by
  simp [detc, map_sub, map_mul]
end Alg
def cT (T : Tri) : Fin 3 → Fin 2 → ℝ := fun k v => T.pts k v
theorem detc_cT (T : Tri) : detc (cT T) = T.det := by
  simp [detc, cT, Tri.det]
theorem integral_std_poly (Q : MvPolynomial (Fin 2) ℝ) :
    ∫ x in stdCarrier, eval (fun v => x v) Q = Λ Q := by
  simp_rw [eval_eq']
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    simp_rw [Fin.prod_univ_two]
    rw [integral_const_mul, integral_std]
  · intro m _
    apply ContinuousOn.integrableOn_compact (isCompact_stdCarrier)
    apply Continuous.continuousOn
    apply continuous_const.mul
    apply continuous_finsetProd
    intro v _
    exact ((PiLp.continuous_apply 2 _ v)).pow _
theorem edgeMap_apply' (T : Tri) (x : Plane) :
    edgeMap T x = x 0 • (T.pts 1 - T.pts 0) + x 1 • (T.pts 2 - T.pts 0) := by
  rw [edgeMap, Module.Basis.constr_apply, Finsupp.sum_fintype _ _ (fun i => by simp),
    Fin.sum_univ_two, pb_repr, pb_repr]
  rfl
theorem place_coord (T : Tri) (x : Plane) (v : Fin 2) :
    (T.pts 0 + edgeMap T x) v = eval (fun w => x w) (Lf (cT T) v) := by
  rw [edgeMap_apply']
  simp [Lf, cT]
  ring
theorem integral_tri (T : Tri) (i j : ℕ) :
    ∫ x in T.carrier, (x 0) ^ i * (x 1) ^ j = |T.det| * Λ (Qm (cT T) i j) := by
  set L := (edgeMap T).toContinuousLinearMap with hL
  set f : Plane → Plane := fun x => T.pts 0 + L x with hf
  have himg : f '' stdCarrier = T.carrier := by
    rw [← placeMap_stdCarrier T]
    congr 1
  have hdet0 : LinearMap.det (edgeMap T) = T.det := by
    have := detTri_eq T
    rw [detTri] at this
    rw [this, Tri.det]; ring
  have hdet : L.det = T.det := by rw [hL, LinearMap.det_toContinuousLinearMap, hdet0]
  have hne : LinearMap.det (edgeMap T) ≠ 0 := by rw [hdet0]; exact T.det_ne_zero
  have hinj : Function.Injective L := fun x y h =>
    (LinearMap.equivOfDetNeZero _ hne).injective h
  rw [← himg, integral_image_eq_integral_abs_det_fderiv_smul volume (f' := fun _ => L)
    isCompact_stdCarrier.measurableSet
    (fun x _ => (L.hasFDerivAt.const_add (T.pts 0)).hasFDerivWithinAt)
    (fun x _ y _ h => hinj (add_left_cancel h))]
  simp only [hdet, smul_eq_mul]
  rw [integral_const_mul, ← integral_std_poly]
  congr 1
  refine setIntegral_congr_fun isCompact_stdCarrier.measurableSet (fun x _ => ?_)
  simp only [hL, LinearMap.coe_toContinuousLinearMap']
  rw [place_coord, place_coord, Qm, map_mul, map_pow, map_pow]
end Erdos634.KMoment
end

section
open MeasureTheory Set MvPolynomial
namespace Erdos634.KMoment
open Erdos634.Geometry
variable {ι : Type*} [Fintype ι] {U : ι → Set Plane} (c : ι → ℝ)
noncomputable def comb (U : ι → Set Plane) (x : Plane) : ℝ := ∑ k, c k * (U k).indicator 1 x
theorem mul_comb (h : Plane → ℝ) (x : Plane) :
    h x * comb c U x = ∑ k, c k * (U k).indicator h x := by
  rw [comb, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hx : x ∈ U k
  · simp [indicator_of_mem hx]; ring
  · simp [indicator_of_notMem hx]
theorem integrable_mul_comb (hU : ∀ k, IsCompact (U k)) {h : Plane → ℝ} (hh : Continuous h) :
    Integrable (fun x => h x * comb c U x) := by
  simp_rw [mul_comb]
  refine integrable_finsetSum _ (fun k _ => ?_)
  exact ((integrable_indicator_iff (hU k).measurableSet).mpr
    (hh.continuousOn.integrableOn_compact (hU k))).const_mul _
theorem integral_mul_comb (hU : ∀ k, IsCompact (U k)) {h : Plane → ℝ} (hh : Continuous h) :
    ∫ x, h x * comb c U x = ∑ k, c k * ∫ x in U k, h x := by
  simp_rw [mul_comb]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [integral_const_mul, integral_indicator (hU k).measurableSet]
  · intro k _
    exact ((integrable_indicator_iff (hU k).measurableSet).mpr
      (hh.continuousOn.integrableOn_compact (hU k))).const_mul _
theorem cont_coord (v : Fin 2) : Continuous (fun x : Plane => x v) := PiLp.continuous_apply 2 _ v
theorem cont_eval (P : MvPolynomial (Fin 2) ℝ) : Continuous (fun x : Plane => eval (fun v => x v) P) := by
  simp_rw [eval_eq']
  exact continuous_finsetSum _ (fun m _ => continuous_const.mul
    (continuous_finsetProd _ (fun v _ => (cont_coord v).pow _)))
theorem poly_moment (hU : ∀ k, IsCompact (U k))
    (hmom : ∀ i j : ℕ, ∑ k, c k * ∫ x in U k, (x 0) ^ i * (x 1) ^ j = 0)
    (P : MvPolynomial (Fin 2) ℝ) : ∫ x, eval (fun v => x v) P * comb c U x = 0 := by
  rw [integral_mul_comb c hU (cont_eval P)]
  simp_rw [eval_eq', Fin.prod_univ_two]
  have : ∀ k, ∫ x in U k, ∑ m ∈ P.support, coeff m P * ((x 0) ^ m 0 * (x 1) ^ m 1)
      = ∑ m ∈ P.support, coeff m P * ∫ x in U k, (x 0) ^ m 0 * (x 1) ^ m 1 := by
    intro k
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul]
    · intro m _
      exact (continuous_const.mul (((cont_coord 0).pow _).mul ((cont_coord 1).pow _))).continuousOn
        |>.integrableOn_compact (hU k)
  simp_rw [this, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  have h := hmom (m 0) (m 1)
  calc ∑ k, c k * (coeff m P * ∫ x in U k, (x 0) ^ m 0 * (x 1) ^ m 1)
      = coeff m P * ∑ k, c k * ∫ x in U k, (x 0) ^ m 0 * (x 1) ^ m 1 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => by ring)
    _ = 0 := by rw [h, mul_zero]
section SW
variable (R : ℝ)
abbrev Kb := Metric.closedBall (0 : Plane) R
instance : CompactSpace (Kb R) := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 R)
def crd (v : Fin 2) : C(Kb R, ℝ) := ⟨fun x => (x : Plane) v, (cont_coord v).comp continuous_subtype_val⟩
noncomputable def polyA : Subalgebra ℝ C(Kb R, ℝ) := (aeval (crd R)).range
theorem aeval_apply (P : MvPolynomial (Fin 2) ℝ) (x : Kb R) :
    (aeval (crd R) P) x = eval (fun v => (x : Plane) v) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [_root_.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp, crd]
theorem polyA_sep : (polyA R).SeparatesPoints := by
  intro x y hxy
  have : ∃ v, (x : Plane) v ≠ (y : Plane) v := by
    by_contra h; push Not at h
    exact hxy (Subtype.ext (PiLp.ext h))
  obtain ⟨v, hv⟩ := this
  exact ⟨crd R v, ⟨crd R v, ⟨X v, by simp⟩, rfl⟩, hv⟩
end SW
theorem ae_zero_of_moments (hU : ∀ k, IsCompact (U k))
    (hmom : ∀ i j : ℕ, ∑ k, c k * ∫ x in U k, (x 0) ^ i * (x 1) ^ j = 0) :
    ∀ᵐ x, comb c U x = 0 := by
  have hint : Integrable (comb c U) := by
    have := integrable_mul_comb c hU (h := fun _ => (1 : ℝ)) continuous_const
    simpa using this
  obtain ⟨R, hR⟩ := (isCompact_iUnion hU).isBounded.subset_closedBall (0 : Plane)
  have hsupp : ∀ x, x ∉ Metric.closedBall (0 : Plane) R → comb c U x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [indicator_of_notMem (fun h => hx (hR (mem_iUnion.mpr ⟨k, h⟩))), mul_zero]
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hint.locallyIntegrable
  intro g hg _
  have hgc : Continuous g := hg.continuous
  simp only [smul_eq_mul]
  set C := ∫ x, |comb c U x|
  have key : ∀ ε > 0, |∫ x, g x * comb c U x| ≤ ε * C := by
    intro ε hε
    let gK : C(Kb R, ℝ) := ⟨fun x => g x, hgc.comp continuous_subtype_val⟩
    obtain ⟨⟨p, hpA⟩, hp⟩ :=
      ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints (polyA R)
        (polyA_sep R) gK ε hε
    obtain ⟨P, rfl⟩ := hpA
    have hP := poly_moment c hU hmom P
    have hdiff : ∫ x, g x * comb c U x
        = ∫ x, (g x - eval (fun v => x v) P) * comb c U x := by
      simp_rw [sub_mul]
      rw [integral_sub (integrable_mul_comb c hU hgc) (integrable_mul_comb c hU (cont_eval P)), hP,
        sub_zero]
    rw [hdiff, ← Real.norm_eq_abs]
    have hb : ∀ x, ‖(g x - eval (fun v => x v) P) * comb c U x‖ ≤ ε * |comb c U x| := by
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : Plane) R
      · rw [norm_mul, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        have h1 := ContinuousMap.norm_coe_le_norm ((aeval (crd R)) P - gK) ⟨x, hx⟩
        rw [ContinuousMap.sub_apply, aeval_apply, Real.norm_eq_abs] at h1
        have h2 : |g x - eval (fun v => x v) P| = |eval (fun v => x v) P - g x| := abs_sub_comm _ _
        rw [h2]; exact (h1.trans hp.le)
      · rw [hsupp x hx]; simp
    calc ‖∫ x, (g x - eval (fun v => x v) P) * comb c U x‖
        ≤ ∫ x, ε * |comb c U x| :=
          norm_integral_le_of_norm_le (hint.abs.const_mul ε) (Filter.Eventually.of_forall hb)
      _ = ε * C := integral_const_mul _ _
  have hC : 0 ≤ C := integral_nonneg (fun x => abs_nonneg _)
  have : |∫ x, g x * comb c U x| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    have := key (δ / (C + 1)) (div_pos hδ (by linarith))
    calc _ ≤ δ / (C + 1) * C := this
      _ ≤ 0 + δ := by
        rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
  exact abs_nonpos_iff.mp this
end Erdos634.KMoment
end

section
open Complex MeasureTheory Set
namespace Erdos634.KConj
open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.KMoment Erdos634.CertCoord
variable {n m : ℕ} (hn : 0 < n) (σ : Kf n →ₐ[ℚ] ℂ)
  (hσ : σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ m) (hm4 : m % 4 = 1)
noncomputable def reK (x : Kf n) : Kf n := (x + conjK n x) / 2
noncomputable def imK (x : Kf n) : Kf n := (x - conjK n x) / (2 * ⟨I, I_mem hn⟩)
theorem coe_reK (x : Kf n) : ((reK x : Kf n) : ℂ) = (((x : ℂ).re : ℝ) : ℂ) := by
  rw [Complex.re_eq_add_conj, reK]; simp [coe_conjK]; norm_cast
theorem coe_imK (x : Kf n) : ((imK hn x : Kf n) : ℂ) = (((x : ℂ).im : ℝ) : ℂ) := by
  rw [Complex.im_eq_sub_conj, imK]; simp [coe_conjK]; norm_cast
include hσ in
theorem sigma_reK (x : Kf n) : σ (reK x) = (((σ x).re : ℝ) : ℂ) := by
  rw [reK, map_div₀, map_add, sigma_conj σ hσ, Complex.re_eq_add_conj, map_ofNat]
include hσ hm4 in
theorem sigma_imK (x : Kf n) : σ (imK hn x) = (((σ x).im : ℝ) : ℂ) := by
  rw [imK, map_div₀, map_sub, sigma_conj σ hσ, map_mul, sigma_I σ hσ hn hm4,
    Complex.im_eq_sub_conj, map_ofNat]
noncomputable def cK (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) : Fin 3 → Fin 2 → Kf n :=
  fun k => ![reK ⟨toC (T.pts k), hT k⟩, imK hn ⟨toC (T.pts k), hT k⟩]
theorem alg_cK (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) (v : Fin 2) :
    algebraMap (Kf n) ℂ (cK hn T hT k v) = ((cT T k v : ℝ) : ℂ) := by
  fin_cases v
  · show ((reK _ : Kf n) : ℂ) = _; rw [coe_reK]; simp [toC_re, cT]
  · show ((imK hn _ : Kf n) : ℂ) = _; rw [coe_imK]; simp [toC_im, cT]
theorem detc_cK (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) :
    algebraMap (Kf n) ℂ (detc (cK hn T hT)) = ((T.det : ℝ) : ℂ) := by
  rw [map_detc, ← detc_cT]
  simp only [alg_cK]
  rw [← Complex.ofRealHom_eq_coe, map_detc]; rfl
theorem alg_Λ (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (i j : ℕ) :
    algebraMap (Kf n) ℂ (Λ (Qm (cK hn T hT) i j)) = ((Λ (Qm (cT T) i j) : ℝ) : ℂ) := by
  rw [map_Λ, map_Qm]
  have h2 := map_Λ Complex.ofRealHom (Qm (cT T) i j)
  rw [map_Qm] at h2
  rw [Complex.ofRealHom_eq_coe] at h2
  rw [h2]
  congr 2
  funext k v
  exact alg_cK hn T hT k v
noncomputable def sw (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) : ℂ :=
  σ ⟨toC (T.pts k), hT k⟩
theorem dissection_integral_sum {N : ℕ} (D : Dissection N) {h : Plane → ℝ} (hh : Continuous h) :
    ∑ i, ∫ x in (D.tile i).carrier, h x = ∫ x in D.target.carrier, h x := by
  rw [← D.covers, integral_iUnion_ae (fun i => (D.tile i).nullMeasurableSet)
    (fun i j hij => D.aedisjoint hij), tsum_fintype]
  rw [D.covers]
  exact hh.continuousOn.integrableOn_compact D.target.isCompact
theorem vol_pos_of (T : Tri) {V : Set Plane} (hV : IsOpen V) {x : Plane} (hx : x ∈ V)
    (hxT : x ∈ T.carrier) : 0 < volume (V ∩ interior T.carrier) := by
  have hcl : x ∈ closure (interior T.carrier) := by
    rw [T.convex.closure_interior_eq_closure_of_nonempty_interior T.interior_nonempty]
    exact subset_closure hxT
  obtain ⟨y, hyV, hyI⟩ := mem_closure_iff.mp hcl V hV hx
  exact (hV.inter isOpen_interior).measure_pos volume ⟨y, hyV, hyI⟩
noncomputable def dissectionOfAe (tile : Fin N → Tri) (target : Tri) (hN : 0 < N)
    (h : ∀ᵐ x, ∑ i, (tile i).carrier.indicator (1 : Plane → ℝ) x
      = target.carrier.indicator 1 x) : Dissection N where
  target := target
  tile := tile
  covers := by
    have hbad : volume {x | ¬ (∑ i, (tile i).carrier.indicator (1 : Plane → ℝ) x
        = target.carrier.indicator 1 x)} = 0 := ae_iff.mp h
    have hnn : ∀ x i, 0 ≤ (tile i).carrier.indicator (1 : Plane → ℝ) x := fun x i =>
      indicator_nonneg (fun _ _ => zero_le_one) x
    apply Subset.antisymm
    · intro x hx
      by_contra hxT
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      have hpos := vol_pos_of (tile i) target.isCompact.isClosed.isOpen_compl hxT hi
      apply (ne_of_gt hpos)
      refine measure_mono_null (fun y hy => ?_) hbad
      intro heq
      rw [indicator_of_notMem hy.1] at heq
      have h1 : (tile i).carrier.indicator (1 : Plane → ℝ) y = 1 :=
        indicator_of_mem (interior_subset hy.2) _
      have := Finset.single_le_sum (fun j _ => hnn y j) (Finset.mem_univ i)
      linarith
    · intro x hx
      by_contra hxU
      have hcl : IsClosed (⋃ i, (tile i).carrier) :=
        isClosed_iUnion_of_finite (fun i => (tile i).isCompact.isClosed)
      have hpos := vol_pos_of target hcl.isOpen_compl hxU hx
      apply (ne_of_gt hpos)
      refine measure_mono_null (fun y hy => ?_) hbad
      intro heq
      rw [indicator_of_mem (interior_subset hy.2)] at heq
      have : ∑ i, (tile i).carrier.indicator (1 : Plane → ℝ) y = 0 := by
        refine Finset.sum_eq_zero (fun i _ => indicator_of_notMem ?_ _)
        exact fun hi => hy.1 (mem_iUnion.mpr ⟨i, hi⟩)
      rw [this] at heq; norm_num at heq
  interiors_disjoint := by
    intro i j hij
    rw [Set.disjoint_iff]
    rintro x ⟨hxi, hxj⟩
    have hbad : volume {x | ¬ (∑ i, (tile i).carrier.indicator (1 : Plane → ℝ) x
        = target.carrier.indicator 1 x)} = 0 := ae_iff.mp h
    have hW : IsOpen (interior (tile i).carrier ∩ interior (tile j).carrier) :=
      isOpen_interior.inter isOpen_interior
    have hpos : 0 < volume (interior (tile i).carrier ∩ interior (tile j).carrier) :=
      hW.measure_pos volume ⟨x, hxi, hxj⟩
    apply (ne_of_gt hpos)
    refine measure_mono_null (fun y hy => ?_) hbad
    intro heq
    have hi1 : (tile i).carrier.indicator (1 : Plane → ℝ) y = 1 :=
      indicator_of_mem (interior_subset hy.1) _
    have hj1 : (tile j).carrier.indicator (1 : Plane → ℝ) y = 1 :=
      indicator_of_mem (interior_subset hy.2) _
    have hle : (tile i).carrier.indicator (1 : Plane → ℝ) y
        + (tile j).carrier.indicator (1 : Plane → ℝ) y
        ≤ ∑ k, (tile k).carrier.indicator (1 : Plane → ℝ) y := by
      rw [← Finset.sum_pair (f := fun k => (tile k).carrier.indicator (1 : Plane → ℝ) y) hij]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => indicator_nonneg (fun _ _ => zero_le_one) y)
    have hT1 : target.carrier.indicator (1 : Plane → ℝ) y ≤ 1 := by
      by_cases hy' : y ∈ target.carrier
      · rw [indicator_of_mem hy']; rfl
      · rw [indicator_of_notMem hy']; norm_num
    linarith
section Phi
include hn hσ hm4
theorem sigma_cK (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) :
    σ (cK hn T hT k 0) = (((sw σ T hT k).re : ℝ) : ℂ) ∧
    σ (cK hn T hT k 1) = (((sw σ T hT k).im : ℝ) : ℂ) := by
  exact ⟨sigma_reK σ hσ _, sigma_imK hn σ hσ hm4 _⟩
theorem phi_det_eq (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) :
    ((det3 (sw σ T hT 0).re (sw σ T hT 0).im (sw σ T hT 1).re (sw σ T hT 1).im
      (sw σ T hT 2).re (sw σ T hT 2).im : ℝ) : ℂ) = σ (detc (cK hn T hT)) := by
  rw [show σ (detc (cK hn T hT)) = σ.toRingHom (detc (cK hn T hT)) from rfl, map_detc]
  have h := fun k => sigma_cK hn σ hσ hm4 T hT k
  simp only [detc, det3]
  change _ = (σ (cK hn T hT 1 0) - σ (cK hn T hT 0 0)) * (σ (cK hn T hT 2 1) - σ (cK hn T hT 0 1))
    - (σ (cK hn T hT 1 1) - σ (cK hn T hT 0 1)) * (σ (cK hn T hT 2 0) - σ (cK hn T hT 0 0))
  rw [(h 0).1, (h 0).2, (h 1).1, (h 1).2, (h 2).1, (h 2).2]
  push_cast; ring
theorem phi_det_ne (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) :
    det3 (sw σ T hT 0).re (sw σ T hT 0).im (sw σ T hT 1).re (sw σ T hT 1).im
      (sw σ T hT 2).re (sw σ T hT 2).im ≠ 0 := by
  intro h
  have h1 := phi_det_eq hn σ hσ hm4 T hT
  rw [h, Complex.ofReal_zero] at h1
  have h2 : detc (cK hn T hT) = 0 := σ.toRingHom.injective (by rw [map_zero]; exact h1.symm)
  have h3 := detc_cK hn T hT
  rw [h2, map_zero] at h3
  exact T.det_ne_zero (by exact_mod_cast h3.symm)
noncomputable def phiTri (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) : Tri :=
  mkTri (sw σ T hT 0).re (sw σ T hT 0).im (sw σ T hT 1).re (sw σ T hT 1).im
    (sw σ T hT 2).re (sw σ T hT 2).im (phi_det_ne hn σ hσ hm4 T hT)
theorem phiTri_pts (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) :
    (phiTri hn σ hσ hm4 T hT).pts k = mkPt (sw σ T hT k).re (sw σ T hT k).im := by
  fin_cases k <;> rfl
theorem toC_phiTri (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) :
    toC ((phiTri hn σ hσ hm4 T hT).pts k) = sw σ T hT k := by
  rw [phiTri_pts, toC_apply]; simp [Complex.re_add_im]
theorem sigma_cK_phi (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (k : Fin 3) (v : Fin 2) :
    σ (cK hn T hT k v) = ((cT (phiTri hn σ hσ hm4 T hT) k v : ℝ) : ℂ) := by
  have h := sigma_cK hn σ hσ hm4 T hT k
  fin_cases v
  · simp only [cT, phiTri_pts]; exact h.1
  · simp only [cT, phiTri_pts]; exact h.2
theorem phi_det (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) :
    (((phiTri hn σ hσ hm4 T hT).det : ℝ) : ℂ) = σ (detc (cK hn T hT)) := by
  rw [show σ (detc (cK hn T hT)) = σ.toRingHom (detc (cK hn T hT)) from rfl, map_detc, ← detc_cT]
  have e : (fun k v => σ.toRingHom (cK hn T hT k v))
      = fun k v => ((cT (phiTri hn σ hσ hm4 T hT) k v : ℝ) : ℂ) := by
    funext k v; exact sigma_cK_phi hn σ hσ hm4 T hT k v
  rw [e, ← Complex.ofRealHom_eq_coe, map_detc]; rfl
theorem phi_Λ (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (i j : ℕ) :
    σ (Λ (Qm (cK hn T hT) i j)) = ((Λ (Qm (cT (phiTri hn σ hσ hm4 T hT)) i j) : ℝ) : ℂ) := by
  have h1 := map_Λ σ.toRingHom (Qm (cK hn T hT) i j)
  rw [map_Qm] at h1
  have h2 := map_Λ Complex.ofRealHom (Qm (cT (phiTri hn σ hσ hm4 T hT)) i j)
  rw [map_Qm] at h2
  change σ _ = _ at h1
  rw [h1, Complex.ofRealHom_eq_coe] at *
  rw [h2]
  congr 2
  funext k v
  exact sigma_cK_phi hn σ hσ hm4 T hT k v
variable {N : ℕ} (D : Dissection N) (hK : ∀ i k, toC ((D.tile i).pts k) ∈ Kf n)
  (hKT : ∀ k, toC (D.target.pts k) ∈ Kf n) (P : ℝ) (hP : ∀ i, |(D.tile i).det| = P)
  (hPT : |D.target.det| = N * P)
theorem phi_det_mul (T T' : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n)
    (hT' : ∀ k, toC (T'.pts k) ∈ Kf n) (c : ℚ) (h : T.det = c * T'.det) :
    (phiTri hn σ hσ hm4 T hT).det = c * (phiTri hn σ hσ hm4 T' hT').det := by
  have hK : detc (cK hn T hT) = (c : Kf n) * detc (cK hn T' hT') := by
    apply (algebraMap (Kf n) ℂ).injective
    rw [map_mul, detc_cK, detc_cK, map_ratCast, h]; push_cast; ring
  have := phi_det hn σ hσ hm4 T hT
  rw [hK, map_mul, map_ratCast, ← phi_det hn σ hσ hm4 T' hT'] at this
  exact_mod_cast this
include hP hPT in
theorem phi_moment (i j : ℕ) :
    ∑ t, ∫ x in (phiTri hn σ hσ hm4 (D.tile t) (hK t)).carrier, (x 0) ^ i * (x 1) ^ j
      = ∫ x in (phiTri hn σ hσ hm4 D.target hKT).carrier, (x 0) ^ i * (x 1) ^ j := by
  have hN := D.pos
  set t0 : Fin N := ⟨0, hN⟩
  have hPpos : 0 < P := by rw [← hP t0]; exact abs_pos.mpr (D.tile t0).det_ne_zero
  have hreal : ∑ t, Λ (Qm (cT (D.tile t)) i j) = N * Λ (Qm (cT D.target) i j) := by
    have h := dissection_integral_sum D (h := fun x : Plane => (x 0) ^ i * (x 1) ^ j)
      (((cont_coord 0).pow i).mul ((cont_coord 1).pow j))
    simp only [integral_tri, hP, hPT] at h
    rw [← Finset.mul_sum] at h
    apply mul_left_cancel₀ hPpos.ne'
    rw [h]; ring
  have hK' : ∑ t, Λ (Qm (cK hn (D.tile t) (hK t)) i j) = N * Λ (Qm (cK hn D.target hKT) i j) := by
    apply (algebraMap (Kf n) ℂ).injective
    rw [map_sum, map_mul, map_natCast]
    simp only [alg_Λ]
    exact_mod_cast hreal
  have hphi : ∑ t, Λ (Qm (cT (phiTri hn σ hσ hm4 (D.tile t) (hK t))) i j)
      = N * Λ (Qm (cT (phiTri hn σ hσ hm4 D.target hKT)) i j) := by
    have := congrArg σ hK'
    rw [map_sum, map_mul, map_natCast] at this
    simp only [phi_Λ hn σ hσ hm4] at this
    exact_mod_cast this
  have hdt : ∀ t, ∃ c : ℚ, (c = 1 ∨ c = -1) ∧ (D.tile t).det = c * (D.tile t0).det := by
    intro t
    have := (hP t).trans (hP t0).symm
    rcases abs_eq_abs.mp this with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩
  have hdT : ∃ c : ℚ, (c = N ∨ c = -N) ∧ D.target.det = c * (D.tile t0).det := by
    have : |D.target.det| = |(N : ℝ) * (D.tile t0).det| := by
      rw [hPT, abs_mul, Nat.abs_cast, hP]
    rcases abs_eq_abs.mp this with h | h
    · exact ⟨N, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨-N, Or.inr rfl, by rw [h]; push_cast; ring⟩
  set Q := |(phiTri hn σ hσ hm4 (D.tile t0) (hK t0)).det|
  have hQt : ∀ t, |(phiTri hn σ hσ hm4 (D.tile t) (hK t)).det| = Q := by
    intro t
    obtain ⟨c, hc, h⟩ := hdt t
    rw [phi_det_mul hn σ hσ hm4 _ _ (hK t) (hK t0) c h, abs_mul]
    rcases hc with rfl | rfl <;> simp [Q]
  have hQT : |(phiTri hn σ hσ hm4 D.target hKT).det| = N * Q := by
    obtain ⟨c, hc, h⟩ := hdT
    rw [phi_det_mul hn σ hσ hm4 _ _ hKT (hK t0) c h, abs_mul]
    rcases hc with rfl | rfl <;> simp [Q]
  simp only [integral_tri, hQt, hQT]
  rw [← Finset.mul_sum, hphi]; ring
include hP hPT in
theorem phi_ae :
    ∀ᵐ x, ∑ t, (phiTri hn σ hσ hm4 (D.tile t) (hK t)).carrier.indicator (1 : Plane → ℝ) x
      = (phiTri hn σ hσ hm4 D.target hKT).carrier.indicator 1 x := by
  let U : Option (Fin N) → Set Plane := fun o => match o with
    | none => (phiTri hn σ hσ hm4 D.target hKT).carrier
    | some t => (phiTri hn σ hσ hm4 (D.tile t) (hK t)).carrier
  let c : Option (Fin N) → ℝ := fun o => match o with
    | none => -1
    | some _ => 1
  have hU : ∀ o, IsCompact (U o) := by
    intro o; cases o <;> exact Tri.isCompact _
  have hmom : ∀ i j : ℕ, ∑ o, c o * ∫ x in U o, (x 0) ^ i * (x 1) ^ j = 0 := by
    intro i j
    rw [Fintype.sum_option]
    simp only [U, c, one_mul, neg_one_mul]
    rw [phi_moment hn σ hσ hm4 D hK hKT P hP hPT i j]; ring
  filter_upwards [ae_zero_of_moments c hU hmom] with x hx
  rw [comb, Fintype.sum_option] at hx
  simp only [U, c, one_mul, neg_one_mul] at hx
  linarith
include hP hPT in
noncomputable def phiDissection : Dissection N :=
  dissectionOfAe (fun t => phiTri hn σ hσ hm4 (D.tile t) (hK t)) (phiTri hn σ hσ hm4 D.target hKT)
    D.pos (phi_ae hn σ hσ hm4 D hK hKT P hP hPT)
end Phi
end Erdos634.KConj
end

section
open Complex
namespace Erdos634.KConj
open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.Geometry.A1Field
theorem arg_exp_I {θ : ℝ} (h1 : -Real.pi < θ) (h2 : θ ≤ Real.pi) :
    arg (Complex.exp ((θ : ℂ) * I)) = θ := by
  rw [arg_exp]
  simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
  rw [toIocMod_eq_self]
  constructor <;> linarith
theorem exp_sub_pi (θ : ℝ) :
    Complex.exp ((θ : ℂ) * I) = -Complex.exp (((θ - Real.pi : ℝ) : ℂ) * I) := by
  have : Complex.exp (((θ - Real.pi : ℝ) : ℂ) * I)
      = Complex.exp ((θ : ℂ) * I) * Complex.exp (-(Real.pi : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this, neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]; ring
theorem exp_add_pi (θ : ℝ) :
    Complex.exp ((θ : ℂ) * I) = -Complex.exp (((θ + Real.pi : ℝ) : ℂ) * I) := by
  have : Complex.exp (((θ + Real.pi : ℝ) : ℂ) * I)
      = Complex.exp ((θ : ℂ) * I) * Complex.exp ((Real.pi : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [this, Complex.exp_pi_mul_I]; ring
theorem abs_arg_phase {ρ y : ℝ} (hρ : ρ ≠ 0) (hy0 : 0 < y) (hy1 : y < 1) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    |arg ((ρ : ℂ) * Complex.exp (((ε * Real.pi * y : ℝ) : ℂ) * I))| = Real.pi * y ∨
    |arg ((ρ : ℂ) * Complex.exp (((ε * Real.pi * y : ℝ) : ℂ) * I))| = Real.pi * (1 - y) := by
  have hp := Real.pi_pos
  rcases lt_or_gt_of_ne hρ with hneg | hpos
  · right
    rcases hε with rfl | rfl
    · rw [exp_sub_pi, mul_neg, ← neg_mul, ← ofReal_neg, arg_real_mul _ (by linarith),
        arg_exp_I (by nlinarith) (by nlinarith), abs_of_neg (by nlinarith)]
      ring
    · rw [exp_add_pi, mul_neg, ← neg_mul, ← ofReal_neg, arg_real_mul _ (by linarith),
        arg_exp_I (by nlinarith) (by nlinarith), abs_of_pos (by nlinarith)]
      ring
  · left
    rcases hε with rfl | rfl
    · rw [arg_real_mul _ hpos, arg_exp_I (by nlinarith) (by nlinarith), abs_of_pos (by nlinarith)]
      ring
    · rw [arg_real_mul _ hpos, arg_exp_I (by nlinarith) (by nlinarith), abs_of_neg (by nlinarith)]
      ring
theorem cornerAngle_toC (p q r : Plane) :
    cornerAngle p q r = InnerProductGeometry.angle (toC p - toC q) (toC r - toC q) := by
  rw [cornerAngle, EuclideanGeometry.angle, ← toC.toLinearIsometry.angle_map]
  simp [vsub_eq_sub, map_sub]
variable {n m : ℕ} (hn : 0 < n) (σ : Kf n →ₐ[ℚ] ℂ)
  (hσ : σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ m) (hm4 : m % 4 = 1)
noncomputable def yf (n m b : ℕ) : ℝ := ((Int.fract ((((m : ℤ) * (b : ℤ) : ℤ) : ℚ) / n) : ℚ) : ℝ)
include hn hσ in
theorem sigma_phase (q : Kf n) (hq : q ≠ 0) (b : ℕ)
    (hb : |arg (q : ℂ)| = b * Real.pi / n) :
    ∃ ρ : ℝ, ρ ≠ 0 ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      σ q = (ρ : ℂ) * Complex.exp (((ε * Real.pi * yf n m b : ℝ) : ℂ) * I) := by
  have hq' : (q : ℂ) ≠ 0 := fun h => hq (Subtype.ext h)
  obtain ⟨ε, hε, hθ⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ arg (q : ℂ) = ((ε * b : ℤ) : ℝ) * Real.pi / n := by
    rcases abs_eq (by positivity : (0 : ℝ) ≤ b * Real.pi / n) |>.mp hb with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; push_cast; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; push_cast; ring⟩
  set E : Kf n := ⟨Complex.exp ((((ε * b : ℤ) : ℝ) * Real.pi / n : ℝ) * I), exp_int_mem hn _⟩
  have hE0 : E ≠ 0 := fun h => Complex.exp_ne_zero _ (congrArg Subtype.val h)
  set R : Kf n := q * E⁻¹
  have hRc : ((R : Kf n) : ℂ) = ((‖(q : ℂ)‖ : ℝ) : ℂ) := by
    have h1 := Complex.norm_mul_exp_arg_mul_I (q : ℂ)
    have hE' : ((E : Kf n) : ℂ) = Complex.exp ((arg (q : ℂ) : ℂ) * I) := by
      show Complex.exp (((((ε * b : ℤ) : ℝ) * Real.pi / n : ℝ)) * I) = _
      rw [hθ]
    rw [show ((R : Kf n) : ℂ) = (q : ℂ) * ((E : Kf n) : ℂ)⁻¹ by simp [R], hE', eq_comm,
      eq_mul_inv_iff_mul_eq₀ (Complex.exp_ne_zero _)]
    exact h1
  have hR0 : R ≠ 0 := mul_ne_zero hq (inv_ne_zero hE0)
  have hreal : (starRingEnd ℂ) (σ R) = σ R := sigma_real σ hσ R (by rw [hRc, Complex.conj_ofReal])
  set r := (σ R).re
  have hr : σ R = (r : ℂ) := (Complex.conj_eq_iff_re.mp hreal).symm
  have hr0 : r ≠ 0 := by
    intro h; rw [h, Complex.ofReal_zero] at hr
    exact hR0 (σ.toRingHom.injective (by rw [map_zero]; exact hr))
  have hσE := sigma_exp σ hσ hn (ε * b)
  set x : ℚ := (((m : ℤ) * (b : ℤ) : ℤ) : ℚ) / n
  have hq2 := Int.fract_add_floor x
  have hx : (((ε * b * m : ℤ) : ℝ) * Real.pi / n)
      = (ε : ℝ) * Real.pi * yf n m b + ((ε * ⌊x⌋ : ℤ) : ℝ) * Real.pi := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hxr : ((x : ℚ) : ℝ) = (((m : ℤ) * (b : ℤ) : ℤ) : ℝ) / n := by simp [x]
    have hq3 := congrArg (fun t : ℚ => (t : ℝ)) hq2
    simp only [Rat.cast_add, Rat.cast_intCast] at hq3
    have hyf : yf n m b = ((Int.fract x : ℚ) : ℝ) := rfl
    have hmb : (((m : ℤ) * (b : ℤ) : ℤ) : ℝ) = ((Int.fract x : ℚ) : ℝ) * n + (⌊x⌋ : ℝ) * n := by
      rw [← add_mul, hq3, hxr]; field_simp
    have e1 : (((ε * b * m : ℤ) : ℝ)) = (ε : ℝ) * (((m : ℤ) * (b : ℤ) : ℤ) : ℝ) := by push_cast; ring
    have e2 : ((ε * ⌊x⌋ : ℤ) : ℝ) = (ε : ℝ) * (⌊x⌋ : ℝ) := by push_cast; ring
    rw [e1, hmb, hyf, e2]
    field_simp
  refine ⟨r * (-1) ^ ⌊x⌋, ?_, ε, ?_, ?_⟩
  · exact mul_ne_zero hr0 (zpow_ne_zero _ (by norm_num))
  · rcases hε with rfl | rfl <;> simp
  · have hqRE : q = R * E := by simp [R, hE0]
    rw [hqRE, map_mul, hr, hσE]
    have e1 : Complex.exp ((((ε * b * m : ℤ) : ℝ) * Real.pi / n : ℝ) * I)
        = (((-1 : ℝ) ^ ⌊x⌋ : ℝ) : ℂ) * Complex.exp ((((ε : ℝ) * Real.pi * yf n m b : ℝ) : ℂ) * I) := by
      rw [hx]
      push_cast
      rw [add_mul, Complex.exp_add, mul_comm (Complex.exp _)]
      congr 1
      have : ((ε : ℂ) * (⌊x⌋ : ℂ) * (Real.pi : ℂ) * I) = ((ε * ⌊x⌋ : ℤ) : ℂ) * ((Real.pi : ℂ) * I) := by
        push_cast; ring
      rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I]
      rcases hε with rfl | rfl
      · simp
      · simp only [Int.reduceNeg, neg_mul, one_mul, zpow_neg]
        rw [← inv_zpow, inv_neg, inv_one]
    rw [e1]; push_cast; ring
include hσ hm4 in
theorem phi_angle (T : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (v : Fin 3) (b : ℕ)
    (hb : T.angleAt v = b * Real.pi / n) (hy0 : 0 < yf n m b) :
    (phiTri hn σ hσ hm4 T hT).angleAt v = Real.pi * yf n m b ∨
    (phiTri hn σ hσ hm4 T hT).angleAt v = Real.pi * (1 - yf n m b) := by
  set z : Fin 3 → Kf n := fun k => ⟨toC (T.pts k), hT k⟩
  have hne : ∀ j : Fin 3, j ≠ v → z j - z v ≠ 0 := by
    intro j hj h
    have h' : toC (T.pts j) = toC (T.pts v) := by
      have := congrArg Subtype.val h; simpa [z, sub_eq_zero] using this
    exact hj (T.indep.injective (toC.injective h'))
  have h1 : v + 1 ≠ v := (by decide : ∀ w : Fin 3, w + 1 ≠ w) v
  have h2 : v + 2 ≠ v := (by decide : ∀ w : Fin 3, w + 2 ≠ w) v
  set q : Kf n := (z (v + 1) - z v) / (z (v + 2) - z v)
  have hq0 : q ≠ 0 := div_ne_zero (hne _ h1) (hne _ h2)
  have hcoe : ∀ j, ((z j - z v : Kf n) : ℂ) ≠ 0 → True := fun _ _ => trivial
  have hzne : ∀ j : Fin 3, j ≠ v → ((z j : ℂ) - (z v : ℂ)) ≠ 0 := by
    intro j hj h; apply hne j hj; ext; simpa using h
  have hang : T.angleAt v = |arg (q : ℂ)| := by
    rw [Tri.angleAt, cornerAngle_toC, Complex.angle_eq_abs_arg (hzne _ h1) (hzne _ h2)]
    simp [q, z]
  rw [hang] at hb
  obtain ⟨ρ, hρ, ε, hε, hσq⟩ := sigma_phase hn σ hσ q hq0 b hb
  have hzne' : ∀ j : Fin 3, j ≠ v → σ (z j) - σ (z v) ≠ 0 := by
    intro j hj h
    rw [← map_sub] at h
    exact hne j hj (σ.toRingHom.injective (by rw [map_zero]; exact h))
  have hang' : (phiTri hn σ hσ hm4 T hT).angleAt v = |arg (σ q)| := by
    rw [Tri.angleAt, cornerAngle_toC, toC_phiTri, toC_phiTri, toC_phiTri]
    show InnerProductGeometry.angle (σ (z (v + 1)) - σ (z v)) (σ (z (v + 2)) - σ (z v)) = _
    rw [Complex.angle_eq_abs_arg (hzne' _ h1) (hzne' _ h2)]
    simp [q, map_div₀, map_sub, sw, z]
  have hy1 : yf n m b < 1 := by
    rw [yf]; exact_mod_cast Int.fract_lt_one _
  rw [hang', hσq]
  exact abs_arg_phase hρ hy0 hy1 hε
end Erdos634.KConj
end

section
open Complex MeasureTheory
namespace Erdos634.KConj
open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.Geometry.A1Field Erdos634.DissectionMap Erdos634.AreaDet
variable {N : ℕ} (D : CongruentDissection N)
noncomputable def cN : ℂ := (wAB D)⁻¹ / ((circD D.model : ℝ) : ℂ)
theorem cN_ne : cN D ≠ 0 :=
  div_ne_zero (inv_ne_zero (wAB_ne D)) (ofReal_ne_zero.mpr (circD_pos _).ne')
noncomputable def linN : Plane ≃ₗ[ℝ] Plane :=
  toC.toLinearEquiv ≪≫ₗ ((LinearEquiv.smulOfNeZero ℂ ℂ (cN D) (cN_ne D)).restrictScalars ℝ) ≪≫ₗ
    toC.symm.toLinearEquiv
noncomputable def eN : Plane ≃ᵃ[ℝ] Plane :=
  (AffineEquiv.constVAdd ℝ Plane (-D.target.pts 0)).trans (linN D).toAffineEquiv
theorem toC_eN (P : Plane) : toC (eN D P) = zc D P := by
  simp only [eN, linN, AffineEquiv.trans_apply, AffineEquiv.constVAdd_apply, vadd_eq_add,
    LinearEquiv.coe_toAffineEquiv, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    LinearEquiv.smulOfNeZero_apply, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply, smul_eq_mul, zc, cN]
  rw [neg_add_eq_sub, mul_comm]
noncomputable def Dn : Dissection N := mapDissection (eN D) D.toDissection
theorem Dn_tile_pts (i : Fin N) (k : Fin 3) : ((Dn D).tile i).pts k = eN D ((D.tile i).pts k) :=
  rfl
theorem Dn_target_pts (k : Fin 3) : (Dn D).target.pts k = eN D (D.target.pts k) := rfl
theorem Dn_hK {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (i : Fin N) (k : Fin 3) :
    toC (((Dn D).tile i).pts k) ∈ Kf n := by
  rw [Dn_tile_pts, toC_eN]
  have h := lemma1_full D hn a ha
  exact h.2.2.2.2.2.2.2.2 _ (h.2.2.2.2.2.2.1 i k)
theorem Dn_hKT {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (k : Fin 3) :
    toC ((Dn D).target.pts k) ∈ Kf n := by
  rw [Dn_target_pts, toC_eN]
  have h := lemma1_full D hn a ha
  exact h.2.2.2.2.2.2.2.2 _ (h.2.2.2.2.2.2.2.1 k)
theorem detTri_eq_det' (T : Tri) : detTri T = T.det := by
  rw [detTri_eq]; unfold Tri.det; ring
theorem abs_det_congr {T U : Tri} (h : T.Congruent U) : |T.det| = |U.det| := by
  have hv := Erdos634.CongruentArea.volume_congruent h
  rw [volume_eq_det_mul, volume_eq_det_mul, detTri_eq_det', detTri_eq_det'] at hv
  have hS0 : volume stdCarrier ≠ 0 := by
    have hp := U.volume_pos
    rw [volume_eq_det_mul, detTri_eq_det'] at hp
    intro h0; rw [h0, mul_zero] at hp; exact lt_irrefl _ hp
  have hST : volume stdCarrier ≠ ⊤ := by
    have hf := U.volume_ne_top
    rw [volume_eq_det_mul, detTri_eq_det'] at hf
    intro h0; apply hf; rw [h0]
    exact ENNReal.mul_top (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact abs_pos.mpr U.det_ne_zero)
  have := (ENNReal.mul_left_inj hS0 hST).mp hv
  exact (ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (abs_nonneg _)).mp this
noncomputable def PN : ℝ := |LinearMap.det ((eN D).linear : Plane →ₗ[ℝ] Plane)| * |D.model.det|
theorem Dn_hP (i : Fin N) : |((Dn D).tile i).det| = PN D := by
  rw [Dn, mapDissection_tile, ← detTri_eq_det', detTri_mapTri, abs_mul, detTri_eq_det',
    abs_det_congr (D.tiles_congruent i), PN]
theorem Dn_hPT : |(Dn D).target.det| = N * PN D := by
  rw [Dn, mapDissection_target, ← detTri_eq_det', detTri_mapTri, abs_mul, detTri_eq_det',
    Erdos634.Geometry.Row3.RP.abs_det_target D, PN]
  ring
theorem angleAt_eN (T : Tri) (v : Fin 3) : (mapTri (eN D) T).angleAt v = T.angleAt v := by
  have key : ∀ p q : Plane, toC (eN D p) - toC (eN D q) = (toC p - toC q) * cN D := by
    intro p q
    rw [toC_eN, toC_eN, zc, zc, map_sub, map_sub]
    simp only [cN]; ring
  rw [Tri.angleAt, Tri.angleAt, cornerAngle_toC, cornerAngle_toC]
  show InnerProductGeometry.angle (toC (eN D _) - toC (eN D _)) (toC (eN D _) - toC (eN D _)) = _
  rw [key, key, Complex.angle_mul_right (cN_ne D)]
theorem eN_inj {p q : Plane} : eN D p = eN D q ↔ p = q := (eN D).injective.eq_iff
end Erdos634.KConj
end

section


open Complex
namespace Erdos634.KConj
open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV Erdos634.Geometry.CaseA.LemmaK1 Erdos634.LemmaKStar Erdos634.DissectionMap Erdos634.CertCoord
variable {N : ℕ}
theorem localAngle_nonvertex (T : Tri) (p : Plane) (h : ∀ v, p ≠ T.pts v) :
    T.localAngle p = 0 ∨ Real.pi ≤ T.localAngle p := by
  classical
  unfold Tri.localAngle
  rw [dif_neg (fun ⟨j, hj⟩ => h j hj)]
  split_ifs
  · right; linarith [Real.pi_pos]
  · right; exact le_refl _
  · left; rfl
noncomputable def vc (T : Tri) (p : Plane) : ℝ := ∑ v, if T.pts v = p then T.angleAt v else 0
theorem vc_of_vertex (T : Tri) (v0 : Fin 3) : vc T (T.pts v0) = T.localAngle (T.pts v0) := by
  rw [vc, Tri.localAngle_vertex]
  have : ∀ v, (T.pts v = T.pts v0) ↔ v = v0 := fun v => T.indep.injective.eq_iff
  simp only [this]
  rw [Finset.sum_ite_eq']; simp; rfl
theorem vc_of_nonvertex (T : Tri) (p : Plane) (h : ∀ v, p ≠ T.pts v) : vc T p = 0 := by
  rw [vc]; exact Finset.sum_eq_zero (fun v _ => if_neg (fun h' => h v h'.symm))
theorem vertex_sum (D0 : Dissection N) (j : Fin 3) :
    ∑ i, vc (D0.tile i) (D0.target.pts j) = D0.target.angleAt j := by
  have hsum := D0.sum_localAngle_eq (D0.target.pts j)
  rw [Tri.localAngle_vertex] at hsum
  have hlt : D0.target.angleAt j < Real.pi := angle_lt_pi _ j
  have hnn : ∀ i, 0 ≤ (D0.tile i).localAngle (D0.target.pts j) := fun i => Tri.localAngle_nonneg _ _
  have key : ∀ i, vc (D0.tile i) (D0.target.pts j) = (D0.tile i).localAngle (D0.target.pts j) := by
    intro i
    by_cases hv : ∃ v, D0.target.pts j = (D0.tile i).pts v
    · obtain ⟨v, hv⟩ := hv; rw [hv]; exact vc_of_vertex _ v
    · push Not at hv
      rw [vc_of_nonvertex _ _ hv]
      rcases localAngle_nonvertex _ _ hv with h | h
      · exact h.symm
      · exfalso
        have := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i)
        rw [hsum] at this
        exact absurd (lt_of_lt_of_le hlt (h.trans this)) (lt_irrefl _)
  rw [Finset.sum_congr rfl (fun i _ => key i), hsum]; rfl
noncomputable def fig (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (j l : Fin 3) :
    ℕ :=
  (Finset.univ.filter (fun p : Fin N × Fin 3 =>
    (D.tile p.1).pts p.2 = D.target.pts j ∧ idx p.1 p.2 = l)).card
theorem fiber_sum (D : CongruentDissection N) (idx : Fin N → Equiv.Perm (Fin 3)) (j : Fin 3)
    (g : Fin 3 → ℝ) :
    ∑ i, ∑ v, (if (D.tile i).pts v = D.target.pts j then g (idx i v) else 0)
      = ∑ l, (fig D idx j l : ℝ) * g l := by
  classical
  have h1 : ∀ l, (fig D idx j l : ℝ) * g l = ∑ p : Fin N × Fin 3,
      (if (D.tile p.1).pts p.2 = D.target.pts j ∧ idx p.1 p.2 = l then g l else 0) := by
    intro l
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, fig]
  calc ∑ i, ∑ v, (if (D.tile i).pts v = D.target.pts j then g (idx i v) else 0)
      = ∑ p : Fin N × Fin 3, (if (D.tile p.1).pts p.2 = D.target.pts j then g (idx p.1 p.2) else 0) :=
        by rw [Fintype.sum_prod_type]
    _ = ∑ p : Fin N × Fin 3, ∑ l, (if (D.tile p.1).pts p.2 = D.target.pts j ∧ idx p.1 p.2 = l
          then g l else 0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        by_cases hp : (D.tile p.1).pts p.2 = D.target.pts j
        · simp only [hp, true_and, if_true]
          rw [Finset.sum_ite_eq]; simp
        · simp [hp]
    _ = ∑ l, ∑ p : Fin N × Fin 3, (if (D.tile p.1).pts p.2 = D.target.pts j ∧ idx p.1 p.2 = l
          then g l else 0) := Finset.sum_comm
    _ = ∑ l, (fig D idx j l : ℝ) * g l := by simp_rw [h1]
theorem exists_idx (D : CongruentDissection N) {n : ℕ} (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    ∃ idx : Fin N → Equiv.Perm (Fin 3), ∀ i v, (D.tile i).angleAt v = a (idx i v) * Real.pi / n := by
  choose idx hidx using fun i => Tri.Congruent.cornerAngle_perm (D.tiles_congruent i)
  exact ⟨idx, fun i v => by rw [Tri.angleAt, ← hidx i v]; exact ha (idx i v)⟩
theorem target_angle_fig (D : CongruentDissection N) {n : ℕ} (a : Fin 3 → ℕ)
    (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i v, (D.tile i).angleAt v = a (idx i v) * Real.pi / n) (j : Fin 3) :
    D.target.angleAt j = (uu a (fig D idx) j : ℕ) * Real.pi / n := by
  have h := vertex_sum D.toDissection j
  simp only [vc] at h
  have e : ∀ i v, (if (D.tile i).pts v = D.target.pts j then (D.tile i).angleAt v else 0)
      = (if (D.tile i).pts v = D.target.pts j then (fun l => (a l : ℝ) * Real.pi / n) (idx i v)
          else 0) := by
    intro i v; split_ifs <;> simp [hidx]
  simp only [e] at h
  have hfs := fiber_sum D idx j (fun l => (a l : ℝ) * Real.pi / n)
  beta_reduce at hfs
  rw [hfs] at h
  rw [← h, uu]; push_cast
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl (fun l _ => by ring)
theorem forced (y β : Fin 3 → ℝ) (hy : ∀ v, 0 < y v) (hy1 : ∀ v, y v < 1)
    (hβ : ∀ v, β v = y v ∨ β v = 1 - y v) (hβs : β 0 + β 1 + β 2 = 1) {s : ℝ}
    (hs : y 0 + y 1 + y 2 = s) (hs12 : s = 1 ∨ s = 2) (v : Fin 3) :
    β v = if s = 1 then y v else 1 - y v := by
  have h0 := hy 0; have h1 := hy 1; have h2 := hy 2
  have g0 := hy1 0; have g1 := hy1 1; have g2 := hy1 2
  rcases hs12 with rfl | rfl
  · rw [if_pos rfl]
    rcases hβ 0 with a0 | a0 <;> rcases hβ 1 with a1 | a1 <;> rcases hβ 2 with a2 | a2 <;>
      fin_cases v <;> simp <;> linarith
  · rw [if_neg (by norm_num)]
    rcases hβ 0 with a0 | a0 <;> rcases hβ 1 with a1 | a1 <;> rcases hβ 2 with a2 | a2 <;>
      fin_cases v <;> simp <;> linarith
theorem K2_congr {n : ℕ} (hn : 0 < n) {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ}
    (hsum : ∑ i, a i = n) (ha1 : ∀ i, 1 ≤ a i) (hsu : ∑ j, uu a f j = n) (hu1 : ∀ j, 1 ≤ uu a f j)
    {k m : ℤ} (hk : Int.gcd k n = 1) (h : (n : ℤ) ∣ m - k ∨ (n : ℤ) ∣ m + k) :
    K2 n a f m ↔ K2 n a f k := by
  have hxp : ∀ i, xp n a m i = xp n a k i ∧ ∀ j, xpu n a f m j = xpu n a f k j := by
    intro i
    rcases h with h | h
    · have hy : ∀ l, yv n a m l = yv n a k l := fun l => yv_congr h hn l
      have hx : ∀ l, xv n a f m l = xv n a f k l := fun l => yv_congr (a := uu a f) h hn l
      have hs : sT n a m = sT n a k := by unfold sT; simp only [hy]
      refine ⟨by unfold xp; rw [hs, hy], fun j => by unfold xpu; rw [hs, hx]⟩
    · have h' : (n : ℤ) ∣ m - (-k) := by simpa using h
      have hy : ∀ l, yv n a m l = 1 - yv n a k l := fun l => by
        rw [yv_congr h' hn l, yv_neg hsum ha1 hk]
      have hx : ∀ l, xv n a f m l = 1 - xv n a f k l := fun l => by
        rw [show xv n a f m l = yv n (uu a f) m l from rfl, yv_congr (a := uu a f) h' hn l,
          yv_neg hsu hu1 hk]; rfl
      have hs : sT n a m = 3 - sT n a k := by
        unfold sT; simp only [hy, Fin.sum_univ_three]; ring
      rcases sT_12 hsum ha1 hk with h1 | h1
      · have hm : sT n a m ≠ 1 := by rw [hs, h1]; norm_num
        refine ⟨by unfold xp; rw [if_neg hm, if_pos h1, hy]; ring,
          fun j => by unfold xpu; rw [if_neg hm, if_pos h1, hx]; ring⟩
      · have hm : sT n a m = 1 := by rw [hs, h1]; norm_num
        have hk1 : sT n a k ≠ 1 := by rw [h1]; norm_num
        exact ⟨by unfold xp; rw [if_pos hm, if_neg hk1, hy],
          fun j => by unfold xpu; rw [if_pos hm, if_neg hk1, hx]⟩
  unfold K2
  constructor
  · intro H j; rw [← (hxp 0).2 j, ← H j]; simp only [fun i => (hxp i).1]
  · intro H j; rw [(hxp 0).2 j, ← H j]; simp only [fun i => (hxp i).1]
theorem phi_pts_eq {n m : ℕ} (hn : 0 < n) (σ : Kf n →ₐ[ℚ] ℂ)
    (hσ : σ (IntermediateField.AdjoinSimple.gen ℚ (zeta n)) = zeta n ^ m) (hm4 : m % 4 = 1)
    (T T' : Tri) (hT : ∀ k, toC (T.pts k) ∈ Kf n) (hT' : ∀ k, toC (T'.pts k) ∈ Kf n) (v w : Fin 3) :
    (phiTri hn σ hσ hm4 T hT).pts v = (phiTri hn σ hσ hm4 T' hT').pts w ↔ T.pts v = T'.pts w := by
  constructor
  · intro h
    have h1 := congrArg toC h
    rw [toC_phiTri, toC_phiTri] at h1
    have h2 : (⟨toC (T.pts v), hT v⟩ : Kf n) = ⟨toC (T'.pts w), hT' w⟩ := σ.toRingHom.injective h1
    exact toC.injective (congrArg Subtype.val h2)
  · intro h
    apply toC.injective
    rw [toC_phiTri, toC_phiTri]
    show σ ⟨toC (T.pts v), hT v⟩ = σ ⟨toC (T'.pts w), hT' w⟩
    congr 2; rw [h]
theorem lemmaK (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (idx : Fin N → Equiv.Perm (Fin 3))
    (hidx : ∀ i v, (D.tile i).angleAt v = a (idx i v) * Real.pi / n) :
    (∀ j, D.target.angleAt j = (uu a (fig D idx) j : ℕ) * Real.pi / n) ∧
    ∀ k : ℤ, Int.gcd k n = 1 → K1 n a (fig D idx) k ∧ K2 n a (fig D idx) k := by
  set f := fig D idx
  have hf := target_angle_fig D a idx hidx
  refine ⟨hf, fun k hk => ⟨lemmaK_K1 D hn a ha f hf hk, ?_⟩⟩
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have sum_of : ∀ (T : Tri) (b : Fin 3 → ℕ), (∀ i, T.angleAt i = b i * Real.pi / n) →
      ∑ i, b i = n := by
    intro T b hb
    have hs := T.angleAt_sum
    rw [hb 0, hb 1, hb 2] at hs
    have hnn : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
    have key : (((b 0 + b 1 + b 2 : ℕ) : ℝ) - n) * (Real.pi / n) = 0 := by
      push_cast; linear_combination hs - hnn
    have := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (div_ne_zero Real.pi_ne_zero hn'))
    rw [Fin.sum_univ_three]; exact_mod_cast this
  have hsum := sum_of _ a ha
  have hsu := sum_of _ (uu a f) hf
  have ha1 : ∀ i, 1 ≤ a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hu1 : ∀ j, 1 ≤ uu a f j := fun j => (nat_bounds hn (hf j) (angle_pos _ j) (angle_lt_pi _ j)).1
  obtain ⟨m, hmc, hm4, hmk⟩ := exists_m hn hk
  obtain ⟨σ, hσ⟩ := exists_sigma hn hmc
  have hmg : Int.gcd (m : ℤ) n = 1 := by
    rw [Int.gcd_natCast_natCast]; exact Nat.Coprime.coprime_mul_left_right hmc
  rw [← K2_congr hn hsum ha1 hsu hu1 hk hmk]
  set Dn' := Dn D
  set E := phiDissection hn σ hσ hm4 Dn' (Dn_hK D hn a ha) (Dn_hKT D hn a ha) (PN D) (Dn_hP D)
    (Dn_hPT D)
  have hy : ∀ l, yf n m (a l) = ((yv n a m l : ℚ) : ℝ) := fun l => rfl
  have hyp : ∀ l, 0 < yv n a m l := fun l =>
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (yv_ne hsum ha1 hmg l))
  have hyl : ∀ l, yv n a m l < 1 := fun l => Int.fract_lt_one _
  have hs12 : sT n a m = 1 ∨ sT n a m = 2 := sT_12 hsum ha1 hmg
  have tile_ang : ∀ i v, (E.tile i).angleAt v = Real.pi * ((xp n a m (idx i v) : ℚ) : ℝ) := by
    intro i
    have hang : ∀ v, (E.tile i).angleAt v = Real.pi * yf n m (a (idx i v)) ∨
        (E.tile i).angleAt v = Real.pi * (1 - yf n m (a (idx i v))) := by
      intro v
      refine phi_angle hn σ hσ hm4 (Dn'.tile i) (Dn_hK D hn a ha i) v (a (idx i v)) ?_ ?_
      · rw [show Dn'.tile i = mapTri (eN D) (D.tile i) from rfl, angleAt_eN]; exact hidx i v
      · rw [hy]; exact_mod_cast hyp _
    have hsumβ := (E.tile i).angleAt_sum
    set y : Fin 3 → ℝ := fun v => ((yv n a m (idx i v) : ℚ) : ℝ)
    set β : Fin 3 → ℝ := fun v => (E.tile i).angleAt v / Real.pi
    have hpi := Real.pi_pos
    have hsy : y 0 + y 1 + y 2 = ((sT n a m : ℚ) : ℝ) := by
      have : ∑ v, y v = ∑ l, ((yv n a m l : ℚ) : ℝ) :=
        Equiv.sum_comp (idx i) (fun l => ((yv n a m l : ℚ) : ℝ))
      rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
      rw [this, sT, Fin.sum_univ_three]; push_cast; ring
    have hF := forced y β
      (fun v => by show (0 : ℝ) < ((yv n a m (idx i v) : ℚ) : ℝ); exact_mod_cast hyp _)
      (fun v => by show ((yv n a m (idx i v) : ℚ) : ℝ) < 1; exact_mod_cast hyl _)
      (fun v => by
        rcases hang v with h | h
        · left; simp only [β, y, h, ← hy]; field_simp
        · right; simp only [β, y, h, ← hy]; field_simp)
      (by simp only [β]; field_simp; linarith) hsy
      (by rcases hs12 with h | h <;> [left; right] <;> rw [h] <;> norm_num)
    intro v
    have := hF v
    simp only [β] at this
    rw [div_eq_iff hpi.ne'] at this
    rw [this, xp]
    split_ifs with h1 h2 h2
    · simp [y]; ring
    · exact absurd (by exact_mod_cast h1) h2
    · exact absurd (by rw [h2]; norm_num) h1
    · push_cast; simp [y]; ring
  have hK1 := lemmaK_K1 D hn a ha f hf hmg
  have hxp : ∀ l, 0 < xv n a f m l := fun l =>
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm (yv_ne (a := uu a f) hsu hu1 hmg l))
  have hxl : ∀ l, xv n a f m l < 1 := fun l => Int.fract_lt_one _
  have targ_ang : ∀ j, E.target.angleAt j = Real.pi * ((xpu n a f m j : ℚ) : ℝ) := by
    have hang : ∀ j, E.target.angleAt j = Real.pi * yf n m (uu a f j) ∨
        E.target.angleAt j = Real.pi * (1 - yf n m (uu a f j)) := by
      intro j
      refine phi_angle hn σ hσ hm4 Dn'.target (Dn_hKT D hn a ha) j (uu a f j) ?_ ?_
      · rw [show Dn'.target = mapTri (eN D) D.target from rfl, angleAt_eN]; exact hf j
      · show 0 < ((xv n a f m j : ℚ) : ℝ); exact_mod_cast hxp j
    have hsumβ := E.target.angleAt_sum
    set y : Fin 3 → ℝ := fun j => ((xv n a f m j : ℚ) : ℝ)
    set β : Fin 3 → ℝ := fun j => E.target.angleAt j / Real.pi
    have hpi := Real.pi_pos
    have hsy : y 0 + y 1 + y 2 = ((sT n a m : ℚ) : ℝ) := by
      rw [show sT n a m = sABC n a f m from hK1, sABC, Fin.sum_univ_three]; push_cast; rfl
    have hF := forced y β
      (fun v => by show (0 : ℝ) < ((xv n a f m v : ℚ) : ℝ); exact_mod_cast hxp _)
      (fun v => by show ((xv n a f m v : ℚ) : ℝ) < 1; exact_mod_cast hxl _)
      (fun v => by
        rcases hang v with h | h
        · left; simp only [β, y, h]; field_simp; rfl
        · right; simp only [β, y, h]; field_simp; rfl)
      (by simp only [β]; field_simp; linarith) hsy
      (by rcases hs12 with h | h <;> [left; right] <;> rw [h] <;> norm_num)
    intro j
    have := hF j
    simp only [β] at this
    rw [div_eq_iff hpi.ne'] at this
    rw [this, xpu]
    split_ifs with h1 h2 h2
    · simp [y]; ring
    · exact absurd (by exact_mod_cast h1) h2
    · exact absurd (by rw [h2]; norm_num) h1
    · push_cast; simp [y]; ring
  intro j
  have hv := vertex_sum E j
  simp only [vc] at hv
  have hpred : ∀ i v, ((E.tile i).pts v = E.target.pts j) ↔ ((D.tile i).pts v = D.target.pts j) := by
    intro i v
    rw [show E.tile i = phiTri hn σ hσ hm4 (Dn'.tile i) (Dn_hK D hn a ha i) from rfl,
      show E.target = phiTri hn σ hσ hm4 Dn'.target (Dn_hKT D hn a ha) from rfl, phi_pts_eq,
      Dn_tile_pts, Dn_target_pts, eN_inj]
  have e : ∀ i v, (if (E.tile i).pts v = E.target.pts j then (E.tile i).angleAt v else 0)
      = (if (D.tile i).pts v = D.target.pts j then
          (fun l => Real.pi * ((xp n a m l : ℚ) : ℝ)) (idx i v) else 0) := by
    intro i v
    by_cases hp : (D.tile i).pts v = D.target.pts j
    · rw [if_pos ((hpred i v).mpr hp), if_pos hp, tile_ang]
    · rw [if_neg (fun h => hp ((hpred i v).mp h)), if_neg hp]
  simp only [e] at hv
  have hfs := fiber_sum D idx j (fun l => Real.pi * ((xp n a m l : ℚ) : ℝ))
  beta_reduce at hfs
  rw [hfs, targ_ang] at hv
  have hv' : ∑ l, (f j l : ℝ) * ((xp n a m l : ℚ) : ℝ) = ((xpu n a f m j : ℚ) : ℝ) := by
    have hpi := Real.pi_pos
    apply mul_left_cancel₀ hpi.ne'
    rw [← hv, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => by ring)
  exact_mod_cast hv'
end Erdos634.KConj
end

section
open scoped BigOperators
namespace Erdos634.CaseA.R0c
open Erdos634.Geometry Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)
variable {N : ℕ}
theorem sum_of_angles {T : Tri} {n : ℕ} (hn : 0 < n) {b : Fin 3 → ℕ}
    (hb : ∀ i, T.angleAt i = b i * Real.pi / n) : ∑ i, b i = n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs := T.angleAt_sum
  rw [hb 0, hb 1, hb 2] at hs
  have hnn : (n : ℝ) * (Real.pi / n) = Real.pi := by field_simp
  have key : (((b 0 + b 1 + b 2 : ℕ) : ℝ) - n) * (Real.pi / n) = 0 := by
    push_cast; linear_combination hs - hnn
  have := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right (div_ne_zero Real.pi_ne_zero hn'))
  rw [Fin.sum_univ_three]; exact_mod_cast this
theorem perm_of_counts (g h : Fin 3 → ℕ)
    (hc : ∀ x : ℕ, ∑ j, (if g j = x then 1 else 0 : ℕ) = ∑ i, (if h i = x then 1 else 0 : ℕ)) :
    ∃ τ : Equiv.Perm (Fin 3), ∀ j, g j = h (τ j) := by
  have hp : List.Perm (List.ofFn g) (List.ofFn h) := by
    rw [List.perm_iff_count]
    intro x
    have := hc x
    simp only [Fin.sum_univ_three] at this
    simp only [List.ofFn_succ, List.ofFn_zero, List.count_cons, List.count_nil, beq_iff_eq]
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at *
    split_ifs at this ⊢ <;> omega
  have hsg := (Equiv.Perm.ofFn_comp_perm (Tuple.sort g) g)
  have hsh := (Equiv.Perm.ofFn_comp_perm (Tuple.sort h) h)
  have heq : List.ofFn (g ∘ Tuple.sort g) = List.ofFn (h ∘ Tuple.sort h) :=
    List.Perm.eq_of_sortedLE (List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort g))
      (List.sortedLE_ofFn_iff.mpr (Tuple.monotone_sort h)) (hsg.trans (hp.trans hsh.symm))
  have hf := List.ofFn_injective heq
  refine ⟨(Tuple.sort g).symm.trans (Tuple.sort h), fun j => ?_⟩
  have := congrFun hf ((Tuple.sort g).symm j)
  simpa using this
end Erdos634.CaseA.R0c
end

section
open scoped Classical
namespace Erdos634.Draft.LaczFormal
def Far (n1 m : ℕ) : Prop := 3 * (m % n1) ≤ n1 ∨ 2 * n1 ≤ 3 * (m % n1)
theorem lem52_n1 {n1 : ℕ} (h2 : 2 ≤ n1) (h : ∀ m : ℕ, Nat.Coprime m n1 → Far n1 m) :
    n1 = 3 ∨ n1 = 4 ∨ n1 = 6 ∨ n1 = 10 := by
  by_cases hle : n1 ≤ 6
  · interval_cases n1
    · have := h 1 (by norm_num); unfold Far at this; omega
    · simp
    · simp
    · have := h 2 (by norm_num); unfold Far at this; omega
    · simp
  · push Not at hle
    obtain ⟨q, hq, hq1, hq2⟩ := Nat.exists_prime_lt_and_le_two_mul (n1 / 3) (by omega)
    have hlo : n1 < 3 * q := by omega
    have hhi : 3 * q < 2 * n1 := by
      have : 3 * q ≤ 6 * (n1 / 3) := by omega
      have h6 : 6 * (n1 / 3) ≤ 2 * n1 := by omega
      by_contra hc
      have h3 : 3 * q = 2 * n1 := by omega
      have : 3 ∣ 2 * n1 := ⟨q, h3.symm⟩
      have h3n : 3 ∣ n1 := by omega
      obtain ⟨t, rfl⟩ := h3n
      have : q = 2 * t := by omega
      subst this
      have hp2 : (2 * t).Prime := hq
      have := (Nat.prime_mul_iff.mp hp2)
      rcases this with ⟨_, h1⟩ | ⟨_, h1⟩
      · omega
      · omega
    have hqlt : q < n1 := by omega
    by_cases hd : q ∣ n1
    · obtain ⟨s, hs⟩ := hd
      have hs2 : s = 2 := by
        have : s < 3 := by
          by_contra hc; push Not at hc; nlinarith
        have : 1 < s := by
          by_contra hc; push Not at hc
          interval_cases s <;> omega
        omega
      subst hs2
      subst hs
      have hq5 : 5 ≤ q := by
        by_contra hc; push Not at hc
        have h4 : q = 4 := by omega
        subst h4
        exact absurd hq (by norm_num)
      have hodd : q % 2 = 1 := by
        by_contra hc
        have h2d : 2 ∣ q := by omega
        rcases hq.eq_one_or_self_of_dvd 2 h2d with h' | h' <;> omega
      have hc1 : Nat.Coprime (q - 2) q := by
        apply Nat.Coprime.symm
        exact (Nat.Prime.coprime_iff_not_dvd hq).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
      have hc2 : Nat.Coprime (q - 2) 2 := by
        apply Nat.Coprime.symm
        exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
      have hcop : Nat.Coprime (q - 2) (q * 2) := Nat.Coprime.mul_right hc1 hc2
      have := h (q - 2) hcop
      unfold Far at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    · exfalso
      have hc : Nat.Coprime q n1 := (Nat.Prime.coprime_iff_not_dvd hq).mpr hd
      have := h q hc
      unfold Far at this
      rw [Nat.mod_eq_of_lt hqlt] at this
      omega
theorem lacz_lemma_5_2 {a n : ℕ} (h0 : 0 < a) (han : a < n)
    (h : ∀ k : ℕ, Nat.Coprime k (2 * n) →
      3 * ((k * a) % n) ≤ n ∨ 2 * n ≤ 3 * ((k * a) % n)) :
    ∃ n1 : ℕ, n = Nat.gcd a n * n1 ∧ (n1 = 3 ∨ n1 = 4 ∨ n1 = 6 ∨ n1 = 10) := by
  set d := Nat.gcd a n with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ h0
  obtain ⟨a1, ha1⟩ : d ∣ a := Nat.gcd_dvd_left a n
  obtain ⟨n1, hn1⟩ : d ∣ n := Nat.gcd_dvd_right a n
  have hcop : Nat.Coprime a1 n1 := by
    have e1 : a / d = a1 := Nat.div_eq_of_eq_mul_right hdpos ha1
    have e2 : n / d = n1 := Nat.div_eq_of_eq_mul_right hdpos hn1
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := n) hdpos
    rwa [← hd, e1, e2] at this
  have ha1pos : 0 < a1 := by
    rcases Nat.eq_zero_or_pos a1 with h' | h'
    · rw [h'] at ha1; omega
    · exact h'
  have hlt : a1 < n1 := by
    by_contra hc; push Not at hc
    have : d * n1 ≤ d * a1 := Nat.mul_le_mul_left d hc
    omega
  have hn12 : 2 ≤ n1 := by omega
  refine ⟨n1, by rw [← hn1], lem52_n1 hn12 ?_⟩
  intro m hm
  have hφ : 0 < Nat.totient n1 := Nat.totient_pos.mpr (by omega)
  set r := m * a1 ^ (Nat.totient n1 - 1) with hr
  have hrcop : Nat.Coprime r n1 :=
    Nat.Coprime.mul_left hm (Nat.Coprime.pow_left _ hcop)
  have hrm : r * a1 ≡ m [MOD n1] := by
    have : r * a1 = m * a1 ^ Nat.totient n1 := by
      rw [hr, mul_assoc, ← pow_succ, Nat.sub_add_cancel hφ]
    rw [this]
    have h1 := Nat.ModEq.pow_totient hcop
    simpa using (Nat.ModEq.refl m).mul h1
  set i := ∏ p ∈ (2 * n).primeFactors.filter (fun p => ¬ p ∣ r), p with hi
  have hkcop : Nat.Coprime (r + i * n1) (2 * n) := by
    apply Nat.coprime_of_dvd
    intro p hp hpk hp2n
    by_cases hpr : p ∣ r
    · have hin : p ∣ i * n1 := (Nat.dvd_add_right hpr).mp hpk
      have hpn1 : ¬ p ∣ n1 := fun hh =>
        hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hrcop ▸ Nat.dvd_gcd hpr hh))
      have hpi : ¬ p ∣ i := by
        intro hpi
        obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpi
        have hqm := Finset.mem_filter.mp hq
        have : p = q := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors hqm.1)).mp hpq
        exact hqm.2 (this ▸ hpr)
      rcases (Nat.Prime.dvd_mul hp).mp hin with h' | h'
      · exact hpi h'
      · exact hpn1 h'
    · have hpmem : p ∈ (2 * n).primeFactors.filter (fun p => ¬ p ∣ r) :=
        Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hp2n, by omega⟩, hpr⟩
      have hpi : p ∣ i := Finset.dvd_prod_of_mem _ hpmem
      have : p ∣ r := (Nat.dvd_add_left (dvd_mul_of_dvd_left hpi n1)).mp hpk
      exact hpr this
  have key := h _ hkcop
  have hmod : ((r + i * n1) * a) % n = d * (m % n1) := by
    have h1 : (r + i * n1) * a = d * ((r + i * n1) * a1) := by rw [ha1]; ring
    rw [h1, hn1, Nat.mul_mod_mul_left]
    congr 1
    have h2 : (r + i * n1) * a1 = r * a1 + (i * a1) * n1 := by ring
    rw [h2, Nat.add_mul_mod_self_right]
    exact hrm
  rw [hmod, hn1] at key
  unfold Far
  rcases key with k1 | k1
  · left; nlinarith
  · right; nlinarith
theorem lacz_lemma_5_2_values {a n : ℕ} (h0 : 0 < a) (han : a < n) (h3 : 3 * a ≤ n)
    (h : ∀ k : ℕ, Nat.Coprime k (2 * n) →
      3 * ((k * a) % n) ≤ n ∨ 2 * n ≤ 3 * ((k * a) % n)) :
    n = 3 * a ∨ n = 4 * a ∨ n = 6 * a ∨ n = 10 * a ∨ 10 * a = 3 * n := by
  obtain ⟨n1, hn1, hcases⟩ := lacz_lemma_5_2 h0 han h
  set d := Nat.gcd a n with hd
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left _ h0
  obtain ⟨a1, ha1⟩ : d ∣ a := Nat.gcd_dvd_left a n
  have hcop : Nat.Coprime a1 n1 := by
    have e1 : a / d = a1 := Nat.div_eq_of_eq_mul_right hdpos ha1
    have e2 : n / d = n1 := Nat.div_eq_of_eq_mul_right hdpos hn1
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := n) hdpos
    rwa [← hd, e1, e2] at this
  have ha1pos : 0 < a1 := by
    rcases Nat.eq_zero_or_pos a1 with h' | h'
    · rw [h'] at ha1; omega
    · exact h'
  have h3' : 3 * a1 ≤ n1 := by
    have e : 3 * a = d * (3 * a1) := by rw [ha1]; ring
    have : d * (3 * a1) ≤ d * n1 := by rw [← e, ← hn1]; exact h3
    exact Nat.le_of_mul_le_mul_left this hdpos
  rcases hcases with rfl | rfl | rfl | rfl
  · left
    have : a1 = 1 := by omega
    subst this; omega
  · right; left
    have : a1 = 1 := by omega
    subst this; omega
  · right; right; left
    have : a1 = 1 := by
      have hlt : a1 ≤ 2 := by omega
      interval_cases a1
      · rfl
      · exfalso; revert hcop; norm_num
    subst this; omega
  · have : a1 = 1 ∨ a1 = 3 := by
      have hlt : a1 ≤ 3 := by omega
      interval_cases a1
      · exact Or.inl rfl
      · exfalso; revert hcop; norm_num
      · exact Or.inr rfl
    rcases this with rfl | rfl
    · right; right; right; left; omega
    · right; right; right; right; omega
end Erdos634.Draft.LaczFormal
end

section
open scoped BigOperators
open Erdos634.LemmaKStar
namespace Erdos634.Draft.LaczFormal
variable {n : ℕ} {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ}
theorem yv_lt_one (k : ℤ) (i : Fin 3) (hn : 0 < n) : 0 ≤ yv n a k i ∧ yv n a k i < 1 := by
  unfold yv; exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
theorem yv_pos {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (i : Fin 3) (hai : 0 < a i) (hlt : a i < n) :
    0 < yv n a k i := by
  unfold yv
  rcases (Int.fract_nonneg (((k * (a i : ℤ) : ℤ) : ℚ) / n)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.mp h.symm
    have h1 : ((k * (a i : ℤ) : ℤ) : ℚ) = (m * n : ℤ) := by
      push_cast; push_cast at hm
      field_simp at hm; linarith
    have h2 : k * (a i : ℤ) = m * n := by exact_mod_cast h1
    have hcop : IsCoprime k (n : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr hk
    have hdvd : (n : ℤ) ∣ (a i : ℤ) := by
      have : (n : ℤ) ∣ k * (a i : ℤ) := ⟨m, by rw [h2]; ring⟩
      exact (hcop.symm).dvd_of_dvd_mul_left this
    have := Int.le_of_dvd (by exact_mod_cast hai) hdvd
    omega
theorem sT_eq_one_or_two {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i)
    (hsum : ∑ i, a i = n) : sT n a k = 1 ∨ sT n a k = 2 := by
  have hlt : ∀ i, a i < n := by
    intro i
    rw [← hsum, Fin.sum_univ_three]
    have := hpos 0; have := hpos 1; have := hpos 2
    fin_cases i <;> simp <;> omega
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hint : ∃ m : ℤ, sT n a k = m := by
    refine ⟨k - ∑ i, ⌊((k * (a i : ℤ) : ℤ) : ℚ) / n⌋, ?_⟩
    unfold sT yv
    simp only [Int.fract]
    rw [Finset.sum_sub_distrib]
    have : ∑ i, ((k * (a i : ℤ) : ℤ) : ℚ) / n = k := by
      rw [← Finset.sum_div]
      have : ∑ i, ((k * (a i : ℤ) : ℤ) : ℚ) = k * n := by
        push_cast
        rw [← Finset.mul_sum]
        have : ∑ i, (a i : ℚ) = n := by exact_mod_cast hsum
        rw [this]
      rw [this]; field_simp
    rw [this]; push_cast; ring
  obtain ⟨m, hm⟩ := hint
  have hlo : 0 < sT n a k := by
    unfold sT
    exact Finset.sum_pos (fun i _ => yv_pos hk hn i (hpos i) (hlt i)) ⟨0, Finset.mem_univ _⟩
  have hhi : sT n a k < 3 := by
    unfold sT
    calc ∑ i, yv n a k i < ∑ _i : Fin 3, (1 : ℚ) :=
          Finset.sum_lt_sum (fun i _ => (yv_lt_one k i hn).2.le) ⟨0, Finset.mem_univ _, (yv_lt_one k 0 hn).2⟩
      _ = 3 := by simp
  rw [hm] at hlo hhi ⊢
  have h1 : (0 : ℤ) < m := by exact_mod_cast hlo
  have h2 : m < 3 := by exact_mod_cast hhi
  have : m = 1 ∨ m = 2 := by omega
  rcases this with rfl | rfl
  · left; norm_num
  · right; norm_num
theorem xp_bounds {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i)
    (hsum : ∑ i, a i = n) (i : Fin 3) : 0 ≤ xp n a k i ∧ xp n a k i ≤ 1 := by
  have := yv_lt_one (a := a) k i hn
  unfold xp
  split_ifs
  · exact ⟨this.1, this.2.le⟩
  · constructor <;> linarith [this.2]
theorem R1_conj_eq {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i)
    (hsum : ∑ i, a i = n) (hK1 : K1 n a f k) (hK2 : K2 n a f k) :
    ∑ i, (FF f i : ℚ) * xp n a k i = 1 := by
  have hsw : ∑ i, (FF f i : ℚ) * xp n a k i = ∑ j, xpu n a f k j := by
    have : ∑ i, (FF f i : ℚ) * xp n a k i = ∑ j, ∑ i, (f j i : ℚ) * xp n a k i := by
      unfold FF
      push_cast
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    rw [this]
    exact Finset.sum_congr rfl (fun j _ => hK2 j)
  rw [hsw]
  unfold K1 at hK1
  rcases sT_eq_one_or_two hk hn hpos hsum with h1 | h2
  · have : ∑ j, xpu n a f k j = ∑ j, xv n a f k j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      unfold xpu; rw [if_pos h1]
    rw [this]; change sABC n a f k = 1
    rw [← hK1]; exact h1
  · have : ∑ j, xpu n a f k j = ∑ j, (1 - xv n a f k j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      unfold xpu; rw [if_neg (by rw [h2]; norm_num)]
    rw [this, Finset.sum_sub_distrib]
    have : ∑ j, xv n a f k j = 2 := by
      change sABC n a f k = 2
      rw [← hK1]; exact h2
    rw [this]; simp; norm_num
end Erdos634.Draft.LaczFormal
end

section
namespace Erdos634.Draft.LaczFormal
def pickOk (p r d2 d3 d5 i : ℕ) : Bool :=
  (decide (1 ≤ i)) && ((r + i) % p == 0) && (d2 == 0 || i % 2 != 0) && (d3 == 0 || i % 3 != 0) && (d5 == 0 || i % 5 != 0)
def feasB (p r d2 d3 d5 : ℕ) : Bool :=
  (d2 == 0 || p % 2 != 0 || r % 2 != 0) && (d3 == 0 || p % 3 != 0 || r % 3 != 0) && (d5 == 0 || p % 5 != 0 || r % 5 != 0)
def allChk : Bool :=
  (List.range 11).all fun p => !(p == 3 || p == 4 || p == 6 || p == 10) ||
    (List.range p).all fun r => (List.range 2).all fun d2 => (List.range 2).all fun d3 => (List.range 2).all fun d5 =>
      !feasB p r d2 d3 d5 || (List.range 20).any (pickOk p r d2 d3 d5)
theorem allChk_true : allChk = true := by decide +kernel
theorem pick_i_decide {p r d2 d3 d5 : ℕ} (hp11 : p < 11) (hp : p = 3 ∨ p = 4 ∨ p = 6 ∨ p = 10) (hr : r < p)
    (h2 : d2 < 2) (h3 : d3 < 2) (h5 : d5 < 2) (hf : feasB p r d2 d3 d5 = true) :
    (List.range 20).any (pickOk p r d2 d3 d5) = true := by
  have h := allChk_true
  unfold allChk at h
  rw [List.all_eq_true] at h
  have h1 := h p (List.mem_range.mpr hp11)
  have hp' : (p == 3 || p == 4 || p == 6 || p == 10) = true := by
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  rw [hp'] at h1
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have h6 := h1 r hr d2 h2 d3 h3 d5 h5
  rw [hf] at h6
  simpa using h6
theorem pick_i {p a b : ℕ} (hp : p = 3 ∨ p = 4 ∨ p = 6 ∨ p = 10)
    (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ a → ℓ ≤ 5) (hcop : Nat.Coprime a b) :
    ∃ i, 1 ≤ i ∧ i ≤ 19 ∧ p ∣ b + i ∧ Nat.Coprime i a := by
  have hpos : 0 < p := by rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hp11 : p < 11 := by rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hl : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ a → ℓ ∣ p → (b % p) % ℓ ≠ 0 := by
    intro ℓ hℓ hla hlp h0
    have h1 : ℓ ∣ b % p := Nat.dvd_of_mod_eq_zero h0
    have h2 : ℓ ∣ b := by
      have := Nat.mod_add_div b p
      rw [← this]
      exact dvd_add h1 (Dvd.dvd.mul_right hlp _)
    have h3 : ℓ ∣ Nat.gcd a b := Nat.dvd_gcd hla h2
    rw [hcop] at h3
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h3)
  have hfe : feasB p (b % p) (if 2 ∣ a then 1 else 0) (if 3 ∣ a then 1 else 0) (if 5 ∣ a then 1 else 0) = true := by
    unfold feasB
    have e2 := hl 2 Nat.prime_two
    have e3 := hl 3 Nat.prime_three
    have e5 := hl 5 Nat.prime_five
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · by_cases h : 2 ∣ a
      · by_cases hq : 2 ∣ p
        · right; exact e2 h hq
        · left; right; intro h0; exact hq (Nat.dvd_of_mod_eq_zero h0)
      · left; left; simp [h]
    · by_cases h : 3 ∣ a
      · by_cases hq : 3 ∣ p
        · right; exact e3 h hq
        · left; right; intro h0; exact hq (Nat.dvd_of_mod_eq_zero h0)
      · left; left; simp [h]
    · by_cases h : 5 ∣ a
      · by_cases hq : 5 ∣ p
        · right; exact e5 h hq
        · left; right; intro h0; exact hq (Nat.dvd_of_mod_eq_zero h0)
      · left; left; simp [h]
  have hany := pick_i_decide hp11 hp (Nat.mod_lt b hpos) (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
    (by split_ifs <;> norm_num) hfe
  rw [List.any_eq_true] at hany
  obtain ⟨i, hi, hok⟩ := hany
  rw [List.mem_range] at hi
  simp only [pickOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨hi1, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  refine ⟨i, hi1, by omega, ?_, ?_⟩
  · have hm : (b % p + i) ≡ b + i [MOD p] := (Nat.mod_modEq b p).add_right i
    have hd : p ∣ b % p + i := Nat.dvd_of_mod_eq_zero h1
    exact (hm.dvd_iff (dvd_refl p)).mp hd
  · apply Nat.coprime_of_dvd
    intro ℓ hℓ hli hla
    have h5 := hsm ℓ hℓ hla
    have hl2 : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 5 := by
      have h2' : 2 ≤ ℓ := hℓ.two_le
      interval_cases ℓ
      · simp
      · simp
      · exact absurd hℓ (by norm_num)
      · simp
    rcases hl2 with rfl | rfl | rfl
    · rcases h2 with h2 | h2
      · simp [hla] at h2
      · exact h2 (Nat.mod_eq_zero_of_dvd hli)
    · rcases h3 with h3 | h3
      · simp [hla] at h3
      · exact h3 (Nat.mod_eq_zero_of_dvd hli)
    · rcases h4 with h4 | h4
      · simp [hla] at h4
      · exact h4 (Nat.mod_eq_zero_of_dvd hli)
theorem Q_core {p a b i : ℕ} (hp : 0 < p) (ha : 0 < a) (hab : Nat.Coprime a b) (hdiv : p ∣ b + i)
    (hi : Nat.Coprime i a) :
    ∃ (k t w : ℤ), k = p * t - 1 ∧ k * b = i + ((p * a : ℕ) : ℤ) * w ∧ IsCoprime k ((p * a : ℕ) : ℤ) := by
  obtain ⟨s, hs⟩ := hdiv
  have hab' : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  obtain ⟨u, v, huv⟩ := hab'
  refine ⟨p * (s * v) - 1, s * v, -(s * u), rfl, ?_, ?_⟩
  · have hs' : (b : ℤ) + i = p * s := by exact_mod_cast hs
    push_cast
    linear_combination ((p:ℤ) * s) * huv - hs'
  · have hk1 : IsCoprime ((p:ℤ) * (s * v) - 1) (p : ℤ) := ⟨-1, s * v, by ring⟩
    have hia : IsCoprime (i : ℤ) (a : ℤ) := Nat.isCoprime_iff_coprime.mpr hi
    have hs' : (b : ℤ) + i = p * s := by exact_mod_cast hs
    have heq : ((p:ℤ) * (s * v) - 1) * b = i + a * (p * -(s * u)) := by
      linear_combination ((p:ℤ) * s) * huv - hs'
    have hkb : IsCoprime (((p:ℤ) * (s * v) - 1) * b) (a : ℤ) := by
      rw [heq]; exact hia.add_mul_left_left _
    have hk2 : IsCoprime ((p:ℤ) * (s * v) - 1) (a : ℤ) := hkb.of_mul_left_left
    push_cast
    exact hk1.mul_right hk2
end Erdos634.Draft.LaczFormal
end

section
open scoped BigOperators
open Erdos634.LemmaKStar Erdos634.LemmaF
namespace Erdos634.Draft.LaczFormal
variable {n : ℕ} {a : Fin 3 → ℕ}
theorem fract_of_eq (m c w : ℤ) (n : ℕ) (hn : 0 < n) (hc0 : 0 ≤ c) (hcn : c < n) (hm : m = c + n * w) :
    Int.fract ((m : ℚ) / n) = (c : ℚ) / n := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (m : ℚ) / n = (c : ℚ) / n + (w : ℚ) := by
    rw [hm]; push_cast; field_simp
  rw [this, Int.fract_add_intCast]
  apply Int.fract_eq_self.mpr
  constructor
  · positivity
  · rw [div_lt_one (by exact_mod_cast hn)]; exact_mod_cast hcn
theorem xp_le_third {F : Fin 3 → ℕ} {k : ℤ} (hk : Int.gcd k n = 1) (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i)
    (hsum : ∑ i, a i = n) (h : ∑ i, (F i : ℚ) * xp n a k i = 1) (i : Fin 3) (hF : 3 ≤ F i) :
    xp n a k i ≤ 1 / 3 := by
  rw [Fin.sum_univ_three] at h
  have b0 := xp_bounds hk hn hpos hsum 0
  have b1 := xp_bounds hk hn hpos hsum 1
  have b2 := xp_bounds hk hn hpos hsum 2
  have hF' : (3 : ℚ) ≤ F i := by exact_mod_cast hF
  have c0 : 0 ≤ (F 0 : ℚ) * xp n a k 0 := mul_nonneg (by positivity) b0.1
  have c1 : 0 ≤ (F 1 : ℚ) * xp n a k 1 := mul_nonneg (by positivity) b1.1
  have c2 : 0 ≤ (F 2 : ℚ) * xp n a k 2 := mul_nonneg (by positivity) b2.1
  have hi : (F i : ℚ) * xp n a k i ≤ 1 := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 by fin_cases i <;> simp) with rfl | rfl | rfl <;> linarith
  have hx := (xp_bounds hk hn hpos hsum i).1
  nlinarith
theorem four_values {F : Fin 3 → ℕ} (hn : 0 < n) (hpos : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n)
    (hFa : ∑ l, F l * a l = n) (hR : ∀ k : ℤ, Int.gcd k n = 1 → ∑ l, (F l : ℚ) * xp n a k l = 1)
    (i : Fin 3) (h3 : 3 ≤ F i) :
    n = 3 * a i ∨ n = 4 * a i ∨ n = 6 * a i ∨ n = 10 * a i ∨ 10 * a i = 3 * n := by
  have hle : F i * a i ≤ n := by
    rw [← hFa]
    exact Finset.single_le_sum (f := fun l => F l * a l) (fun l _ => Nat.zero_le _) (Finset.mem_univ i)
  have h3a : 3 * a i ≤ n := le_trans (Nat.mul_le_mul_right _ h3) hle
  have hai := hpos i
  refine lacz_lemma_5_2_values (by omega) (by omega) h3a ?_
  intro k hk
  have hk1 : Nat.Coprime k n := Nat.Coprime.coprime_dvd_right (Dvd.intro_left 2 rfl) hk
  have hkz : Int.gcd (k : ℤ) n = 1 := by rw [Int.gcd_natCast_natCast]; exact hk1
  have hb := xp_le_third hkz hn hpos hsum (hR (k : ℤ) hkz) i h3
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hy : yv n a (k : ℤ) i = (((k * a i) % n : ℕ) : ℚ) / n := by
    unfold yv
    have : (((k : ℤ) * (a i : ℤ) : ℤ) : ℚ) = ((k * a i : ℕ) : ℚ) := by push_cast; ring
    rw [this, Int.fract_div_natCast_eq_div_natCast_mod]
  unfold xp at hb
  split_ifs at hb
  · left
    rw [hy, div_le_iff₀ hn'] at hb
    have : (3 * (((k * a i) % n : ℕ) : ℚ)) ≤ n := by linarith
    exact_mod_cast this
  · right
    rw [hy] at hb
    have : (2 * n : ℚ) ≤ 3 * (((k * a i) % n : ℕ) : ℚ) := by
      have h1 : 2 / 3 ≤ (((k * a i) % n : ℕ) : ℚ) / n := by linarith
      rw [le_div_iff₀ hn'] at h1; linarith
    exact_mod_cast this
theorem gcd_one_of_all {i j r : Fin 3} (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) {g : ℕ} (hi : g ∣ a i) (hj : g ∣ a j) (hr : g ∣ a r) : g = 1 := by
  have hall : ∀ l, g ∣ a l := by
    intro l
    rcases cover i j r hij hir hjr l with rfl | rfl | rfl <;> assumption
  have : g ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
    Nat.dvd_gcd (hall 0) (Nat.dvd_gcd (hall 1) (hall 2))
  rw [hgcd] at this
  exact Nat.dvd_one.mp this
theorem claimQ {F : Fin 3 → ℕ} {i j r : Fin 3} (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hn : 200 < n) (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5) (hpos : ∀ l, 1 ≤ a l)
    (hsum : ∑ l, a l = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hFi : F i * a i = n) (hFj : F j = 0) (hFr : F r = 0) (hp : F i = 3 ∨ F i = 4 ∨ F i = 6 ∨ F i = 10)
    (hR : ∀ k : ℤ, Int.gcd k n = 1 → ∑ l, (F l : ℚ) * xp n a k l = 1) : False := by
  set p := F i with hpdef
  have hp3 : 3 ≤ p := by rcases hp with h | h | h | h <;> omega
  have hp10 : p ≤ 10 := by rcases hp with h | h | h | h <;> omega
  have hai21 : 21 ≤ a i := by
    by_contra hlt
    push_neg at hlt
    have : p * a i ≤ 10 * 20 := Nat.mul_le_mul hp10 (by omega)
    omega
  have hsa : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ a i → ℓ ≤ 5 := fun ℓ hℓ hd =>
    hsm ℓ hℓ (dvd_trans hd (Dvd.intro_left p hFi))
  have hs3 : a i + a j + a r = n := by rw [← hsum]; exact (sum3 a hij hir hjr).symm
  have hain : a i ∣ n := Dvd.intro_left p hFi
  have hcop : Nat.Coprime (a i) (a j) := by
    have hgi : Nat.gcd (a i) (a j) ∣ a i := Nat.gcd_dvd_left _ _
    have hgj : Nat.gcd (a i) (a j) ∣ a j := Nat.gcd_dvd_right _ _
    have hsumij : Nat.gcd (a i) (a j) ∣ a i + a j := dvd_add hgi hgj
    have hn' : Nat.gcd (a i) (a j) ∣ n := dvd_trans hgi hain
    have hgr : Nat.gcd (a i) (a j) ∣ a r := by
      rw [← hs3] at hn'
      exact (Nat.dvd_add_right hsumij).mp (by simpa [add_assoc] using hn')
    exact gcd_one_of_all hij hir hjr hgcd hgi hgj hgr
  obtain ⟨i0, hi1, hi19, hdiv, hi0⟩ := pick_i (p := p) (a := a i) (b := a j) hp hsa hcop
  obtain ⟨k, t, w, hk, hkb, hkc⟩ := Q_core (by omega) (by omega) hcop hdiv hi0
  have hn0 : 0 < n := by omega
  have hcast : ((p * a i : ℕ) : ℤ) = (n : ℤ) := by exact_mod_cast hFi
  rw [hcast] at hkb hkc
  have hkg : Int.gcd k n = 1 := Int.isCoprime_iff_gcd_eq_one.mp hkc
  have hnp' : (p : ℤ) * a i = n := by exact_mod_cast hFi
  have hp3Z : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hAZ : (21 : ℤ) ≤ a i := by exact_mod_cast hai21
  have hAn : (a i : ℤ) + 2 * a i ≤ n := by nlinarith
  have h1 : k * (a i : ℤ) = n * t - a i := by rw [hk]; linear_combination t * hnp'
  have h2 : k * (a j : ℤ) = i0 + n * w := hkb
  have hyi : yv n a k i = ((n - a i : ℤ) : ℚ) / n := by
    unfold yv
    refine fract_of_eq _ _ (t - 1) n hn0 (by omega) (by omega) ?_
    rw [h1]; ring
  have hyj : yv n a k j = (i0 : ℚ) / n := by
    unfold yv
    have := fract_of_eq (k * a j) (i0 : ℤ) w n hn0 (by omega) (by omega) h2
    simpa using this
  have har : (a r : ℤ) = n - a i - a j := by omega
  have hyr : yv n a k r = ((a i - i0 : ℤ) : ℚ) / n := by
    unfold yv
    refine fract_of_eq _ _ (k - t - w) n hn0 (by omega) (by omega) ?_
    rw [har]
    calc k * ((n : ℤ) - a i - a j) = n * k - k * a i - k * a j := by ring
      _ = (a i - i0) + n * (k - t - w) := by rw [h1, h2]; ring
  have hsT : sT n a k = 1 := by
    unfold sT
    rw [sum3 (fun l => yv n a k l) hij hir hjr, hyi, hyj, hyr]
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
    field_simp
    push_cast
    ring
  have hxp : ∀ l, xp n a k l = yv n a k l := fun l => by unfold xp; rw [if_pos hsT]
  have h := hR k hkg
  rw [sum3 (fun l => (F l : ℚ) * xp n a k l) hij hir hjr, hFj, hFr, hxp i, hyi] at h
  have hnq : (n : ℚ) = p * a i := by exact_mod_cast hFi.symm
  have hai' : (a i : ℚ) ≠ 0 := by exact_mod_cast (by omega : a i ≠ 0)
  have hp3' : (3 : ℚ) ≤ p := by exact_mod_cast hp3
  push_cast at h
  rw [hnq] at h
  field_simp at h
  nlinarith
theorem big_div {F : Fin 3 → ℕ} {i j r : Fin 3} (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hn : 200 < n) (hpos : ∀ l, 1 ≤ a l) (hsum : ∑ l, a l = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hFa : ∑ l, F l * a l = n) (hR : ∀ k : ℤ, Int.gcd k n = 1 → ∑ l, (F l : ℚ) * xp n a k l = 1)
    (hFr : F r = 0) (h3 : 3 ≤ F i) : ∃ D, n ≤ 10 * D ∧ D ∣ a i ∧ D ∣ F j := by
  have hn0 : 0 < n := by omega
  have hFa2 : F i * a i + F j * a j = n := by
    rw [sum3 (fun l => F l * a l) hij hir hjr, hFr] at hFa; simpa using hFa
  have hs3 : a i + a j + a r = n := by rw [← hsum]; exact (sum3 a hij hir hjr).symm
  have hv := four_values hn0 hpos hsum hFa hR i h3
  obtain ⟨D, hD10, hDa, hDn⟩ : ∃ D, n ≤ 10 * D ∧ D ∣ a i ∧ D ∣ n := by
    rcases hv with h | h | h | h | h
    · exact ⟨a i, by omega, dvd_refl _, ⟨3, by omega⟩⟩
    · exact ⟨a i, by omega, dvd_refl _, ⟨4, by omega⟩⟩
    · exact ⟨a i, by omega, dvd_refl _, ⟨6, by omega⟩⟩
    · exact ⟨a i, by omega, dvd_refl _, ⟨10, by omega⟩⟩
    · exact ⟨n / 10, by omega, ⟨3, by omega⟩, ⟨10, by omega⟩⟩
  refine ⟨D, hD10, hDa, ?_⟩
  have hDF : D ∣ F j * a j := by
    have h1 : D ∣ F i * a i := Dvd.dvd.mul_left hDa _
    rw [← hFa2] at hDn
    exact (Nat.dvd_add_right h1).mp hDn
  have hcop : Nat.Coprime D (a j) := by
    have hgi : Nat.gcd D (a j) ∣ a i := dvd_trans (Nat.gcd_dvd_left _ _) hDa
    have hgj : Nat.gcd D (a j) ∣ a j := Nat.gcd_dvd_right _ _
    have hn' : Nat.gcd D (a j) ∣ n := dvd_trans (Nat.gcd_dvd_left _ _) hDn
    have hgr : Nat.gcd D (a j) ∣ a r := by
      rw [← hs3] at hn'
      exact (Nat.dvd_add_right (dvd_add hgi hgj)).mp hn'
    exact gcd_one_of_all hij hir hjr hgcd hgi hgj hgr
  exact hcop.dvd_of_dvd_mul_right hDF
theorem no_big {F : Fin 3 → ℕ} {i j r : Fin 3} (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r)
    (hn : 200 < n) (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5) (hpos : ∀ l, 1 ≤ a l)
    (hsum : ∑ l, a l = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hFa : ∑ l, F l * a l = n) (hR : ∀ k : ℤ, Int.gcd k n = 1 → ∑ l, (F l : ℚ) * xp n a k l = 1)
    (hFr : F r = 0) (h3 : 3 ≤ F i) : False := by
  have hn0 : 0 < n := by omega
  have hFa2 : F i * a i + F j * a j = n := by
    rw [sum3 (fun l => F l * a l) hij hir hjr, hFr] at hFa; simpa using hFa
  obtain ⟨D, hD10, hDa, hDF⟩ := big_div hij hir hjr hn hpos hsum hgcd hFa hR hFr h3
  rcases Nat.eq_zero_or_pos (F j) with hFj | hFj
  · 
    rw [hFj] at hFa2
    have hFi : F i * a i = n := by simpa using hFa2
    have hv := four_values hn0 hpos hsum hFa hR i h3
    have hai := hpos i
    have hp : F i = 3 ∨ F i = 4 ∨ F i = 6 ∨ F i = 10 := by
      rcases hv with h | h | h | h | h
      · left; exact Nat.eq_of_mul_eq_mul_right hai (by rw [hFi]; omega)
      · right; left; exact Nat.eq_of_mul_eq_mul_right hai (by rw [hFi]; omega)
      · right; right; left; exact Nat.eq_of_mul_eq_mul_right hai (by rw [hFi]; omega)
      · right; right; right; exact Nat.eq_of_mul_eq_mul_right hai (by rw [hFi]; omega)
      · exfalso
        have h1 : 10 * (F i * a i) = F i * (10 * a i) := by ring
        rw [hFi, h] at h1
        have h2 : n * 10 = n * (F i * 3) := by linarith
        have h3' := Nat.eq_of_mul_eq_mul_left hn0 h2
        omega
    exact claimQ hij hir hjr hn hsm hpos hsum hgcd hFi hFj hFr hp hR
  · have hDle : D ≤ F j := Nat.le_of_dvd hFj hDF
    have h3j : 3 ≤ F j := by omega
    obtain ⟨D', hD'10, hD'a, hD'F⟩ := big_div hij.symm hjr hir hn hpos hsum hgcd hFa hR hFr h3j
    have hFi : 0 < F i := by omega
    have h1 : D' ≤ F i := Nat.le_of_dvd hFi hD'F
    have h2 : D ≤ a i := Nat.le_of_dvd (hpos i) hDa
    have h4 : D' * D ≤ n := le_trans (Nat.mul_le_mul h1 h2) (le_trans (Nat.le_add_right _ _) hFa2.le)
    nlinarith
theorem shapes_of_K_uniform {f : Fin 3 → Fin 3 → ℕ} (hn : 200 < n) (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5)
    (hpos : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n) (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (hf : ∀ j, f j ≠ 0) (hu : ∑ j, uu a f j = n)
    (hK : ∀ k : ℤ, Int.gcd k n = 1 → K1 n a f k ∧ K2 n a f k) :
    LemmaF.Similar a f ∨ HalfIso n a f := by
  have hn0 : 0 < n := by omega
  have hFa : ∑ l, FF f l * a l = n := by
    rw [← hu]
    simp only [uu, FF, Finset.sum_mul]
    exact Finset.sum_comm
  have hR : ∀ k : ℤ, Int.gcd k n = 1 → ∑ l, (FF f l : ℚ) * xp n a k l = 1 := fun k hk =>
    R1_conj_eq hk hn0 hpos hsum (hK k hk).1 (hK k hk).2
  by_cases hz : ∃ r, FF f r = 0
  · obtain ⟨r, hr⟩ := hz
    have key : ∀ {i j r : Fin 3}, i ≠ j → i ≠ r → j ≠ r → FF f r = 0 → LemmaF.Similar a f ∨ HalfIso n a f := by
      intro i j r hij hir hjr hFr
      have hFa2 : FF f i * a i + FF f j * a j = n := by
        rw [sum3 (fun l => FF f l * a l) hij hir hjr, hFr] at hFa; simpa using hFa
      have hs3 : a i + a j + a r = n := by rw [← hsum]; exact (sum3 a hij hir hjr).symm
      have hFi2 : FF f i ≤ 2 := by
        by_contra h; push_neg at h
        exact no_big hij hir hjr hn hsm hpos hsum hgcd hFa hR hFr h
      have hFj2 : FF f j ≤ 2 := by
        by_contra h; push_neg at h
        exact no_big hij.symm hjr hir hn hsm hpos hsum hgcd hFa hR hFr h
      have hm := mass_ge hf
      rw [sum3 (FF f) hij hir hjr, hFr] at hm
      have hcases : (FF f i = 2 ∧ FF f j = 1) ∨ (FF f i = 1 ∧ FF f j = 2) ∨ (FF f i = 2 ∧ FF f j = 2) := by omega
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        have hM : ∑ l, FF f l = 3 := by rw [sum3 (FF f) hij hir hjr, hFr, h1, h2]
        intro x
        rw [count_mass3 hf hM x, sum3 (fun l => FF f l * (if a l = x then 1 else 0)) hij hir hjr, hFr, h1, h2, sum3 (fun l => if a l = x then 1 else 0) hij hir hjr]
        rw [h1, h2] at hFa2
        have : a r = a i := by omega
        rw [this]
        split_ifs <;> omega
      · left
        have hM : ∑ l, FF f l = 3 := by rw [sum3 (FF f) hij hir hjr, hFr, h1, h2]
        intro x
        rw [count_mass3 hf hM x, sum3 (fun l => FF f l * (if a l = x then 1 else 0)) hij hir hjr, hFr, h1, h2, sum3 (fun l => if a l = x then 1 else 0) hij hir hjr]
        rw [h1, h2] at hFa2
        have : a r = a j := by omega
        rw [this]
        split_ifs <;> omega
      · rw [h1, h2] at hFa2
        exact right_case hij hir hjr (by omega) (by omega) hf hFr h1 h2
    have hr3 : r = 0 ∨ r = 1 ∨ r = 2 := by fin_cases r <;> simp
    rcases hr3 with rfl | rfl | rfl
    · exact key (i := 1) (j := 2) (by decide) (by decide) (by decide) hr
    · exact key (i := 0) (j := 2) (by decide) (by decide) (by decide) hr
    · exact key (i := 0) (j := 1) (by decide) (by decide) (by decide) hr
  · push_neg at hz
    left
    have hge : ∀ l, a l ≤ FF f l * a l := fun l => Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (hz l))
    have hsum' := hsum
    rw [Fin.sum_univ_three] at hsum' hFa
    have e0 := hge 0; have e1 := hge 1; have e2 := hge 2
    have hall : ∀ l, FF f l = 1 := by
      intro l
      have hl : FF f l * a l = a l := by
        fin_cases l <;> simp <;> omega
      exact Nat.eq_of_mul_eq_mul_right (hpos l) (by simpa using hl)
    have hM : ∑ l, FF f l = 3 := by simp [hall]
    intro x
    rw [count_mass3 hf hM x]
    simp [hall]
end Erdos634.Draft.LaczFormal
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
open scoped BigOperators Classical
open Erdos634.Geometry Erdos634.LemmaKStar Erdos634.LemmaF Erdos634.KConj Erdos634.CaseA.R0c Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi)
namespace Erdos634.Draft.LaczFormal
theorem l9_uniform {N : ℕ} (D : CongruentDissection N) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (h200 : 200 < n) (hsm : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → ℓ ≤ 5) :
    SimilarTM D ∨
      ∃ k l : Fin 3, l ≠ k ∧ D.model.angleAt k = Real.pi / 2 ∧
        ∃ j₁ j₂ : Fin 3, j₁ ≠ j₂ ∧ D.target.angleAt j₁ = D.model.angleAt l ∧
          D.target.angleAt j₂ = D.model.angleAt l := by
  obtain ⟨idx, hidx⟩ := exists_idx D a ha
  obtain ⟨hf, hK⟩ := lemmaK D hn a ha idx hidx
  set f := fig D idx
  have hsum := sum_of_angles hn ha
  have hsu := sum_of_angles hn hf
  have ha1 : ∀ i, 1 ≤ a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have hu1 : ∀ j, 1 ≤ uu a f j := fun j =>
    (nat_bounds hn (hf j) (angle_pos _ j) (angle_lt_pi _ j)).1
  have hfne : ∀ j, f j ≠ 0 := by
    intro j h
    have := hu1 j
    rw [uu, h] at this; simp at this
  rcases shapes_of_K_uniform h200 hsm ha1 hsum hgcd hfne hsu hK with hsim | ⟨k, l, hk, hlk, j₁, j₂, hj, h1, h2⟩
  · left
    obtain ⟨τ, hτ⟩ := perm_of_counts (uu a f) a hsim
    have hang : ∀ j, D.target.angleAt j = D.model.angleAt (τ j) := by
      intro j; rw [hf j, ha (τ j), hτ j]
    set μ := A1Field.circD D.target / A1Field.circD D.model
    have hcm := (A1Field.circD_pos D.model).ne'
    refine ⟨μ, τ, fun j => ⟨hang j, ?_⟩⟩
    rw [A1Field.oppLen_eq D.target j, A1Field.oppLen_eq D.model (τ j), hang j]
    simp only [μ]; field_simp
  · right
    have hmk : D.model.angleAt k = Real.pi / 2 := by
      rw [ha k]
      have : (2 * a k : ℝ) = n := by exact_mod_cast hk
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp; linarith
    refine ⟨k, l, hlk, hmk, j₁, j₂, hj, ?_, ?_⟩
    · rw [hf j₁, h1, ha l]
    · rw [hf j₂, h2, ha l]
end Erdos634.Draft.LaczFormal
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


set_option maxHeartbeats 4000000 in
/-- Step H3 of erdos-634.R1.H3.R1: n is 5-smooth and n > 200. -/
theorem OMA.solution : OMA.R_erdos_634_R1_H3_R1.H3 := by
  intro p hp hgt T Ts hc hd hu t hi n a hn ha hg hs h200
  rcases Erdos634.Draft.LaczFormal.l9_uniform (OMA.E634S.mk T Ts hc hd hu t) hn a ha hg h200 hs with
    hS | ⟨k, l, hlk, hk, j₁, j₂, hj, h1, h2⟩
  · obtain ⟨μ, τ, h⟩ := hS
    exact ⟨τ, fun k => (h k).1⟩
  · exact absurd ⟨j₁, j₂, hj, h1.trans h2.symm⟩ hi
