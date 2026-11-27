import OMAReductions.R_erdos_634_R1_H4_R1

/-!
# Erdos 634, step R1.H4.R1.H1: the classification of Laczkovich (1995, Theorem 4.1)

Flattened from the Lean port of Beeson-Rosu / Bonfioli (formalizations of the triangle tiling
papers), restricted to the declarations this step uses.
-/

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
theorem tile_subset_target (D : Dissection N) (j : Fin N) :
    (D.tile j).carrier ⊆ D.target.carrier := by
  rw [← D.covers]; exact Set.subset_iUnion (fun i => (D.tile i).carrier) j
noncomputable def Tri.basis (T : Tri) : AffineBasis (Fin 3) ℝ Plane :=
  AffineBasis.mk T.pts T.indep (by
    have := T.affineSpan_eq_top
    rwa [Tri.carrier, affineSpan_convexHull] at this)
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
noncomputable def Tri.det (T : Tri) : ℝ :=
  (T.pts 1 - T.pts 0) 0 * (T.pts 2 - T.pts 0) 1 - (T.pts 1 - T.pts 0) 1 * (T.pts 2 - T.pts 0) 0
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
end Erdos634.Geometry
end

section
namespace Erdos634.Geometry
open MeasureTheory Set
theorem cross_sub_right (u a b : Plane) : cross u (a - b) = cross u a - cross u b := by
  simp only [cross, PiLp.sub_apply]; ring
theorem cross_smul_left (t : ℝ) (u v : Plane) : cross (t • u) v = t * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring
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
theorem Tri.Congruent.dist_eq {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i j, dist (T.pts i) (T.pts j) = dist (U.pts (σ i)) (U.pts (σ j)) := by
  obtain ⟨f, σ, hf⟩ := h
  exact ⟨σ, fun i j => by rw [← hf i, ← hf j, f.dist_eq]⟩
structure CongruentDissection (N : ℕ) extends Dissection N where
  model : Tri
  tiles_congruent : ∀ i, (tile i).Congruent model
namespace CongruentDissection
variable {N : ℕ}
end CongruentDissection
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
theorem pin_angle_sum_interior {N : ℕ} (D : Dissection N) {p : Plane}
    (hp : p ∈ interior D.target.carrier) :
    ∑ i, (D.tile i).localAngle p = 2 * Real.pi := by
  rw [D.sum_localAngle_eq p, D.target.localAngle_interior hp]
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
namespace Erdos634.VertexFigureReal
open Erdos634.Geometry Finset
theorem sum_by_value {N : ℕ} (S : Finset ℝ) (f : Fin N → ℝ) (h : ∀ i, f i ∈ S) :
    ∑ i, f i = ∑ v ∈ S, (({i | f i = v} : Finset (Fin N)).card : ℝ) * v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (fun i _ => h i) f]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const,
    nsmul_eq_mul]
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
theorem corner_angle_sum {N : ℕ} (D : Dissection N) (k : Fin 3) :
    ∑ i, (D.tile i).localAngle (D.target.pts k)
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) := by
  rw [D.sum_localAngle_eq (D.target.pts k), D.target.localAngle_vertex k]
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
end Erdos634.Geometry.Dissection
end

section
namespace Erdos634.RouteOne
open Erdos634.Geometry
theorem Tri.carrier_eq_closure_interior (T : Tri) :
    T.carrier = closure (interior T.carrier) := by
  have hconv : Convex ℝ T.carrier := by
    rw [Erdos634.Geometry.Tri.carrier]; exact convex_convexHull ℝ _
  have hne : (interior T.carrier).Nonempty := Erdos634.Geometry.Tri.interior_nonempty T
  have hclosed : IsClosed T.carrier := (Erdos634.Geometry.Tri.isCompact T).isClosed
  rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne, hclosed.closure_eq]
theorem Dissection.not_mem_interior_of_mem {N : ℕ} (D : Dissection N) {i j : Fin N}
    (hij : i ≠ j) {x : Plane} (hx : x ∈ (D.tile i).carrier) :
    x ∉ interior (D.tile j).carrier := by
  intro hxj
  have hx' : x ∈ closure (interior (D.tile i).carrier) := by
    rw [← Tri.carrier_eq_closure_interior]; exact hx
  obtain ⟨y, hyi, hyj⟩ :=
    mem_closure_iff.mp hx' (interior (D.tile j).carrier) isOpen_interior hxj
  exact Set.disjoint_left.mp (D.interiors_disjoint hij) hyj hyi
end Erdos634.RouteOne
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
theorem Tri.Congruent.corner_count_eq_one {T U : Tri} (h : T.Congruent U)
    (hdist : ∀ k l : Fin 3,
      cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))
        = cornerAngle (T.pts (l + 1)) (T.pts l) (T.pts (l + 2)) → k = l)
    (k : Fin 3) :
    ({j | cornerAngle (U.pts (j + 1)) (U.pts j) (U.pts (j + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2))} : Finset (Fin 3)).card = 1 := by
  classical
  obtain ⟨σ, hperm⟩ := h.cornerAngle_perm
  refine Finset.card_eq_one.mpr ⟨σ k, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    have hm := hperm (σ.symm j)
    rw [Equiv.apply_symm_apply] at hm
    have : cornerAngle (T.pts (σ.symm j + 1)) (T.pts (σ.symm j)) (T.pts (σ.symm j + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) := by rw [← hm]; exact hj
    have hk := hdist _ _ this
    rw [← hk, Equiv.apply_symm_apply]
  · intro hj; subst hj; exact hperm k
theorem congruentDissection_corner_total {N : ℕ} (D : CongruentDissection N)
    (hdist : ∀ k l : Fin 3,
      cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
        = cornerAngle (D.model.pts (l + 1)) (D.model.pts l) (D.model.pts (l + 2)) → k = l)
    (k : Fin 3) :
    ∑ i : Fin N, ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j)
          ((D.tile i).pts (j + 2))
        = cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))}
        : Finset (Fin 3)).card = N := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => ((D.tiles_congruent i).symm).corner_count_eq_one hdist k)]
  simp
open Classical in
noncomputable def cornerPts {N : ℕ} (D : Dissection N) : Finset Plane :=
  Finset.univ.biUnion (fun i : Fin N => Finset.univ.image (fun j : Fin 3 => (D.tile i).pts j))
theorem mem_cornerPts {N : ℕ} (D : Dissection N) (i : Fin N) (j : Fin 3) :
    (D.tile i).pts j ∈ cornerPts D := by
  classical
  refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
theorem tile_corner_card {N : ℕ} (D : Dissection N) (i : Fin N) (θ : ℝ)
    (h0 : θ ≠ 0) (hpi : θ ≠ Real.pi) (h2pi : θ ≠ 2 * Real.pi) :
    ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = θ}
        : Finset (Fin 3)).card
      = ({v ∈ cornerPts D | (D.tile i).localAngle v = θ} : Finset Plane).card := by
  classical
  have himg : ({v ∈ cornerPts D | (D.tile i).localAngle v = θ} : Finset Plane)
      = ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = θ}
          : Finset (Fin 3)).image (D.tile i).pts := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hang⟩
      rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with
        ⟨j, hj, hval⟩ | h | h | h
      · exact ⟨j, by rw [← hval]; exact hang, hj.symm⟩
      · exact absurd (h ▸ hang) (Ne.symm h2pi)
      · exact absurd (h ▸ hang) (Ne.symm hpi)
      · exact absurd (h ▸ hang) (Ne.symm h0)
    · rintro ⟨j, hj, rfl⟩
      exact ⟨mem_cornerPts D i j, by rw [Erdos634.Geometry.Tri.localAngle_vertex]; exact hj⟩
  rw [himg, Finset.card_image_of_injective _ (D.tile i).indep.injective]
theorem corner_double_count {N : ℕ} (D : Dissection N) (θ : ℝ)
    (h0 : θ ≠ 0) (hpi : θ ≠ Real.pi) (h2pi : θ ≠ 2 * Real.pi) :
    ∑ i : Fin N,
        ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2)) = θ}
          : Finset (Fin 3)).card
      = ∑ v ∈ cornerPts D, ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card := by
  classical
  rw [Finset.sum_congr rfl (fun i _ => tile_corner_card D i θ h0 hpi h2pi)]
  simp only [Finset.card_filter]
  exact Finset.sum_comm
theorem congruentDissection_corner_balance {N : ℕ} (D : CongruentDissection N)
    (hdist : ∀ k l : Fin 3,
      cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
        = cornerAngle (D.model.pts (l + 1)) (D.model.pts l) (D.model.pts (l + 2)) → k = l)
    (k : Fin 3)
    (h0 : cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) ≠ 0)
    (hpi : cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) ≠ Real.pi)
    (h2pi : cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
      ≠ 2 * Real.pi) :
    ∑ v ∈ cornerPts D.toDissection,
        ({i | (D.tile i).localAngle v
          = cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))}
          : Finset (Fin N)).card = N := by
  classical
  rw [← corner_double_count D.toDissection _ h0 hpi h2pi]
  exact congruentDissection_corner_total D hdist k
theorem congruentDissection_localAngle_mem_all {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (v : Plane) (i : Fin N) :
    (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 2 * Real.pi, 0} : Finset ℝ) := by
  classical
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) v with
    ⟨j, -, hval⟩ | h2pi | hpi | h0
  · obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
    rw [hval, hk]
    have hall : ∀ m : Fin 3, m = 0 ∨ m = 1 ∨ m = 2 := by decide
    have hk3 := hall k
    rcases hk3 with rfl | rfl | rfl
    · rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hα]; simp
    · rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, hβ]; simp
    · rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, hγ]; simp
  · rw [h2pi]; simp
  · rw [hpi]; simp
  · rw [h0]; simp
theorem congruentDissection_localAngle_mem_at_corner {N : ℕ} (D : CongruentDissection N)
    (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    {v : Plane} (j : Fin N) (m : Fin 3) (hvj : (D.tile j).pts m = v) (i : Fin N) :
    (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
  classical
  have hmemj : v ∈ (D.tile j).carrier := by
    rw [← hvj, Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨m, rfl⟩
  have hnotint : v ∉ interior (D.tile i).carrier := by
    by_cases hij : i = j
    · subst hij; rw [← hvj]; exact _root_.Erdos634.Geometry.Dissection.target_vertex_not_interior _ m
    · exact fun hint =>
        Erdos634.RouteOne.Dissection.not_mem_interior_of_mem D.toDissection (Ne.symm hij) hmemj hint
  have h2pi := _root_.Erdos634.Geometry.Dissection.localAngle_ne_two_pi_of_not_mem_interior hnotint
  have hmem := congruentDissection_localAngle_mem_all D α β γ hmα hmβ hmγ v i
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
  rcases hmem with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact absurd h h2pi
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
theorem vertex_of_localAngle_corner (T : Tri) {v : Plane} {θ : ℝ} (h : T.localAngle v = θ)
    (h0 : θ ≠ 0) (hpi : θ ≠ Real.pi) (h2pi : θ ≠ 2 * Real.pi) :
    ∃ m : Fin 3, T.pts m = v := by
  classical
  rcases Erdos634.PinPlumbing.localAngle_cases T v with ⟨m, hm, -⟩ | hb | hb | hb
  · exact ⟨m, hm.symm⟩
  · exact absurd (h.symm.trans hb) h2pi
  · exact absurd (h.symm.trans hb) hpi
  · exact absurd (h.symm.trans hb) h0
theorem localAngle_at_own_vertex_mem {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (j : Fin N) (m : Fin 3) :
    (D.tile j).localAngle ((D.tile j).pts m) = α ∨
    (D.tile j).localAngle ((D.tile j).pts m) = β ∨
    (D.tile j).localAngle ((D.tile j).pts m) = γ := by
  rw [Erdos634.Geometry.Tri.localAngle_vertex]
  obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent j).symm m
  rw [hk]
  have hall : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  rcases hall k with rfl | rfl | rfl
  · left
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl]
    exact hmα
  · right; left
    rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl]
    exact hmβ
  · right; right
    rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl]
    exact hmγ
theorem cornerPts_trichotomy {N : ℕ} (D : Dissection N) {v : Plane} (hv : v ∈ cornerPts D) :
    v ∈ Set.range D.target.pts ∨
    (v ∈ frontier D.target.carrier ∧ v ∉ Set.range D.target.pts) ∨
    v ∈ interior D.target.carrier := by
  classical
  have hvt : v ∈ D.target.carrier := by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hi
    refine tile_subset_target D i ?_
    rw [← hm, Erdos634.Geometry.Tri.carrier]; exact subset_convexHull ℝ _ ⟨m, rfl⟩
  by_cases hint : v ∈ interior D.target.carrier
  · exact Or.inr (Or.inr hint)
  · have hfr : v ∈ frontier D.target.carrier := by
      rw [(D.target.isCompact.isClosed).frontier_eq]
      exact ⟨hvt, hint⟩
    by_cases hcorner : v ∈ Set.range D.target.pts
    · exact Or.inl hcorner
    · exact Or.inr (Or.inl ⟨hfr, hcorner⟩)
end Erdos634.Geometry
end

section
namespace Erdos634.CertNode
open Erdos634.Geometry
theorem pts_injective (T : Tri) : Function.Injective T.pts := T.indep.injective
end Erdos634.CertNode
end

section
open scoped Classical
namespace Erdos634.Geometry
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
end Erdos634.Geometry.Row3.RP
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
open scoped Classical
namespace Erdos634.Geometry
def Tri.TwoAlphaData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = Real.pi - 3 * α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * α ∧ T.oppLen (σ 2) = c
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
end Erdos634.Geometry.CaseA.LemmaV
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
namespace Erdos634.Geometry.A1Field
open Erdos634.Geometry
open Erdos634.Geometry.CaseA.LemmaV (angle_pos angle_lt_pi)
variable {N : ℕ}
theorem sin_angle_pos (T : Tri) (k : Fin 3) : 0 < Real.sin (T.angleAt k) :=
  Real.sin_pos_of_pos_of_lt_pi (angle_pos T k) (angle_lt_pi T k)
end Erdos634.Geometry.A1Field
end

section
open scoped Classical
namespace Erdos634.Geometry
def Tri.TwoPiThreeData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = Real.pi / 3 - α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = 2 * Real.pi / 3 ∧ T.oppLen (σ 2) = c
end Erdos634.Geometry
end

section
open scoped Classical
namespace Erdos634.Geometry
variable {N : ℕ}
def Tri.SixtyData (T : Tri) (α a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    T.angleAt (σ 0) = α ∧ T.oppLen (σ 0) = a ∧
    T.angleAt (σ 1) = 2 * Real.pi / 3 - α ∧ T.oppLen (σ 1) = b ∧
    T.angleAt (σ 2) = Real.pi / 3 ∧ T.oppLen (σ 2) = c
end Erdos634.Geometry
end

section
namespace Erdos634.Draft.LemmaCShapes
def TA (θ : Fin 3 → ℝ) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), θ (σ 0) = x ∧ θ (σ 1) = y ∧ θ (σ 2) = z
theorem ta_of_idx (θ : Fin 3 → ℝ) (x y z : ℝ) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hx : θ i = x) (hy : θ j = y) (hz : θ l = z) : TA θ x y z := by
  have key : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → Function.Bijective ![i, j, l] := by decide
  refine ⟨Equiv.ofBijective _ (key i j l hij hil hjl), ?_, ?_, ?_⟩
  · simpa using hx
  · simpa using hy
  · simpa using hz
theorem fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
set_option maxHeartbeats 4000000 in
theorem shapes_threeTwo (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = 2 * w + v) (hrel : 3 * w + 2 * v = Real.pi)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    TA θ v v (3 * w) ∨
    TA θ (w + v) (w + v) w ∨
    TA θ (2 * w) v (w + v) ∨
    TA θ (2 * w) w (2 * v) ∨
    TA θ w w (w + 2 * v) ∨
    TA θ w v u := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1 ∨ Q 0 = 2) with e0 | e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2 ∨ R 0 = 3) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      obtain e2 : Q 1 = 1 := by omega
      obtain e3 : R 1 = 0 := by omega
      obtain e4 : Q 2 = 1 := by omega
      obtain e5 : R 2 = 0 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1 ∨ R 0 = 2) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      obtain e2 : Q 1 = 0 := by omega
      rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 2 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      obtain e2 : Q 1 = 0 := by omega
      obtain e3 : R 1 = 1 := by omega
      obtain e4 : Q 2 = 0 := by omega
      obtain e5 : R 2 = 1 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
set_option maxHeartbeats 4000000 in
theorem shapes_twoAlpha (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = 2 * w) (hv : v = Real.pi - 3 * w)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 1) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    TA θ w w (v + w) ∨
    TA θ w v u := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1) with e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2) with e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      obtain e2 : Q 1 = 0 := by omega
      rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 2 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
    · 
      obtain e2 : Q 1 = 0 := by omega
      obtain e3 : R 1 = 1 := by omega
      obtain e4 : Q 2 = 0 := by omega
      obtain e5 : R 2 = 1 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
set_option maxHeartbeats 4000000 in
theorem shapes_right (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = Real.pi / 2) (hw : w = Real.pi / 2 - v)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 2)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    TA θ v v (2 * w) ∨
    TA θ (2 * v) w w ∨
    TA θ u v w := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1 ∨ Q 0 = 2) with e0 | e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2) with e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      obtain e2 : Q 1 = 1 := by omega
      obtain e3 : R 1 = 0 := by omega
      obtain e4 : Q 2 = 1 := by omega
      obtain e5 : R 2 = 0 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
  · 
    obtain e1 : R 0 = 0 := by omega
    obtain e2 : Q 1 = 0 := by omega
    obtain e3 : R 1 = 1 := by omega
    obtain e4 : Q 2 = 0 := by omega
    obtain e5 : R 2 = 1 := by omega
    rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
    push_cast at h0 h1 h2
    exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
set_option maxHeartbeats 4000000 in
theorem shapes_twoPiThree (θ : Fin 3 → ℝ) (u v w : ℝ) (P Q R : Fin 3 → ℕ)
    (hu : u = 2 * Real.pi / 3) (hv : v = Real.pi / 3 - w)
    (hθ : ∀ k, θ k = (P k : ℝ) * u + (Q k : ℝ) * v + (R k : ℝ) * w)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 3) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) :
    (∀ k, θ k = Real.pi / 3) ∨
    TA θ w w (w + 3 * v) ∨
    TA θ v v (v + 3 * w) ∨
    TA θ w (w + v) (w + 2 * v) ∨
    TA θ v (w + v) (2 * w + v) ∨
    TA θ (2 * w) (2 * v) (w + v) ∨
    TA θ w (2 * w) (3 * v) ∨
    TA θ v (2 * v) (3 * w) ∨
    TA θ w (2 * v) (2 * w + v) ∨
    TA θ v (2 * w) (w + 2 * v) ∨
    TA θ w v u := by
  have h0 := hθ 0; have h1 := hθ 1; have h2 := hθ 2
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have hPk : P 0 = 0 ∧ P 1 = 0 ∧ P 2 = 0 := by omega
  obtain ⟨hP0, hP1, hP2⟩ := hPk
  rcases (by omega : Q 0 = 0 ∨ Q 0 = 1 ∨ Q 0 = 2 ∨ Q 0 = 3) with e0 | e0 | e0 | e0
  · 
    rcases (by omega : R 0 = 1 ∨ R 0 = 2 ∨ R 0 = 3) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2 ∨ Q 1 = 3) with e2 | e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 3 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
        · 
          obtain e4 : Q 2 = 3 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2 ∨ Q 1 = 3) with e2 | e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 3 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
    · 
      rcases (by omega : Q 1 = 1 ∨ Q 1 = 2) with e2 | e2
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1 ∨ R 0 = 2 ∨ R 0 = 3) with e1 | e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 1 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 0 2 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 2 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inl (fun k => by rcases fin3 k with rfl | rfl | rfl <;> linarith)
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1 ∨ Q 1 = 2) with e2 | e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 2 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
    · 
      obtain e2 : Q 1 = 1 := by omega
      obtain e3 : R 1 = 0 := by omega
      obtain e4 : Q 2 = 1 := by omega
      obtain e5 : R 2 = 0 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1 ∨ R 0 = 2) with e1 | e1 | e1
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2 ∨ R 1 = 3) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1 ∨ R 1 = 2) with e3 | e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 3 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 0 2 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 0 1 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
        · 
          obtain e4 : Q 2 = 1 := by omega
          obtain e5 : R 2 = 0 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        rcases (by omega : R 1 = 0 ∨ R 1 = 1) with e3 | e3
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 2 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
        · 
          obtain e4 : Q 2 = 0 := by omega
          obtain e5 : R 2 = 1 := by omega
          rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
          push_cast at h0 h1 h2
          exact Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))
    · 
      rcases (by omega : Q 1 = 0 ∨ Q 1 = 1) with e2 | e2
      · 
        obtain e3 : R 1 = 1 := by omega
        obtain e4 : Q 2 = 1 := by omega
        obtain e5 : R 2 = 0 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
      · 
        obtain e3 : R 1 = 0 := by omega
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))))))))))
  · 
    rcases (by omega : R 0 = 0 ∨ R 0 = 1) with e1 | e1
    · 
      obtain e2 : Q 1 = 0 := by omega
      rcases (by omega : R 1 = 1 ∨ R 1 = 2) with e3 | e3
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 2 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
      · 
        obtain e4 : Q 2 = 0 := by omega
        obtain e5 : R 2 = 1 := by omega
        rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
        push_cast at h0 h1 h2
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ta_of_idx θ _ _ _ 2 1 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith))))))))
    · 
      obtain e2 : Q 1 = 0 := by omega
      obtain e3 : R 1 = 1 := by omega
      obtain e4 : Q 2 = 0 := by omega
      obtain e5 : R 2 = 1 := by omega
      rw [hP0, e0, e1] at h0; rw [hP1, e2, e3] at h1; rw [hP2, e4, e5] at h2
      push_cast at h0 h1 h2
      exact Or.inr (Or.inl (ta_of_idx θ _ _ _ 1 2 0 (by decide) (by decide) (by decide) (by linarith) (by linarith) (by linarith)))
end Erdos634.Draft.LemmaCShapes
end

section
open scoped BigOperators
namespace Erdos634.Draft.LemmaCArith
lemma rat_prop (x : Fin 3 → ℝ) (hsum : x 0 + x 1 + x 2 = Real.pi)
    (hirr : ∃ i, ¬ ∃ r : ℚ, x i = (r : ℝ) * Real.pi)
    (g e : Fin 3 → ℤ)
    (hg : (g 0 : ℝ) * x 0 + g 1 * x 1 + g 2 * x 2 = 0)
    (he : (e 0 : ℝ) * x 0 + e 1 * x 1 + e 2 * x 2 = 0) (hne : e ≠ 0) :
    ∀ i j, g i * e j = g j * e i := by
  by_contra hcon
  have hw : ¬ (g 1 * e 2 - g 2 * e 1 = 0 ∧ g 2 * e 0 - g 0 * e 2 = 0 ∧
      g 0 * e 1 - g 1 * e 0 = 0) := by
    rintro ⟨h0, h1, h2⟩
    apply hcon
    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  obtain ⟨i0, hi0⟩ := hirr
  set w0 : ℤ := g 1 * e 2 - g 2 * e 1 with hw0
  set w1 : ℤ := g 2 * e 0 - g 0 * e 2 with hw1
  set w2 : ℤ := g 0 * e 1 - g 1 * e 0 with hw2
  have h01 : x 0 * (w1 : ℝ) = x 1 * w0 := by
    simp only [hw0, hw1]; push_cast
    linear_combination (g 2 : ℝ) * he - (e 2 : ℝ) * hg
  have h02 : x 0 * (w2 : ℝ) = x 2 * w0 := by
    simp only [hw0, hw2]; push_cast
    linear_combination (-(g 1 : ℝ)) * he + (e 1 : ℝ) * hg
  have h12 : x 1 * (w2 : ℝ) = x 2 * w1 := by
    simp only [hw1, hw2]; push_cast
    linear_combination (g 0 : ℝ) * he - (e 0 : ℝ) * hg
  have hS : ((w0 + w1 + w2 : ℤ) : ℝ) ≠ 0 := by
    intro hS0
    push_cast at hS0
    have a0 : (w0 : ℝ) * Real.pi = 0 := by
      have : x 0 * ((w0 : ℝ) + w1 + w2) = (w0 : ℝ) * Real.pi := by
        rw [← hsum]; linear_combination h01 + h02
      rw [← this, hS0]; ring
    have a1 : (w1 : ℝ) * Real.pi = 0 := by
      have : x 1 * ((w0 : ℝ) + w1 + w2) = (w1 : ℝ) * Real.pi := by
        rw [← hsum]; linear_combination (-1 : ℝ) * h01 + h12
      rw [← this, hS0]; ring
    have a2 : (w2 : ℝ) * Real.pi = 0 := by
      have : x 2 * ((w0 : ℝ) + w1 + w2) = (w2 : ℝ) * Real.pi := by
        rw [← hsum]; linear_combination (-1 : ℝ) * h02 - h12
      rw [← this, hS0]; ring
    have hpi := Real.pi_pos.ne'
    have b0 : (w0 : ℝ) = 0 := by
      rcases mul_eq_zero.mp a0 with h | h
      · exact h
      · exact absurd h hpi
    have b1 : (w1 : ℝ) = 0 := by
      rcases mul_eq_zero.mp a1 with h | h
      · exact h
      · exact absurd h hpi
    have b2 : (w2 : ℝ) = 0 := by
      rcases mul_eq_zero.mp a2 with h | h
      · exact h
      · exact absurd h hpi
    exact hw ⟨by exact_mod_cast b0, by exact_mod_cast b1, by exact_mod_cast b2⟩
  apply hi0
  have hSq : ((w0 + w1 + w2 : ℤ) : ℚ) ≠ 0 := by
    intro h; apply hS; have := congrArg (fun q : ℚ => (q : ℝ)) h; simpa using this
  have hx0 : x 0 * ((w0 : ℝ) + w1 + w2) = (w0 : ℝ) * Real.pi := by
    rw [← hsum]; linear_combination h01 + h02
  have hx1 : x 1 * ((w0 : ℝ) + w1 + w2) = (w1 : ℝ) * Real.pi := by
    rw [← hsum]; linear_combination (-1 : ℝ) * h01 + h12
  have hx2 : x 2 * ((w0 : ℝ) + w1 + w2) = (w2 : ℝ) * Real.pi := by
    rw [← hsum]; linear_combination (-1 : ℝ) * h02 - h12
  push_cast at hS
  fin_cases i0
  · refine ⟨(w0 : ℚ) / ((w0 : ℚ) + w1 + w2), ?_⟩
    push_cast; field_simp; linarith
  · refine ⟨(w1 : ℚ) / ((w0 : ℚ) + w1 + w2), ?_⟩
    push_cast; field_simp; linarith
  · refine ⟨(w2 : ℚ) / ((w0 : ℚ) + w1 + w2), ?_⟩
    push_cast; field_simp; linarith
theorem lemmaC_arith (x : Fin 3 → ℝ) (hpos : ∀ i, 0 < x i)
    (hsum : x 0 + x 1 + x 2 = Real.pi)
    (hirr : ∃ i, ¬ ∃ r : ℚ, x i = (r : ℝ) * Real.pi)
    (c : Fin 3 → ℕ) (hc3 : 3 ≤ c 0 + c 1 + c 2)
    (hc : (c 0 : ℝ) * x 0 + c 1 * x 1 + c 2 * x 2 = Real.pi)
    (hne : ¬ (c 0 = 1 ∧ c 1 = 1 ∧ c 2 = 1))
    {ι : Type*} (s : Finset ι) (f : ι → Fin 3 → ℕ) (k : ι → ℕ)
    (hk : ∀ v ∈ s, k v = 1 ∨ k v = 2)
    (hf : ∀ v ∈ s, (f v 0 : ℝ) * x 0 + f v 1 * x 1 + f v 2 * x 2 = (k v : ℝ) * Real.pi)
    (N : ℕ) (hN : ∀ j, ∑ v ∈ s, f v j + c j = N) :
    ∃ d : Fin 3 → ℤ, (∀ j, (c j : ℤ) = 1 + d j) ∧ (∀ j, -1 ≤ d j ∧ d j ≤ 2) ∧
      (∃ j, d j = -1) ∧ (∃ j, 0 < d j) ∧ 0 ≤ d 0 + d 1 + d 2 ∧
      (d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2 = 0 := by
  classical
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  set e : Fin 3 → ℤ := fun j => (c j : ℤ) - 1 with he_def
  have hex : (e 0 : ℝ) * x 0 + e 1 * x 1 + e 2 * x 2 = 0 := by
    simp only [he_def]; push_cast; linarith
  have hene : e ≠ 0 := by
    intro h
    apply hne
    have h0 := congrFun h 0; have h1 := congrFun h 1; have h2 := congrFun h 2
    simp only [he_def, Pi.zero_apply] at h0 h1 h2
    omega
  set g : ι → Fin 3 → ℤ := fun v j => (f v j : ℤ) - k v with hg_def
  have hgx : ∀ v ∈ s, (g v 0 : ℝ) * x 0 + g v 1 * x 1 + g v 2 * x 2 = 0 := by
    intro v hv
    simp only [hg_def]; push_cast
    have := hf v hv
    linear_combination this - (k v : ℝ) * hsum
  have hp : ∀ v ∈ s, ∀ i j, g v i * e j = g v j * e i := fun v hv =>
    rat_prop x hsum hirr (g v) e (hgx v hv) hex hene
  obtain ⟨n, hnpos, hndvd, α, hnα⟩ : ∃ n : ℤ, 0 < n ∧ (∀ j, n ∣ e j) ∧
      ∃ α : Fin 3 → ℤ, n = α 0 * e 0 + α 1 * e 1 + α 2 * e 2 := by
    set m : ℤ := (Int.gcd (e 0) (e 1) : ℤ) with hm
    have hm0 : m ∣ e 0 := Int.gcd_dvd_left ..
    have hm1 : m ∣ e 1 := Int.gcd_dvd_right ..
    have hmB : m = e 0 * Int.gcdA (e 0) (e 1) + e 1 * Int.gcdB (e 0) (e 1) :=
      Int.gcd_eq_gcd_ab _ _
    set n : ℤ := (Int.gcd m (e 2) : ℤ) with hn
    have hnm : n ∣ m := Int.gcd_dvd_left ..
    have hn2 : n ∣ e 2 := Int.gcd_dvd_right ..
    have hnB : n = m * Int.gcdA m (e 2) + e 2 * Int.gcdB m (e 2) := Int.gcd_eq_gcd_ab _ _
    have hdv : ∀ j, n ∣ e j := by
      intro j; fin_cases j
      · exact hnm.trans hm0
      · exact hnm.trans hm1
      · exact hn2
    refine ⟨n, ?_, hdv, ![Int.gcdA (e 0) (e 1) * Int.gcdA m (e 2),
      Int.gcdB (e 0) (e 1) * Int.gcdA m (e 2), Int.gcdB m (e 2)], ?_⟩
    · have hn0 : n ≠ 0 := by
        intro h0
        apply hene
        funext j
        have := hdv j
        rw [h0, zero_dvd_iff] at this
        simpa using this
      exact lt_of_le_of_ne (Int.natCast_nonneg _) (Ne.symm hn0)
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [hnB, hmB]; ring
  have hn0 : n ≠ 0 := hnpos.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  set d : Fin 3 → ℤ := fun j => e j / n with hd_def
  have hed : ∀ j, e j = n * d j := fun j => (Int.mul_ediv_cancel' (hndvd j)).symm
  have hdx : (d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2 = 0 := by
    have h : (n : ℝ) * ((d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2) = 0 := by
      have := hex
      rw [hed 0, hed 1, hed 2] at this
      push_cast at this; linarith
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hnR
    · exact h
  have hdne : ∃ j, d j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hene; funext j; rw [hed j, hcon j]; simp
  set t : ι → ℤ := fun v => α 0 * g v 0 + α 1 * g v 1 + α 2 * g v 2 with ht_def
  have hgt : ∀ v ∈ s, ∀ j, g v j = t v * d j := by
    intro v hv j
    have hp' := hp v hv
    have key : n * g v j = n * (t v * d j) := by
      have h1 : n * g v j = t v * e j := by
        rw [hnα]; simp only [ht_def]
        linear_combination α 0 * hp' j 0 + α 1 * hp' j 1 + α 2 * hp' j 2
      rw [h1, hed j]; ring
    exact mul_left_cancel₀ hn0 key
  have hfv : ∀ v ∈ s, ∀ j, (f v j : ℤ) = k v + t v * d j := by
    intro v hv j
    have := hgt v hv j
    simp only [hg_def] at this
    linarith
  have hcj : ∀ j, (c j : ℤ) = 1 + n * d j := by
    intro j; have := hed j; simp only [he_def] at this; linarith
  set T : ℤ := ∑ v ∈ s, t v with hT
  set K : ℤ := ∑ v ∈ s, (k v : ℤ) with hK
  have hcount : ∀ j, K + T * d j = (N : ℤ) - c j := by
    intro j
    have h1 : ∑ v ∈ s, (f v j : ℤ) = (N : ℤ) - c j := by
      have := hN j
      have h2 : ((∑ v ∈ s, f v j : ℕ) : ℤ) + c j = N := by exact_mod_cast this
      push_cast at h2; linarith
    rw [← h1, Finset.sum_congr rfl (fun v hv => hfv v hv j), Finset.sum_add_distrib, ← Finset.sum_mul]
  have hTn : ∀ j, (T + n) * d j = (N : ℤ) - 1 - K := by
    intro j; have := hcount j; have := hcj j; linarith
  have hNK : (N : ℤ) - 1 - K = 0 := by
    have h : ((N : ℝ) - 1 - K) * Real.pi = 0 := by
      have e0 := hTn 0; have e1 := hTn 1; have e2 := hTn 2
      have r0 : (((T + n) * d 0 : ℤ) : ℝ) = (((N : ℤ) - 1 - K : ℤ) : ℝ) := by rw [e0]
      have r1 : (((T + n) * d 1 : ℤ) : ℝ) = (((N : ℤ) - 1 - K : ℤ) : ℝ) := by rw [e1]
      have r2 : (((T + n) * d 2 : ℤ) : ℝ) = (((N : ℤ) - 1 - K : ℤ) : ℝ) := by rw [e2]
      push_cast at r0 r1 r2
      have : ((N : ℝ) - 1 - K) * (x 0 + x 1 + x 2)
          = ((T : ℝ) + n) * ((d 0 : ℝ) * x 0 + d 1 * x 1 + d 2 * x 2) := by
        linear_combination (-x 0) * r0 + (-x 1) * r1 + (-x 2) * r2
      rw [hsum, hdx] at this; linarith
    rcases mul_eq_zero.mp h with h | h
    · exact_mod_cast (by linarith : ((N : ℝ) - 1 - K) = 0)
    · exact absurd h hpi
  have hTn0 : T + n = 0 := by
    obtain ⟨j, hj⟩ := hdne
    have := hTn j
    rw [hNK] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hj
  have hTneg : T = -n := by linarith
  obtain ⟨v0, hv0, htv0⟩ : ∃ v ∈ s, t v < 0 := by
    by_contra h
    push Not at h
    have : 0 ≤ T := Finset.sum_nonneg h
    linarith
  have hk2 : (k v0 : ℤ) ≤ 2 := by have := hk v0 hv0; omega
  have hdle : ∀ j, d j ≤ 2 := by
    intro j
    by_contra hj
    push Not at hj
    have h1 := hfv v0 hv0 j
    have h2 : (0 : ℤ) ≤ (f v0 j : ℤ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ -1 - t v0) (by linarith : (0 : ℤ) ≤ d j)]
  have hneg : ∃ j, d j < 0 := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hdne
    have hjpos : 0 < d j := lt_of_le_of_ne (h j) (Ne.symm hj)
    have t0 : 0 ≤ (d 0 : ℝ) * x 0 := mul_nonneg (by exact_mod_cast h 0) (hpos 0).le
    have t1 : 0 ≤ (d 1 : ℝ) * x 1 := mul_nonneg (by exact_mod_cast h 1) (hpos 1).le
    have t2 : 0 ≤ (d 2 : ℝ) * x 2 := mul_nonneg (by exact_mod_cast h 2) (hpos 2).le
    have hjr : 0 < (d j : ℝ) * x j := mul_pos (by exact_mod_cast hjpos) (hpos j)
    fin_cases j <;> simp at hjr <;> linarith
  have hposx : ∃ j, 0 < d j := by
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hdne
    have hjneg : d j < 0 := lt_of_le_of_ne (h j) hj
    have t0 : (d 0 : ℝ) * x 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h 0) (hpos 0).le
    have t1 : (d 1 : ℝ) * x 1 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h 1) (hpos 1).le
    have t2 : (d 2 : ℝ) * x 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h 2) (hpos 2).le
    have hjr : (d j : ℝ) * x j < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast hjneg) (hpos j)
    fin_cases j <;> simp at hjr <;> linarith
  obtain ⟨j0, hj0⟩ := hneg
  have hc0 : (0 : ℤ) ≤ (c j0 : ℤ) := Nat.cast_nonneg _
  have hn1 : n = 1 := by
    have := hcj j0
    nlinarith [mul_nonneg hnpos.le (by linarith : (0 : ℤ) ≤ -1 - d j0)]
  subst hn1
  have hcj1 : ∀ j, (c j : ℤ) = 1 + d j := fun j => by have := hcj j; linarith
  have hge : ∀ j, -1 ≤ d j := fun j => by
    have := hcj1 j; have : (0 : ℤ) ≤ (c j : ℤ) := Nat.cast_nonneg _; linarith
  refine ⟨d, hcj1, fun j => ⟨hge j, hdle j⟩, ⟨j0, by have := hge j0; omega⟩, hposx, ?_, hdx⟩
  have h0 := hcj1 0; have h1 := hcj1 1; have h2 := hcj1 2
  omega
def sixVectors : Finset (ℤ × ℤ × ℤ) :=
  {(-1, 1, 0), (-1, 0, 2), (-1, 1, 1), (-1, 1, 2), (-1, 2, 2), (-1, -1, 2)}
theorem enum_six (a b c : ℤ) (ha : -1 ≤ a ∧ a ≤ 2) (hb : -1 ≤ b ∧ b ≤ 2) (hc : -1 ≤ c ∧ c ≤ 2)
    (hm : a = -1 ∨ b = -1 ∨ c = -1) (hp : 0 < a ∨ 0 < b ∨ 0 < c) (hs : 0 ≤ a + b + c) :
    ∃ i j l : Fin 3, i ≠ j ∧ j ≠ l ∧ i ≠ l ∧
      (![a, b, c] i, ![a, b, c] j, ![a, b, c] l) ∈ sixVectors := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hc1, hc2⟩ := hc
  interval_cases a <;> interval_cases b <;> interval_cases c <;> first
    | (exfalso; omega)
    | decide
end Erdos634.Draft.LemmaCArith
end

section
open scoped Classical
open Erdos634.Geometry
namespace Erdos634.Draft.LemmaCFigures
theorem vertex_figure_sum {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    {v : Plane} (hv : v ∈ cornerPts D.toDissection) (hnc : v ∉ Set.range D.target.pts) :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧
      (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card : ℝ) * γ
      = (k : ℝ) * Real.pi := by
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp hv
  obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hj
  have hvals : ∀ i, (D.tile i).localAngle v ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) :=
    fun i => congruentDissection_localAngle_mem_at_corner D α β γ hmα hmβ hmγ j m hm i
  have hpi := Real.pi_pos
  have hsumv := VertexFigureReal.sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ)
    (fun i => (D.tile i).localAngle v) hvals
  rw [show ({α, β, γ, Real.pi, 0} : Finset ℝ)
      = insert α (insert β (insert γ (insert Real.pi {0}))) from rfl] at hsumv
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hαβ, hαγ, hαπ.ne, hα0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hβγ, hβπ.ne, hβ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hγπ.ne, hγ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hpi.ne'),
      Finset.sum_singleton] at hsumv
  beta_reduce at hsumv
  set cα := (({i | (D.tile i).localAngle v = α} : Finset (Fin N)).card : ℝ) with hcα
  set cβ := (({i | (D.tile i).localAngle v = β} : Finset (Fin N)).card : ℝ) with hcβ
  set cγ := (({i | (D.tile i).localAngle v = γ} : Finset (Fin N)).card : ℝ) with hcγ
  set cπ := ({i | (D.tile i).localAngle v = Real.pi} : Finset (Fin N)).card with hcπ
  have hown : cα ≠ 0 ∨ cβ ≠ 0 ∨ cγ ≠ 0 := by
    have h := localAngle_at_own_vertex_mem D α β γ hmα hmβ hmγ j m
    rw [hm] at h
    have hne : ∀ c : Finset (Fin N), j ∈ c → (c.card : ℝ) ≠ 0 := fun c hc => by
      have := Finset.card_pos.mpr ⟨j, hc⟩; positivity
    rcases h with h | h | h
    · exact Or.inl (hne _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    · exact Or.inr (Or.inl (hne _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
    · exact Or.inr (Or.inr (hne _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)))
  have hc0 : 0 ≤ cα := Nat.cast_nonneg _
  have hc1 : 0 ≤ cβ := Nat.cast_nonneg _
  have hc2 : 0 ≤ cγ := Nat.cast_nonneg _
  have hcp : 0 ≤ (cπ : ℝ) := Nat.cast_nonneg _
  have hFpos : 0 < cα * α + cβ * β + cγ * γ := by
    have p0 := mul_nonneg hc0 hα0.le
    have p1 := mul_nonneg hc1 hβ0.le
    have p2 := mul_nonneg hc2 hγ0.le
    rcases hown with h | h | h
    · have := mul_pos (lt_of_le_of_ne hc0 (Ne.symm h)) hα0; linarith
    · have := mul_pos (lt_of_le_of_ne hc1 (Ne.symm h)) hβ0; linarith
    · have := mul_pos (lt_of_le_of_ne hc2 (Ne.symm h)) hγ0; linarith
  rcases Erdos634.Geometry.cornerPts_trichotomy D.toDissection hv with h | ⟨hfr, -⟩ | hint
  · exact absurd h hnc
  · have htot := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hfr hnc
    rw [hsumv] at htot
    have : (cπ : ℝ) < 1 := by nlinarith
    have hz : cπ = 0 := by exact_mod_cast (by exact_mod_cast this : cπ < 1) |> Nat.lt_one_iff.mp
    refine ⟨1, Or.inl rfl, ?_⟩
    rw [hz] at htot; push_cast at htot ⊢; linarith
  · have htot := Erdos634.PinPlumbing.pin_angle_sum_interior D.toDissection hint
    rw [hsumv] at htot
    have : (cπ : ℝ) < 2 := by nlinarith
    have hle : cπ ≤ 1 := by
      have : cπ < 2 := by exact_mod_cast this
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with hz | hz
    · refine ⟨2, Or.inr rfl, ?_⟩
      rw [hz] at htot; push_cast at htot ⊢; linarith
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [hz] at htot; push_cast at htot ⊢; linarith
theorem count_sum {N : ℕ} (la : Fin N → ℝ) (α β γ : ℝ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    (hvals : ∀ i, la i ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ)) :
    ∑ i, la i = (({i | la i = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | la i = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | la i = γ} : Finset (Fin N)).card : ℝ) * γ
      + (({i | la i = Real.pi} : Finset (Fin N)).card : ℝ) * Real.pi := by
  have hpi := Real.pi_pos
  have hsumv := VertexFigureReal.sum_by_value ({α, β, γ, Real.pi, 0} : Finset ℝ) la hvals
  rw [show ({α, β, γ, Real.pi, 0} : Finset ℝ)
      = insert α (insert β (insert γ (insert Real.pi {0}))) from rfl] at hsumv
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hαβ, hαγ, hαπ.ne, hα0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hβγ, hβπ.ne, hβ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hγπ.ne, hγ0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hpi.ne'),
      Finset.sum_singleton] at hsumv
  rw [hsumv]; ring
theorem corner_figure {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi) (k : Fin 3) :
    D.target.pts k ∈ cornerPts D.toDissection ∧
    (({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card : ℝ) * α
      + (({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card : ℝ) * β
      + (({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card : ℝ) * γ
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) ∧
    1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card := by
  have hpi := Real.pi_pos
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈ ({α, β, γ, Real.pi, 0} : Finset ℝ) := by
    intro i
    have hmem := congruentDissection_localAngle_mem_all D α β γ hmα hmβ hmγ (D.target.pts k) i
    have h2 := Erdos634.Geometry.Dissection.localAngle_ne_two_pi_of_not_mem_interior
      (D.toDissection.target_vertex_not_interior_tile k i)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact absurd h h2
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  have hcs := count_sum (fun i => (D.tile i).localAngle (D.target.pts k)) α β γ hαβ hαγ hβγ
    hα0 hβ0 hγ0 hαπ hβπ hγπ hvals
  have hθ := Erdos634.VertexFigureReal.corner_angle_sum D.toDissection k
  have hθlt := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target k
  have hθpos := Erdos634.MarchFlank.cornerAngle_pos D.target k
  beta_reduce at hcs
  set cα := (({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card : ℝ)
  set cβ := (({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card : ℝ)
  set cγ := (({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card : ℝ)
  set cπ := (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card : ℝ)
  have hc0 : 0 ≤ cα := Nat.cast_nonneg _
  have hc1 : 0 ≤ cβ := Nat.cast_nonneg _
  have hc2 : 0 ≤ cγ := Nat.cast_nonneg _
  have hcp : 0 ≤ cπ := Nat.cast_nonneg _
  have hcπ0 : cπ = 0 := by
    by_contra hne
    have : 1 ≤ cπ := by
      have : (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card) ≠ 0 := by
        intro h; apply hne; simp [cπ, h]
      exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr this)
    nlinarith [mul_nonneg hc0 hα0.le, mul_nonneg hc1 hβ0.le, mul_nonneg hc2 hγ0.le]
  rw [hcπ0] at hcs
  have hF : cα * α + cβ * β + cγ * γ = cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) := by linarith
  have hFpos : 0 < cα * α + cβ * β + cγ * γ := by rw [hF]; exact hθpos
  have hsum1 : 1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card := by
    by_contra hlt
    have h0 : ({i | (D.tile i).localAngle (D.target.pts k) = α} : Finset (Fin N)).card = 0 := by omega
    have h1 : ({i | (D.tile i).localAngle (D.target.pts k) = β} : Finset (Fin N)).card = 0 := by omega
    have h2 : ({i | (D.tile i).localAngle (D.target.pts k) = γ} : Finset (Fin N)).card = 0 := by omega
    have e0 : cα = 0 := by simp [cα, h0]
    have e1 : cβ = 0 := by simp [cβ, h1]
    have e2 : cγ = 0 := by simp [cγ, h2]
    rw [e0, e1, e2] at hFpos; simp at hFpos
  refine ⟨?_, hF, hsum1⟩
  have : ∃ i, (D.tile i).localAngle (D.target.pts k) = α ∨ (D.tile i).localAngle (D.target.pts k) = β
      ∨ (D.tile i).localAngle (D.target.pts k) = γ := by
    by_contra hno
    push Not at hno
    have hz : ∀ (θ : ℝ), (∀ i, (D.tile i).localAngle (D.target.pts k) ≠ θ) →
        ({i | (D.tile i).localAngle (D.target.pts k) = θ} : Finset (Fin N)).card = 0 := by
      intro θ h; simp [Finset.card_eq_zero, Finset.filter_eq_empty_iff, h]
    have := hz α (fun i => (hno i).1)
    have := hz β (fun i => (hno i).2.1)
    have := hz γ (fun i => (hno i).2.2)
    omega
  obtain ⟨i, hi⟩ := this
  have hne : ∀ θ, (D.tile i).localAngle (D.target.pts k) = θ → 0 < θ → θ < Real.pi →
      D.target.pts k ∈ cornerPts D.toDissection := by
    intro θ h h0 hpi'
    obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) h h0.ne' hpi'.ne (by linarith)
    rw [← hm]; exact mem_cornerPts D.toDissection i m
  rcases hi with h | h | h
  · exact hne α h hα0 hαπ
  · exact hne β h hβ0 hβπ
  · exact hne γ h hγ0 hγπ
end Erdos634.Draft.LemmaCFigures
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.Draft.LemmaCFigures
namespace Erdos634.Draft.LemmaCAssemble
noncomputable def cnt {N : ℕ} (D : CongruentDissection N) (θ : ℝ) (v : Plane) : ℕ :=
  ({i | (D.tile i).localAngle v = θ} : Finset (Fin N)).card
noncomputable def cfig {N : ℕ} (D : CongruentDissection N) (x : Fin 3 → ℝ) (j : Fin 3) : ℕ :=
  ∑ k : Fin 3, cnt D (x j) (D.target.pts k)
theorem lemmaC_geometric {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    (hirr : ∃ i, ¬ ∃ r : ℚ, ![α, β, γ] i = (r : ℝ) * Real.pi)
    (hne : ¬ (cfig D ![α, β, γ] 0 = 1 ∧ cfig D ![α, β, γ] 1 = 1 ∧ cfig D ![α, β, γ] 2 = 1)) :
    ∃ d : Fin 3 → ℤ, (∀ j, (cfig D ![α, β, γ] j : ℤ) = 1 + d j) ∧ (∀ j, -1 ≤ d j ∧ d j ≤ 2) ∧
      (∃ j, d j = -1) ∧ (∃ j, 0 < d j) ∧ 0 ≤ d 0 + d 1 + d 2 ∧
      (d 0 : ℝ) * α + d 1 * β + d 2 * γ = 0 := by
  have hpi := Real.pi_pos
  set x : Fin 3 → ℝ := ![α, β, γ] with hx
  have hsum : x 0 + x 1 + x 2 = Real.pi := by
    have := Erdos634.Geometry.cornerAngle_sum D.model
    simp only [hx, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    linarith
  have hpos : ∀ i, 0 < x i := by intro i; fin_cases i <;> simp [hx, hα0, hβ0, hγ0]
  set s : Finset Plane := (cornerPts D.toDissection).filter (fun v => v ∉ Set.range D.target.pts)
    with hs
  have hF1 : ∀ v ∈ s, ∃ k : ℕ, (k = 1 ∨ k = 2) ∧
      (cnt D α v : ℝ) * α + (cnt D β v : ℝ) * β + (cnt D γ v : ℝ) * γ = (k : ℝ) * Real.pi := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    exact vertex_figure_sum D α β γ hmα hmβ hmγ hαβ hαγ hβγ hα0 hβ0 hγ0 hαπ hβπ hγπ hv1 hv2
  choose! k hk hf using hF1
  have hcorner := fun kk => corner_figure D α β γ hmα hmβ hmγ hαβ hαγ hβγ hα0 hβ0 hγ0 hαπ hβπ hγπ kk
  have hxk : ∀ kk : Fin 3, cornerAngle (D.model.pts (kk + 1)) (D.model.pts kk)
      (D.model.pts (kk + 2)) = x kk := by
    intro kk; fin_cases kk
    · simpa [hx] using hmα
    · simpa [hx] using hmβ
    · simpa [hx] using hmγ
  have hxinj : ∀ a b : Fin 3, x a = x b → a = b := by
    intro a b h
    have hd : ∀ u v : ℝ, u = v → v = u → u ≠ v → False := fun u v h _ hn => hn h
    fin_cases a <;> fin_cases b <;> simp [hx] at h ⊢ <;> simp_all [eq_comm]
  have htotal : ∀ j : Fin 3, ∑ v ∈ cornerPts D.toDissection, cnt D (x j) v = N := by
    intro j
    have := congruentDissection_corner_balance D
      (fun a b h => hxinj a b (by rw [← hxk a, ← hxk b]; exact h)) j
      (by rw [hxk j]; exact (hpos j).ne')
      (by rw [hxk j]; fin_cases j <;> simp [hx] <;> linarith)
      (by rw [hxk j]; fin_cases j <;> simp [hx] <;> linarith)
    rw [hxk j] at this
    exact this
  have hcorn_mem : ∀ kk, D.target.pts kk ∈ cornerPts D.toDissection := fun kk => (hcorner kk).1
  have himg : (cornerPts D.toDissection).filter (fun v => v ∈ Set.range D.target.pts)
      = Finset.univ.image D.target.pts := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
    constructor
    · rintro ⟨_, kk, hkk⟩; exact ⟨kk, hkk⟩
    · rintro ⟨kk, rfl⟩; exact ⟨hcorn_mem kk, kk, rfl⟩
  have hsplit : ∀ j, ∑ v ∈ s, cnt D (x j) v + cfig D x j = N := by
    intro j
    have h1 := Finset.sum_filter_add_sum_filter_not (cornerPts D.toDissection)
      (fun v => v ∈ Set.range D.target.pts) (fun v => cnt D (x j) v)
    rw [himg, Finset.sum_image (fun a _ b _ hab => Erdos634.CertNode.pts_injective D.target hab),
      htotal j] at h1
    have h2 : cfig D x j = ∑ kk : Fin 3, cnt D (x j) (D.target.pts kk) := rfl
    have h3 : s = (cornerPts D.toDissection).filter (fun v => ¬ v ∈ Set.range D.target.pts) := rfl
    rw [h3]; omega
  have e0 := (hcorner 0).2
  have e1 := (hcorner 1).2
  have e2 := (hcorner 2).2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at e0 e1 e2
  have hT := Erdos634.Geometry.cornerAngle_sum D.target
  have hc3 : 3 ≤ cfig D x 0 + cfig D x 1 + cfig D x 2 := by
    obtain ⟨-, a0⟩ := e0
    obtain ⟨-, a1⟩ := e1
    obtain ⟨-, a2⟩ := e2
    simp only [cfig, cnt, Fin.sum_univ_three, hx, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    omega
  have hc : (cfig D x 0 : ℝ) * x 0 + cfig D x 1 * x 1 + cfig D x 2 * x 2 = Real.pi := by
    obtain ⟨b0, -⟩ := e0
    obtain ⟨b1, -⟩ := e1
    obtain ⟨b2, -⟩ := e2
    simp only [cfig, cnt, Fin.sum_univ_three, hx, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast
    linarith
  have hf' : ∀ v ∈ s, (cnt D (x 0) v : ℝ) * x 0 + (cnt D (x 1) v : ℝ) * x 1
      + (cnt D (x 2) v : ℝ) * x 2 = (k v : ℝ) * Real.pi := by
    intro v hv
    have := (hf v hv)
    simpa [hx] using this
  obtain ⟨d, hd1, hd2, hd3, hd4, hd5, hd6⟩ := Erdos634.Draft.LemmaCArith.lemmaC_arith x hpos hsum
    hirr (fun j => cfig D x j) hc3 hc hne s (fun v j => cnt D (x j) v) k (fun v hv => hk v hv)
    hf' N hsplit
  refine ⟨d, hd1, hd2, hd3, hd4, hd5, ?_⟩
  simpa [hx] using hd6
end Erdos634.Draft.LemmaCAssemble
end

section
open scoped Classical
namespace Erdos634.Draft.TheoremPConditional
open Erdos634.Geometry Erdos634.TilePlacement
def IrrPi (x : ℝ) : Prop := ¬ ∃ r : ℚ, x = (r : ℝ) * Real.pi
def TgtAngles {N : ℕ} (D : CongruentDissection N) (x y z : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), D.target.angleAt (σ 0) = x ∧ D.target.angleAt (σ 1) = y ∧
    D.target.angleAt (σ 2) = z
def SimilarTM {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ (μ : ℝ) (τ : Equiv.Perm (Fin 3)), ∀ k, D.target.angleAt k = D.model.angleAt (τ k) ∧
    D.target.oppLen k = μ * D.model.oppLen (τ k)
def RightCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α : ℝ, 0 < α ∧ α < Real.pi / 2 ∧ Irrational (α / Real.pi) ∧
    (∃ p q : Fin 3, p ≠ q ∧ D.model.angleAt p = α ∧ D.model.angleAt q = Real.pi / 2) ∧
    ∃ γ : ℝ, (γ = α ∨ γ = Real.pi / 2 - α) ∧
      ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = γ ∧ D.target.angleAt j = γ
def TwoAlphaCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α a b c : ℝ, IrrPi α ∧ D.model.TwoAlphaData α a b c ∧
    ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = α ∧ D.target.angleAt j = α
def SixtyTile {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α a b c : ℝ, IrrPi α ∧ D.model.SixtyData α a b c
def Equilateral {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∀ k, D.target.angleAt k = Real.pi / 3
def IsoTP {N : ℕ} (D : CongruentDissection N) (α : ℝ) : Prop :=
  TgtAngles D α α (α + 3 * (Real.pi / 3 - α)) ∨
    TgtAngles D (Real.pi / 3 - α) (Real.pi / 3 - α) ((Real.pi / 3 - α) + 3 * α)
def F1Shape {N : ℕ} (D : CongruentDissection N) (α : ℝ) : Prop :=
  TgtAngles D α (α + (Real.pi / 3 - α)) (α + 2 * (Real.pi / 3 - α)) ∨
    TgtAngles D (Real.pi / 3 - α) (α + (Real.pi / 3 - α)) (2 * α + (Real.pi / 3 - α))
def F2to4Shape {N : ℕ} (D : CongruentDissection N) (α : ℝ) : Prop :=
  TgtAngles D (2 * α) (2 * (Real.pi / 3 - α)) (α + (Real.pi / 3 - α)) ∨
  TgtAngles D α (2 * α) (3 * (Real.pi / 3 - α)) ∨
  TgtAngles D (Real.pi / 3 - α) (2 * (Real.pi / 3 - α)) (3 * α) ∨
  TgtAngles D α (2 * (Real.pi / 3 - α)) (2 * α + (Real.pi / 3 - α)) ∨
  TgtAngles D (Real.pi / 3 - α) (2 * α) (α + 2 * (Real.pi / 3 - α))
def TwoPiThreeCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α a b c : ℝ, IrrPi α ∧ D.model.TwoPiThreeData α a b c ∧
    (Equilateral D ∨ IsoTP D α ∨ F1Shape D α ∨ F2to4Shape D α)
def ThreeTwoCase {N : ℕ} (D : CongruentDissection N) : Prop :=
  ∃ α β a b c : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ D.model.ThreeAlphaData α β a b c ∧
    (TgtAngles D β β (3 * α) ∨ TgtAngles D (α + β) (α + β) α ∨
     TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D (2 * α) α (2 * β) ∨
     TgtAngles D α α (α + 2 * β))
section Controls
end Controls
end Erdos634.Draft.TheoremPConditional
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCAssemble
namespace Erdos634.Draft.LemmaCSimilar
theorem sides_of_angles (T M : Tri) (τ : Equiv.Perm (Fin 3))
    (h : ∀ k, T.angleAt k = M.angleAt (τ k)) :
    ∃ μ : ℝ, ∀ k, T.oppLen k = μ * M.oppLen (τ k) := by
  have hs : 0 < Real.sin (T.angleAt 0) := Erdos634.Geometry.A1Field.sin_angle_pos T 0
  have hm : 0 < M.oppLen (τ 0) := Erdos634.Geometry.Row3.RP.oppLen_pos M _
  refine ⟨T.oppLen 0 / M.oppLen (τ 0), fun k => ?_⟩
  have h1 := T.lawSin 0 k
  have h2 := M.lawSin (τ 0) (τ k)
  rw [← h 0, ← h k] at h2
  field_simp
  have : Real.sin (T.angleAt 0) * (T.oppLen k * M.oppLen (τ 0))
      = Real.sin (T.angleAt 0) * (T.oppLen 0 * M.oppLen (τ k)) := by
    linear_combination M.oppLen (τ 0) * h1 - T.oppLen 0 * h2
  exact mul_left_cancel₀ hs.ne' this
theorem perm_of_figures (T M : Tri) (α β γ : ℝ)
    (hM0 : M.angleAt 0 = α) (hM1 : M.angleAt 1 = β) (hM2 : M.angleAt 2 = γ)
    (a b c : Fin 3 → ℕ)
    (hF : ∀ k, (a k : ℝ) * α + (b k : ℝ) * β + (c k : ℝ) * γ = T.angleAt k)
    (hpos : ∀ k, 1 ≤ a k + b k + c k)
    (h0 : a 0 + a 1 + a 2 = 1) (h1 : b 0 + b 1 + b 2 = 1) (h2 : c 0 + c 1 + c 2 = 1) :
    ∃ τ : Equiv.Perm (Fin 3), ∀ k, T.angleAt k = M.angleAt (τ k) := by
  have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  let J : Fin 3 → Fin 3 := fun k => if a k = 1 then 0 else if b k = 1 then 1 else 2
  have hc : ∀ k : Fin 3, (a k = 1 ∧ b k = 0 ∧ c k = 0) ∨ (a k = 0 ∧ b k = 1 ∧ c k = 0)
      ∨ (a k = 0 ∧ b k = 0 ∧ c k = 1) := by
    have : ∀ k : Fin 3, 1 ≤ a k + b k + c k := hpos
    intro k
    rcases fin3 k with rfl | rfl | rfl <;> omega
  have hJinj : Function.Injective J := by
    intro k l hkl
    by_contra hne
    have hk := hc k; have hl := hc l
    have hkl' : k ≠ l := hne
    rcases fin3 k with rfl | rfl | rfl <;> rcases fin3 l with rfl | rfl | rfl <;>
      first | exact absurd rfl hkl' | (simp only [J] at hkl; split_ifs at hkl <;> simp_all <;> omega)
  have hθ : ∀ k, T.angleAt k = M.angleAt (J k) := by
    intro k
    have hk := hF k
    rcases hc k with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
    · simp only [J, e0, if_true]; rw [← hk, e0, e1, e2, hM0]; simp
    · simp only [J, e0, e1]; simp; rw [← hk, e0, e1, e2, hM1]; simp
    · simp only [J, e0, e1]; simp; rw [← hk, e0, e1, e2, hM2]; simp
  exact ⟨Equiv.ofBijective J (Finite.injective_iff_bijective.mp hJinj), hθ⟩
theorem cfig_ne_of_notSimilar {N : ℕ} (D : CongruentDissection N) (α β γ : ℝ)
    (hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α)
    (hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β)
    (hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα0 : 0 < α) (hβ0 : 0 < β) (hγ0 : 0 < γ)
    (hαπ : α < Real.pi) (hβπ : β < Real.pi) (hγπ : γ < Real.pi)
    (hns : ¬ SimilarTM D) :
    ¬ (cfig D ![α, β, γ] 0 = 1 ∧ cfig D ![α, β, γ] 1 = 1 ∧ cfig D ![α, β, γ] 2 = 1) := by
  rintro ⟨h0, h1, h2⟩
  apply hns
  have hcorner := fun kk => Erdos634.Draft.LemmaCFigures.corner_figure D α β γ hmα hmβ hmγ hαβ hαγ
    hβγ hα0 hβ0 hγ0 hαπ hβπ hγπ kk
  obtain ⟨τ, hτ⟩ := perm_of_figures D.target D.model α β γ hmα hmβ hmγ
    (fun k => cnt D α (D.target.pts k)) (fun k => cnt D β (D.target.pts k))
    (fun k => cnt D γ (D.target.pts k))
    (fun k => (hcorner k).2.1) (fun k => (hcorner k).2.2)
    (by simpa [cfig, Fin.sum_univ_three] using h0)
    (by simpa [cfig, Fin.sum_univ_three] using h1)
    (by simpa [cfig, Fin.sum_univ_three] using h2)
  obtain ⟨μ, hμ⟩ := sides_of_angles D.target D.model τ hτ
  exact ⟨μ, τ, fun k => ⟨hτ k, hμ k⟩⟩
end Erdos634.Draft.LemmaCSimilar
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFigures
namespace Erdos634.Draft.LemmaCIso
theorem corner_fig2 {N : ℕ} (D : CongruentDissection N) (a b : ℝ)
    (hmod : ∀ k : Fin 3, cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = a
      ∨ cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = b)
    (hab : a ≠ b) (ha0 : 0 < a) (hb0 : 0 < b) (haπ : a < Real.pi) (hbπ : b < Real.pi) (k : Fin 3) :
    D.target.pts k ∈ cornerPts D.toDissection ∧
    (({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card : ℝ) * a
      + (({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card : ℝ) * b
      = cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) ∧
    1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card := by
  have hpi := Real.pi_pos
  set x0 := cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) with hx0
  set x1 := cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) with hx1
  set x2 := cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) with hx2
  have hxab : ∀ y, (y = x0 ∨ y = x1 ∨ y = x2) → y = a ∨ y = b := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · exact hmod 0
    · exact hmod 1
    · exact hmod 2
  have hvals : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈ ({a, b, Real.pi, 0} : Finset ℝ) := by
    intro i
    have hmem := congruentDissection_localAngle_mem_all D x0 x1 x2 rfl rfl rfl (D.target.pts k) i
    have h2 := Erdos634.Geometry.Dissection.localAngle_ne_two_pi_of_not_mem_interior
      (D.toDissection.target_vertex_not_interior_tile k i)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with h | h | h | h | h | h
    · rcases hxab _ (Or.inl rfl) with e | e <;> [exact Or.inl (h.trans e); exact Or.inr (Or.inl (h.trans e))]
    · rcases hxab _ (Or.inr (Or.inl rfl)) with e | e <;> [exact Or.inl (h.trans e); exact Or.inr (Or.inl (h.trans e))]
    · rcases hxab _ (Or.inr (Or.inr rfl)) with e | e <;> [exact Or.inl (h.trans e); exact Or.inr (Or.inl (h.trans e))]
    · exact Or.inr (Or.inr (Or.inl h))
    · exact absurd h h2
    · exact Or.inr (Or.inr (Or.inr h))
  have hsumv := VertexFigureReal.sum_by_value ({a, b, Real.pi, 0} : Finset ℝ)
    (fun i => (D.tile i).localAngle (D.target.pts k)) hvals
  rw [show ({a, b, Real.pi, 0} : Finset ℝ) = insert a (insert b (insert Real.pi {0})) from rfl] at hsumv
  rw [Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hab, haπ.ne, ha0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hbπ.ne, hb0.ne'⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hpi.ne'),
      Finset.sum_singleton] at hsumv
  beta_reduce at hsumv
  have hθ := Erdos634.VertexFigureReal.corner_angle_sum D.toDissection k
  have hθlt := Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.target k
  have hθpos := Erdos634.MarchFlank.cornerAngle_pos D.target k
  set cα := (({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card : ℝ) with hca
  set cβ := (({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card : ℝ) with hcb
  set cπ := (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card : ℝ) with hcp
  have hc0 : 0 ≤ cα := Nat.cast_nonneg _
  have hc1 : 0 ≤ cβ := Nat.cast_nonneg _
  have hcπ0 : cπ = 0 := by
    by_contra hne
    have : 1 ≤ cπ := by
      have : (({i | (D.tile i).localAngle (D.target.pts k) = Real.pi} : Finset (Fin N)).card) ≠ 0 := by
        intro h; apply hne; simp [cπ, h]
      exact Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr this)
    nlinarith [mul_nonneg hc0 ha0.le, mul_nonneg hc1 hb0.le]
  rw [hcπ0] at hsumv
  have hF : cα * a + cβ * b = cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) := by linarith
  have hFpos : 0 < cα * a + cβ * b := by rw [hF]; exact hθpos
  have hsum1 : 1 ≤ ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card
      + ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card := by
    by_contra hlt
    have h0 : ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card = 0 := by omega
    have h1 : ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card = 0 := by omega
    have e0 : cα = 0 := by simp [cα, h0]
    have e1 : cβ = 0 := by simp [cβ, h1]
    rw [e0, e1] at hFpos; simp at hFpos
  refine ⟨?_, hF, hsum1⟩
  have : ∃ i, (D.tile i).localAngle (D.target.pts k) = a ∨ (D.tile i).localAngle (D.target.pts k) = b := by
    by_contra hno
    push Not at hno
    have hz : ∀ (θ : ℝ), (∀ i, (D.tile i).localAngle (D.target.pts k) ≠ θ) →
        ({i | (D.tile i).localAngle (D.target.pts k) = θ} : Finset (Fin N)).card = 0 := by
      intro θ h; simp [h]
    have := hz a (fun i => (hno i).1)
    have := hz b (fun i => (hno i).2)
    omega
  obtain ⟨i, hi⟩ := this
  have hne : ∀ θ, (D.tile i).localAngle (D.target.pts k) = θ → 0 < θ → θ < Real.pi →
      D.target.pts k ∈ cornerPts D.toDissection := by
    intro θ h h0 hpi'
    obtain ⟨m, hm⟩ := vertex_of_localAngle_corner (D.tile i) h h0.ne' hpi'.ne (by linarith)
    rw [← hm]; exact mem_cornerPts D.toDissection i m
  rcases hi with h | h
  · exact hne a h ha0 haπ
  · exact hne b h hb0 hbπ
theorem iso_arith (a b : ℝ) (hb : 2 * a + b = Real.pi) (hirr : IrrPi a) (m n : ℤ)
    (h : (m : ℝ) * a + (n : ℝ) * b = 0) : m = 0 ∧ n = 0 := by
  have hpi := Real.pi_pos
  have h2 : ((m : ℝ) - 2 * n) * a + (n : ℝ) * Real.pi = 0 := by
    have : b = Real.pi - 2 * a := by linarith
    rw [this] at h; linarith
  by_cases hm : (m : ℝ) - 2 * n = 0
  · rw [hm] at h2
    have hn : (n : ℝ) = 0 := by
      rcases mul_eq_zero.mp (by linarith : (n : ℝ) * Real.pi = 0) with h | h
      · exact h
      · exact absurd h hpi.ne'
    have hn' : n = 0 := by exact_mod_cast hn
    refine ⟨?_, hn'⟩
    have : (m : ℝ) = 0 := by rw [hn] at hm; linarith
    exact_mod_cast this
  · exfalso
    apply hirr
    refine ⟨(-(n : ℚ)) / ((m : ℚ) - 2 * n), ?_⟩
    push_cast
    have hm' : ((m : ℝ) - 2 * n) ≠ 0 := hm
    rw [div_mul_eq_mul_div, eq_div_iff hm']
    linarith
theorem swap_match (f g : Fin 3 → ℝ) (a b : ℝ) (i j : Fin 3)
    (hf : f i = b ∧ ∀ k, k ≠ i → f k = a) (hg : g j = b ∧ ∀ k, k ≠ j → g k = a) :
    ∀ k, f k = g (Equiv.swap i j k) := by
  intro k
  by_cases hki : k = i
  · subst hki; rw [Equiv.swap_apply_left, hf.1, hg.1]
  · by_cases hkj : k = j
    · subst hkj
      rw [Equiv.swap_apply_right, hf.2 _ hki]
      have : k ≠ i := hki
      exact (hg.2 i (fun h => hki h.symm)).symm
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, hf.2 _ hki, hg.2 _ hkj]
theorem iso_similar {N : ℕ} (D : CongruentDissection N) (p q r : Fin 3)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (heq : D.model.angleAt p = D.model.angleAt q)
    (hirr : ∃ i, IrrPi (D.model.angleAt i)) : SimilarTM D := by
  have hpi := Real.pi_pos
  have key : ∀ p q r k : Fin 3, p ≠ q → p ≠ r → q ≠ r → k = p ∨ k = q ∨ k = r := by decide
  have hall : ∀ k, k = p ∨ k = q ∨ k = r := fun k => key p q r k hpq hpr hqr
  have huniv : (Finset.univ : Finset (Fin 3)) = {p, q, r} := by
    ext k; simp [hall k]
  have hsumA : D.model.angleAt 0 + D.model.angleAt 1 + D.model.angleAt 2 = Real.pi :=
    Erdos634.Geometry.cornerAngle_sum D.model
  have hpqr : D.model.angleAt p + D.model.angleAt q + D.model.angleAt r = Real.pi := by
    have h := Fin.sum_univ_three (fun k => D.model.angleAt k)
    rw [huniv, Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_insert (by simp [hqr]),
      Finset.sum_singleton] at h
    linarith
  set a := D.model.angleAt p with ha
  set b := D.model.angleAt r with hb
  have h2ab : 2 * a + b = Real.pi := by rw [← heq] at hpqr; linarith
  have hirra : IrrPi a := by
    obtain ⟨i, hi⟩ := hirr
    rcases hall i with rfl | rfl | rfl
    · exact hi
    · rw [← heq] at hi; exact hi
    · rintro ⟨s, hs⟩
      apply hi
      refine ⟨1 - 2 * s, ?_⟩
      push_cast
      have : b = Real.pi - 2 * a := by linarith
      rw [show D.model.angleAt i = b from rfl, this, hs]; ring
  have hposA : ∀ k, 0 < D.model.angleAt k := fun k => Erdos634.MarchFlank.cornerAngle_pos D.model k
  have hltA : ∀ k, D.model.angleAt k < Real.pi := fun k => Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model k
  have ha0 := hposA p
  have hb0 := hposA r
  have haπ := hltA p
  have hbπ := hltA r
  have hab : a ≠ b := by
    intro h
    apply hirra
    refine ⟨1 / 3, ?_⟩
    push_cast
    linarith
  have hmod : ∀ k : Fin 3, cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = a
      ∨ cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2)) = b := by
    intro k
    rcases hall k with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl heq.symm
    · exact Or.inr rfl
  have hcor := fun k => corner_fig2 D a b hmod hab ha0 hb0 haπ hbπ k
  have e0 := (hcor 0).2
  have e1 := (hcor 1).2
  have e2 := (hcor 2).2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl] at e0 e1 e2
  have hT := Erdos634.Geometry.cornerAngle_sum D.target
  set A : Fin 3 → ℕ := fun k => ({i | (D.tile i).localAngle (D.target.pts k) = a} : Finset (Fin N)).card
    with hA
  set B : Fin 3 → ℕ := fun k => ({i | (D.tile i).localAngle (D.target.pts k) = b} : Finset (Fin N)).card
    with hB
  have hreal : ((A 0 + A 1 + A 2 : ℕ) : ℝ) * a + ((B 0 + B 1 + B 2 : ℕ) : ℝ) * b = Real.pi := by
    push_cast
    have := e0.1; have := e1.1; have := e2.1
    simp only [hA, hB]
    linarith [e0.1, e1.1, e2.1]
  have hz := iso_arith a b h2ab hirra ((A 0 + A 1 + A 2 : ℕ) - 2 : ℤ) ((B 0 + B 1 + B 2 : ℕ) - 1 : ℤ)
    (by push_cast; nlinarith [hreal])
  have hA2 : A 0 + A 1 + A 2 = 2 := by have := hz.1; omega
  have hB1 : B 0 + B 1 + B 2 = 1 := by have := hz.2; omega
  have hp0 : 1 ≤ A 0 + B 0 := e0.2
  have hp1 : 1 ≤ A 1 + B 1 := e1.2
  have hp2 : 1 ≤ A 2 + B 2 := e2.2
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  have hpick : ∃ i, B i = 1 ∧ ∀ k, k ≠ i → B k = 0 := by
    have : (B 0 = 1 ∧ B 1 = 0 ∧ B 2 = 0) ∨ (B 0 = 0 ∧ B 1 = 1 ∧ B 2 = 0)
        ∨ (B 0 = 0 ∧ B 1 = 0 ∧ B 2 = 1) := by omega
    rcases this with h | h | h
    · refine ⟨0, h.1, fun k hk => ?_⟩
      rcases fin3 k with rfl | rfl | rfl
      · exact absurd rfl hk
      · exact h.2.1
      · exact h.2.2
    · refine ⟨1, h.2.1, fun k hk => ?_⟩
      rcases fin3 k with rfl | rfl | rfl
      · exact h.1
      · exact absurd rfl hk
      · exact h.2.2
    · refine ⟨2, h.2.2, fun k hk => ?_⟩
      rcases fin3 k with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact absurd rfl hk
  obtain ⟨i, hi1, hi0⟩ := hpick
  have hAk : ∀ k, A k + B k = 1 := by
    intro k; rcases fin3 k with rfl | rfl | rfl <;> omega
  have hθ : ∀ k, (A k : ℝ) * a + (B k : ℝ) * b = D.target.angleAt k := by
    intro k; rcases fin3 k with rfl | rfl | rfl
    · exact e0.1
    · exact e1.1
    · exact e2.1
  have hf : D.target.angleAt i = b ∧ ∀ k, k ≠ i → D.target.angleAt k = a := by
    refine ⟨?_, fun k hk => ?_⟩
    · rw [← hθ i]; have := hAk i; have : A i = 0 := by omega
      rw [this, hi1]; simp
    · rw [← hθ k]; have := hAk k; have h0 := hi0 k hk
      have : A k = 1 := by omega
      rw [this, h0]; simp
  have hg : D.model.angleAt r = b ∧ ∀ k, k ≠ r → D.model.angleAt k = a := by
    refine ⟨rfl, fun k hk => ?_⟩
    rcases hall k with rfl | rfl | rfl
    · rfl
    · exact heq.symm
    · exact absurd rfl hk
  have hτ := swap_match (fun k => D.target.angleAt k) (fun k => D.model.angleAt k) a b i r hf hg
  obtain ⟨μ, hμ⟩ := Erdos634.Draft.LemmaCSimilar.sides_of_angles D.target D.model (Equiv.swap i r) hτ
  exact ⟨μ, Equiv.swap i r, fun k => ⟨hτ k, hμ k⟩⟩
end Erdos634.Draft.LemmaCIso
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCAssemble Erdos634.Draft.LemmaCShapes
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
theorem irr_transfer (y w : ℝ) (a b : ℚ) (h : y = a * w + b * Real.pi) (hy : IrrPi y) :
    IrrPi w := by
  rintro ⟨q, hq⟩
  exact hy ⟨a * q + b, by rw [h, hq]; push_cast; ring⟩
noncomputable def permOf (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Equiv.Perm (Fin 3) :=
  Equiv.ofBijective ![a, b, c]
    ((by decide : ∀ i j l : Fin 3, i ≠ j → i ≠ l → j ≠ l → Function.Bijective ![i, j, l])
      a b c hab hac hbc)
theorem permOf_0 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    permOf a b c hab hac hbc 0 = a := rfl
theorem permOf_1 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    permOf a b c hab hac hbc 1 = b := rfl
theorem permOf_2 (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    permOf a b c hab hac hbc 2 = c := rfl
theorem sim_of_TA {N : ℕ} (D : CongruentDissection N) (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h : TA (fun k => D.target.angleAt k) (D.model.angleAt a) (D.model.angleAt b)
      (D.model.angleAt c)) : SimilarTM D := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  let τ : Equiv.Perm (Fin 3) := σ.symm.trans (permOf a b c hab hac hbc)
  have hτ : ∀ k, D.target.angleAt k = D.model.angleAt (τ k) := by
    intro k
    obtain ⟨m, rfl⟩ := σ.surjective k
    have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    rcases fin3 m with rfl | rfl | rfl
    · simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, permOf_0]; exact h0
    · simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, permOf_1]; exact h1
    · simp only [τ, Equiv.trans_apply, Equiv.symm_apply_apply, permOf_2]; exact h2
  obtain ⟨μ, hμ⟩ := Erdos634.Draft.LemmaCSimilar.sides_of_angles D.target D.model τ hτ
  exact ⟨μ, τ, fun k => ⟨hτ k, hμ k⟩⟩
theorem caseSixty {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m))
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i - D.model.angleAt j + 2 * D.model.angleAt l = 0) : SixtyTile D := by
  have hl : D.model.angleAt l = Real.pi / 3 := by linarith
  have hj : D.model.angleAt j = 2 * Real.pi / 3 - D.model.angleAt i := by linarith
  have hIrr : IrrPi (D.model.angleAt i) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact hm
    · exact irr_transfer _ _ (-1) (2 / 3) (by rw [hj]; push_cast; ring) hm
    · exact irr_transfer _ _ 0 (1 / 3) (by rw [hl]; push_cast; ring) hm
  refine ⟨D.model.angleAt i, D.model.oppLen i, D.model.oppLen j, D.model.oppLen l, hIrr,
    permOf i j l hij hil hjl, ?_, rfl, ?_, rfl, ?_, rfl⟩
  · rw [permOf_0]
  · rw [permOf_1, hj]
  · rw [permOf_2, hl]
theorem caseThreeTwo {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + D.model.angleAt j + 2 * D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : ThreeTwoCase D := by
  have hu : D.model.angleAt i = 2 * D.model.angleAt l + D.model.angleAt j := by linarith
  have hr2 : 3 * D.model.angleAt l + 2 * D.model.angleAt j = Real.pi := by linarith
  have hj : D.model.angleAt j = Real.pi / 2 - 3 / 2 * D.model.angleAt l := by linarith
  have hIrr : IrrPi (D.model.angleAt l) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact irr_transfer _ _ (1 / 2) (1 / 2) (by rw [hu, hj]; push_cast; ring) hm
    · exact irr_transfer _ _ (-3 / 2) (1 / 2) (by rw [hj]; push_cast; ring) hm
    · exact hm
  have hdata : D.model.ThreeAlphaData (D.model.angleAt l) (D.model.angleAt j)
      (D.model.oppLen l) (D.model.oppLen j) (D.model.oppLen i) :=
    ⟨permOf l j i hjl.symm hil.symm hij.symm, by rw [permOf_0], rfl, by rw [permOf_1], rfl,
      by rw [permOf_2, hu], rfl⟩
  refine ⟨_, _, _, _, _, hIrr, hr2, hdata, ?_⟩
  rcases shapes_threeTwo (fun k => D.target.angleAt k) _ _ _ P Q R hu hr2 hθ hP hQ hR hpos with
    h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact absurd (sim_of_TA D l j i hjl.symm hil.symm hij.symm h) hns
theorem caseTwoAlpha {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + 0 * D.model.angleAt j + 2 * D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 1) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : TwoAlphaCase D := by
  have hu : D.model.angleAt i = 2 * D.model.angleAt l := by linarith
  have hv : D.model.angleAt j = Real.pi - 3 * D.model.angleAt l := by linarith
  have hIrr : IrrPi (D.model.angleAt l) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact irr_transfer _ _ 2 0 (by rw [hu]; push_cast; ring) hm
    · exact irr_transfer _ _ (-3) 1 (by rw [hv]; push_cast; ring) hm
    · exact hm
  have hdata : D.model.TwoAlphaData (D.model.angleAt l) (D.model.oppLen l) (D.model.oppLen j)
      (D.model.oppLen i) :=
    ⟨permOf l j i hjl.symm hil.symm hij.symm, by rw [permOf_0], rfl, by rw [permOf_1, hv], rfl,
      by rw [permOf_2, hu], rfl⟩
  refine ⟨_, _, _, _, hIrr, hdata, ?_⟩
  rcases shapes_twoAlpha (fun k => D.target.angleAt k) _ _ _ P Q R hu hv hθ hP hQ hR hpos with h | h
  · obtain ⟨σ, h0, h1, -⟩ := h
    exact ⟨σ 0, σ 1, fun e => absurd (σ.injective e) (by decide), h0, h1⟩
  · exact absurd (sim_of_TA D l j i hjl.symm hil.symm hij.symm h) hns
theorem caseRight {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 2) (hR : R 0 + R 1 + R 2 = 2)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : RightCase D := by
  have hu : D.model.angleAt i = Real.pi / 2 := by linarith
  have hw : D.model.angleAt l = Real.pi / 2 - D.model.angleAt j := by linarith
  have hlpos : 0 < D.model.angleAt l := Erdos634.MarchFlank.cornerAngle_pos D.model l
  have hjpos : 0 < D.model.angleAt j := Erdos634.MarchFlank.cornerAngle_pos D.model j
  have hIrr : IrrPi (D.model.angleAt j) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact absurd ⟨1 / 2, by rw [hu]; push_cast; ring⟩ hm
    · exact hm
    · exact irr_transfer _ _ (-1) (1 / 2) (by rw [hw]; push_cast; ring) hm
  have hirrat : Irrational (D.model.angleAt j / Real.pi) := by
    rintro ⟨q, hq⟩
    apply hIrr
    refine ⟨q, ?_⟩
    have := Real.pi_pos.ne'
    field_simp at hq ⊢
    linarith
  refine ⟨D.model.angleAt j, hjpos, by linarith, hirrat, ⟨j, i, hij.symm, rfl, hu⟩, ?_⟩
  rcases shapes_right (fun k => D.target.angleAt k) _ _ _ P Q R hu hw hθ hP hQ hR hpos with
    h | h | h
  · obtain ⟨σ, h0, h1, -⟩ := h
    exact ⟨D.model.angleAt j, Or.inl rfl, σ 0, σ 1,
      fun e => absurd (σ.injective e) (by decide), h0, h1⟩
  · obtain ⟨σ, -, h1, h2⟩ := h
    exact ⟨D.model.angleAt l, Or.inr hw, σ 1, σ 2,
      fun e => absurd (σ.injective e) (by decide), h1, h2⟩
  · exact absurd (sim_of_TA D i j l hij hil hjl h) hns
theorem caseTwoPiThree {N : ℕ} (D : CongruentDissection N) (i j l : Fin 3)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (hirr : ∃ m, IrrPi (D.model.angleAt m)) (hns : ¬ SimilarTM D)
    (hsum : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi)
    (hrel : -D.model.angleAt i + 2 * D.model.angleAt j + 2 * D.model.angleAt l = 0)
    (P Q R : Fin 3 → ℕ)
    (hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l)
    (hP : P 0 + P 1 + P 2 = 0) (hQ : Q 0 + Q 1 + Q 2 = 3) (hR : R 0 + R 1 + R 2 = 3)
    (hpos : ∀ k, 1 ≤ P k + Q k + R k) : TwoPiThreeCase D := by
  have hu : D.model.angleAt i = 2 * Real.pi / 3 := by linarith
  have hv : D.model.angleAt j = Real.pi / 3 - D.model.angleAt l := by linarith
  have hIrr : IrrPi (D.model.angleAt l) := by
    obtain ⟨m, hm⟩ := hirr
    rcases key3 i j l m hij hil hjl with rfl | rfl | rfl
    · exact absurd ⟨2 / 3, by rw [hu]; push_cast; ring⟩ hm
    · exact irr_transfer _ _ (-1) (1 / 3) (by rw [hv]; push_cast; ring) hm
    · exact hm
  have hdata : D.model.TwoPiThreeData (D.model.angleAt l) (D.model.oppLen l) (D.model.oppLen j)
      (D.model.oppLen i) :=
    ⟨permOf l j i hjl.symm hil.symm hij.symm, by rw [permOf_0], rfl, by rw [permOf_1, hv], rfl,
      by rw [permOf_2, hu], rfl⟩
  have hθ' : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i
      + (Q k : ℝ) * (Real.pi / 3 - D.model.angleAt l) + (R k : ℝ) * D.model.angleAt l := by
    intro k; rw [hθ k, hv]
  refine ⟨_, _, _, _, hIrr, hdata, ?_⟩
  rcases shapes_twoPiThree (fun k => D.target.angleAt k) _ _ _ P Q R hu rfl hθ' hP hQ hR hpos with
    h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · have h' : TA (fun k => D.target.angleAt k) (D.model.angleAt l) (D.model.angleAt j)
        (D.model.angleAt i) := by rw [hv]; exact h
    exact absurd (sim_of_TA D l j i hjl.symm hil.symm hij.symm h') hns
theorem lemmaC_general {N : ℕ} (D : CongruentDissection N)
    (hirr : ∃ k, IrrPi (D.model.angleAt k)) (hns : ¬ SimilarTM D) :
    RightCase D ∨ TwoAlphaCase D ∨ SixtyTile D ∨ TwoPiThreeCase D ∨ ThreeTwoCase D := by
  have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  by_cases iso : ∃ p q : Fin 3, p ≠ q ∧ D.model.angleAt p = D.model.angleAt q
  · obtain ⟨p, q, hpq, he⟩ := iso
    have h3 : ∀ p q : Fin 3, p ≠ q → ∃ r, p ≠ r ∧ q ≠ r := by decide
    obtain ⟨r, hpr, hqr⟩ := h3 p q hpq
    exact absurd (Erdos634.Draft.LemmaCIso.iso_similar D p q r hpq hpr hqr he hirr) hns
  push Not at iso
  set α := D.model.angleAt 0 with hα
  set β := D.model.angleAt 1 with hβ
  set γ := D.model.angleAt 2 with hγ
  have hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = α := rfl
  have hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = β := rfl
  have hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = γ := rfl
  have hαβ : α ≠ β := iso 0 1 (by decide)
  have hαγ : α ≠ γ := iso 0 2 (by decide)
  have hβγ : β ≠ γ := iso 1 2 (by decide)
  have hpos : ∀ m, 0 < D.model.angleAt m := fun m => Erdos634.MarchFlank.cornerAngle_pos D.model m
  have hlt : ∀ m, D.model.angleAt m < Real.pi := fun m =>
    Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model m
  have hxm : ∀ m, (![α, β, γ] : Fin 3 → ℝ) m = D.model.angleAt m := by
    intro m; rcases fin3 m with rfl | rfl | rfl <;> rfl
  have hirr' : ∃ i, ¬ ∃ r : ℚ, (![α, β, γ] : Fin 3 → ℝ) i = (r : ℝ) * Real.pi := by
    obtain ⟨k, hk⟩ := hirr
    exact ⟨k, by rw [hxm]; exact hk⟩
  have hne := Erdos634.Draft.LemmaCSimilar.cfig_ne_of_notSimilar D α β γ hmα hmβ hmγ hαβ hαγ hβγ
    (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) hns
  obtain ⟨d, hd1, hd2, hd3, hd4, hd5, hd6⟩ := lemmaC_geometric D α β γ hmα hmβ hmγ hαβ hαγ hβγ
    (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) hirr' hne
  have hm : d 0 = -1 ∨ d 1 = -1 ∨ d 2 = -1 := by
    obtain ⟨j, hj⟩ := hd3; rcases fin3 j with rfl | rfl | rfl <;> simp_all
  have hp : 0 < d 0 ∨ 0 < d 1 ∨ 0 < d 2 := by
    obtain ⟨j, hj⟩ := hd4; rcases fin3 j with rfl | rfl | rfl <;> simp_all
  obtain ⟨i, j, l, hij, hjl, hil, hmem⟩ := Erdos634.Draft.LemmaCArith.enum_six (d 0) (d 1) (d 2)
    (hd2 0) (hd2 1) (hd2 2) hm hp hd5
  have hdi : ∀ m, (![d 0, d 1, d 2] : Fin 3 → ℤ) m = d m := by
    intro m; rcases fin3 m with rfl | rfl | rfl <;> rfl
  simp only [hdi, Erdos634.Draft.LemmaCArith.sixVectors, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq] at hmem
  have hsumπ : D.model.angleAt i + D.model.angleAt j + D.model.angleAt l = Real.pi := by
    rw [sum3 (fun m => D.model.angleAt m) i j l hij hil hjl]
    exact Erdos634.Geometry.cornerAngle_sum D.model
  have hrel : (d i : ℝ) * D.model.angleAt i + (d j : ℝ) * D.model.angleAt j
      + (d l : ℝ) * D.model.angleAt l = 0 := by
    rw [sum3 (fun m => (d m : ℝ) * D.model.angleAt m) i j l hij hil hjl]
    exact hd6
  have hcorner := fun kk => Erdos634.Draft.LemmaCFigures.corner_figure D α β γ hmα hmβ hmγ hαβ hαγ
    hβγ (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) kk
  set P : Fin 3 → ℕ := fun k => cnt D (D.model.angleAt i) (D.target.pts k) with hP
  set Q : Fin 3 → ℕ := fun k => cnt D (D.model.angleAt j) (D.target.pts k) with hQ
  set R : Fin 3 → ℕ := fun k => cnt D (D.model.angleAt l) (D.target.pts k) with hR
  have hθ : ∀ k, D.target.angleAt k = (P k : ℝ) * D.model.angleAt i + (Q k : ℝ) * D.model.angleAt j
      + (R k : ℝ) * D.model.angleAt l := by
    intro k
    have h := (hcorner k).2.1
    have h2 := sum3 (fun m => ((cnt D (D.model.angleAt m) (D.target.pts k) : ℕ) : ℝ) *
      D.model.angleAt m) i j l hij hil hjl
    try simp only [Fin.sum_univ_three] at h2
    have hk : D.target.angleAt k = cornerAngle (D.target.pts (k + 1)) (D.target.pts k)
      (D.target.pts (k + 2)) := rfl
    rw [hk, ← h]
    simp only [hP, hQ, hR]
    simp only [cnt] at h2 ⊢
    linarith [h2]
  have hposk : ∀ k, 1 ≤ P k + Q k + R k := by
    intro k
    have h : 1 ≤ cnt D (D.model.angleAt 0) (D.target.pts k)
        + cnt D (D.model.angleAt 1) (D.target.pts k) + cnt D (D.model.angleAt 2) (D.target.pts k) :=
      (hcorner k).2.2
    have h2 := sum3 (fun m => cnt D (D.model.angleAt m) (D.target.pts k)) i j l hij hil hjl
    simp only [hP, hQ, hR] at h2 ⊢
    omega
  have htot : ∀ m, cnt D (D.model.angleAt m) (D.target.pts 0) + cnt D (D.model.angleAt m) (D.target.pts 1)
      + cnt D (D.model.angleAt m) (D.target.pts 2) = cfig D ![α, β, γ] m := by
    intro m
    simp only [cfig, Fin.sum_univ_three, hxm]
  have hPt : ∀ e : ℤ, d i = e → P 0 + P 1 + P 2 = (1 + e).toNat := by
    intro e he; have := hd1 i; have := htot i; simp only [hP]; omega
  have hQt : ∀ e : ℤ, d j = e → Q 0 + Q 1 + Q 2 = (1 + e).toNat := by
    intro e he; have := hd1 j; have := htot j; simp only [hQ]; omega
  have hRt : ∀ e : ℤ, d l = e → R 0 + R 1 + R 2 = (1 + e).toNat := by
    intro e he; have := hd1 l; have := htot l; simp only [hR]; omega
  have hc : ∀ (a b c : ℤ), d i = a → d j = b → d l = c →
      (a : ℝ) * D.model.angleAt i + (b : ℝ) * D.model.angleAt j + (c : ℝ) * D.model.angleAt l = 0 := by
    intro a b c ha hb hc'
    have := hrel; rw [ha, hb, hc'] at this; exact this
  rcases hmem with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
  · exfalso
    have := hc _ _ _ e1 e2 e3
    push_cast at this
    exact iso i j hij (by linarith)
  · refine Or.inr (Or.inl (caseTwoAlpha D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk))
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inl (caseRight D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk)
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inr (caseThreeTwo D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk))))
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inl (caseTwoPiThree D i j l hij hil hjl hirr hns hsumπ ?_ P Q R hθ ?_ ?_ ?_ hposk))))
    · have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
    · rw [hPt _ e1]; rfl
    · rw [hQt _ e2]; rfl
    · rw [hRt _ e3]; rfl
  · refine Or.inr (Or.inr (Or.inl (caseSixty D i j l hij hil hjl hirr hsumπ ?_)))
    have := hc _ _ _ e1 e2 e3; push_cast at this; linarith
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
theorem irrPi_ne {α : ℝ} (h : IrrPi α) (q : ℚ) : α ≠ (q : ℝ) * Real.pi := fun e => h ⟨q, e⟩
theorem irrPi_of_irrational {α : ℝ} (h : Irrational (α / Real.pi)) : IrrPi α := by
  rintro ⟨r, hr⟩
  apply h
  exact ⟨r, by rw [hr]; field_simp [Real.pi_pos.ne']⟩
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement
namespace Erdos634.Draft.LaczFormal
def CommAngles (T : Tri) : Prop := ∀ i j : Fin 3, ∃ q : ℚ, T.angleAt i = (q : ℝ) * T.angleAt j
theorem commAngles_iff (T : Tri) : CommAngles T ↔ ∀ k, ∃ q : ℚ, T.angleAt k = (q : ℝ) * Real.pi := by
  have hpos : ∀ k, 0 < T.angleAt k := fun k => Erdos634.MarchFlank.cornerAngle_pos T k
  constructor
  · intro h k
    choose q hq using fun i => h i 0
    have hsum := angleAt_sum T
    have h0 := hq 0; have h1 := hq 1; have h2 := hq 2
    have hS : Real.pi = ((q 0 : ℝ) + q 1 + q 2) * T.angleAt 0 := by
      rw [← hsum]; linear_combination h0 + h1 + h2
    have hS0 : ((q 0 : ℝ) + q 1 + q 2) ≠ 0 := by
      intro h; rw [h, zero_mul] at hS; exact Real.pi_pos.ne' hS
    refine ⟨q k / (q 0 + q 1 + q 2), ?_⟩
    push_cast
    rw [hq k]
    have : T.angleAt 0 = Real.pi / ((q 0 : ℝ) + q 1 + q 2) := by
      field_simp; linarith
    rw [this]; field_simp
  · rintro h i j
    obtain ⟨a, ha⟩ := h i
    obtain ⟨b, hb⟩ := h j
    have hb0 : (b : ℝ) ≠ 0 := by
      intro h0; have := hpos j; rw [hb, h0] at this; simp at this
    refine ⟨a / b, ?_⟩
    rw [ha, hb]; push_cast; field_simp
theorem lemma1a {N : ℕ} (D : CongruentDissection N) (h : CommAngles D.model) :
    CommAngles D.target := by
  rw [commAngles_iff] at h ⊢
  choose q hq using h
  set n : ℕ := (q 0).den * (q 1).den * (q 2).den with hn
  have hnpos : 0 < n := by
    simp only [hn]; exact Nat.mul_pos (Nat.mul_pos (q 0).den_pos (q 1).den_pos) (q 2).den_pos
  have hpos : ∀ k, 0 < D.model.angleAt k := fun k => Erdos634.MarchFlank.cornerAngle_pos D.model k
  have hqpos : ∀ k, 0 < q k := by
    intro k
    have := hpos k; rw [hq k] at this
    have h' : (0 : ℝ) < (q k : ℝ) := by
      by_contra hc; push Not at hc
      nlinarith [Real.pi_pos, mul_nonpos_of_nonpos_of_nonneg hc Real.pi_pos.le]
    exact_mod_cast h'
  have hnat : ∀ k, ∃ a : ℕ, D.model.angleAt k = a * Real.pi / n := by
    intro k
    have hd : (q k).den ∣ n := by
      fin_cases k
      · exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
      · exact dvd_mul_left _ _
    refine ⟨(q k).num.toNat * (n / (q k).den), ?_⟩
    have hden : ((q k).den : ℝ) ≠ 0 := by exact_mod_cast (q k).den_nz
    have hnz : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hcast : ((n / (q k).den : ℕ) : ℝ) = (n : ℝ) / (q k).den :=
      Nat.cast_div hd hden
    have hnum : (((q k).num.toNat : ℕ) : ℝ) = ((q k).num : ℝ) := by
      have : (0 : ℤ) ≤ (q k).num := Rat.num_nonneg.mpr (hqpos k).le
      exact_mod_cast Int.toNat_of_nonneg this
    rw [hq k, Rat.cast_def]
    push_cast
    rw [hcast, hnum]
    field_simp
  choose a ha using hnat
  intro k
  obtain ⟨u, hu⟩ := Erdos634.Geometry.CaseA.LemmaV.target_angle_nat D hnpos a ha k
  exact ⟨(u : ℚ) / n, by rw [hu]; push_cast; ring⟩
end Erdos634.Draft.LaczFormal
end

section
open scoped Classical
namespace Erdos634.Draft.LemmaPProof
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional
open Erdos634.VertexFigureReal Erdos634.RouteOneVertexKill
lemma irrPi_ne_pi_third {α : ℝ} (hα : IrrPi α) : α ≠ Real.pi / 3 := fun h =>
  hα ⟨1/3, by rw [h]; ring⟩
lemma irrPi_ne_two_thirds_minus {α : ℝ} (hα : IrrPi α) : α ≠ 2 * Real.pi / 3 - α := fun h =>
  hα ⟨1/3, by linarith⟩
lemma irrPi_ne_zero {α : ℝ} (hα : IrrPi α) : α ≠ 0 := fun h =>
  hα ⟨0, by rw [h]; ring⟩
lemma pi_third_ne_two_thirds_minus {α : ℝ} (hα : IrrPi α) : Real.pi / 3 ≠ 2 * Real.pi / 3 - α :=
  fun h => hα ⟨1/3, by linarith⟩
lemma pi_third_ne_zero : Real.pi / 3 ≠ 0 :=
  div_ne_zero Real.pi_ne_zero (by norm_num)
lemma two_thirds_minus_ne_zero {α : ℝ} (hα : IrrPi α) : 2 * Real.pi / 3 - α ≠ 0 := fun h =>
  hα ⟨2/3, by linarith⟩
lemma sixtyData_cornerAngle_mem {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hd : D.model.SixtyData α a b c) (i : Fin N) (j : Fin 3) :
    cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j) ((D.tile i).pts (j + 2))
      ∈ ({α, 2 * Real.pi / 3 - α, Real.pi / 3} : Finset ℝ) := by
  classical
  obtain ⟨σ, hσ0, -, hσ1, -, hσ2, -⟩ := hd
  obtain ⟨k, hk⟩ := congruent_corner_angles (D.tiles_congruent i).symm j
  rw [hk]; obtain ⟨m, rfl⟩ := σ.surjective k
  fin_cases m <;> simp only [Finset.mem_insert, Finset.mem_singleton]
  · exact Or.inl hσ0
  · exact Or.inr (Or.inl hσ1)
  · exact Or.inr (Or.inr hσ2)
lemma localAngle_at_vertex_mem {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hd : D.model.SixtyData α a b c) (k : Fin 3) (i : Fin N) :
    (D.tile i).localAngle (D.target.pts k)
      ∈ ({α, 2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) := by
  classical
  have hcas := corner_angle_sum D.toDissection k
  have hlt := cornerAngle_lt_pi D.target k
  have hnneg : ∀ m : Fin N, 0 ≤ (D.tile m).localAngle (D.target.pts k) :=
    fun m => (D.tile m).localAngle_nonneg _
  rcases Erdos634.PinPlumbing.localAngle_cases (D.tile i) (D.target.pts k) with
    ⟨j, _, hval⟩ | h2pi | hpi | h0
  · rw [hval]
    have hcm := sixtyData_cornerAngle_mem D hd i j
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcm ⊢; tauto
  · exfalso
    have hge2 : 2 * Real.pi ≤ ∑ i, (D.tile i).localAngle (D.target.pts k) :=
      h2pi.symm.le.trans (Finset.single_le_sum (fun m _ => hnneg m) (Finset.mem_univ i))
    linarith [hge2.trans_eq hcas, hlt, Real.pi_pos]
  · exfalso
    have hge1 : Real.pi ≤ ∑ i, (D.tile i).localAngle (D.target.pts k) :=
      hpi.symm.le.trans (Finset.single_le_sum (fun m _ => hnneg m) (Finset.mem_univ i))
    linarith [hge1.trans_eq hcas, hlt, Real.pi_pos]
  · simp [h0]
noncomputable def multOf {N : ℕ} (D : CongruentDissection N) (v : ℝ) (k : Fin 3) : ℕ :=
  ({i : Fin N | (D.tile i).localAngle (D.target.pts k) = v} : Finset (Fin N)).card
lemma per_vertex_eq {N : ℕ} (D : CongruentDissection N) {α a b c : ℝ}
    (hα : IrrPi α) (hd : D.model.SixtyData α a b c) (k : Fin 3) :
    D.target.angleAt k = (multOf D α k : ℝ) * α +
      (multOf D (2 * Real.pi / 3 - α) k : ℝ) * (2 * Real.pi / 3 - α) +
      (multOf D (Real.pi / 3) k : ℝ) * (Real.pi / 3) := by
  classical
  have hcas := corner_angle_sum D.toDissection k
  rw [show cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2))
      = D.target.angleAt k from rfl] at hcas
  have hmem : ∀ i, (D.tile i).localAngle (D.target.pts k) ∈
      ({α, 2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) :=
    fun i => localAngle_at_vertex_mem D hd k i
  rw [sum_by_value _ _ hmem] at hcas
  rw [← hcas]
  have hα23 : α ∉ ({2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) := by
    simp [irrPi_ne_two_thirds_minus hα, irrPi_ne_pi_third hα, irrPi_ne_zero hα]
  have h23_rest : 2 * Real.pi / 3 - α ∉ ({Real.pi / 3, 0} : Finset ℝ) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h1 | h2
    · exact pi_third_ne_two_thirds_minus hα h1.symm
    · exact two_thirds_minus_ne_zero hα h2
  have h13_0 : Real.pi / 3 ∉ ({0} : Finset ℝ) := by simp [pi_third_ne_zero]
  simp only [show ({α, 2 * Real.pi / 3 - α, Real.pi / 3, 0} : Finset ℝ) =
      insert α (insert (2 * Real.pi / 3 - α) (insert (Real.pi / 3) {0})) from rfl,
    Finset.sum_insert hα23, Finset.sum_insert h23_rest, Finset.sum_insert h13_0,
    Finset.sum_singleton, mul_zero, add_zero, multOf]
  ring
lemma target_angle_sum {N : ℕ} (D : CongruentDissection N) :
    D.target.angleAt 0 + D.target.angleAt 1 + D.target.angleAt 2 = Real.pi := by
  show cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) +
       cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) +
       cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = Real.pi
  exact Erdos634.Geometry.cornerAngle_sum D.target
theorem lemmaP_general {N : ℕ} (D : CongruentDissection N) (α a b c : ℝ) (hα : IrrPi α)
    (hd : D.model.SixtyData α a b c) (hB : ¬ SimilarTM D) : Equilateral D := by
  unfold Equilateral; intro k; classical
  have hpv0 := per_vertex_eq D hα hd 0
  have hpv1 := per_vertex_eq D hα hd 1
  have hpv2 := per_vertex_eq D hα hd 2
  have hpi := target_angle_sum D
  let SA : ℤ := (multOf D α 0 : ℤ) + multOf D α 1 + multOf D α 2
  let S23 : ℤ := (multOf D (2 * Real.pi / 3 - α) 0 : ℤ) +
    multOf D (2 * Real.pi / 3 - α) 1 + multOf D (2 * Real.pi / 3 - α) 2
  let S13 : ℤ := (multOf D (Real.pi / 3) 0 : ℤ) +
    multOf D (Real.pi / 3) 1 + multOf D (Real.pi / 3) 2
  have hglobal : (SA : ℝ) * α + (S23 : ℝ) * (2 * Real.pi / 3 - α) +
      (S13 : ℝ) * (Real.pi / 3) = Real.pi := by
    simp only [SA, S23, S13]; push_cast; linarith
  obtain ⟨hA, hB'⟩ := Erdos634.Geometry.angle_indep hα
    (3 * (SA - S23)) (2 * S23 + S13 - 3)
    (by simp only [SA, S23, S13]; push_cast; linarith)
  have heqA : SA = S23 := by omega
  have hsum3 : 2 * S23 + S13 = 3 := by omega
  have hs23_nn : 0 ≤ S23 := by
    simp only [S23]; positivity
  have hs23_le1 : S23 ≤ 1 := by omega
  have hS23_cases : S23 = 0 ∨ S23 = 1 := by omega
  rcases hS23_cases with hs0 | hs1
  · 
    have hSA0 : SA = 0 := by omega
    have hS130 : S13 = 3 := by omega
    have hSA_exp : (multOf D α 0 : ℤ) + multOf D α 1 + multOf D α 2 = 0 := by
      have h : SA = 0 := hSA0; simp only [SA] at h; exact h
    have hS23_exp : (multOf D (2 * Real.pi / 3 - α) 0 : ℤ) +
        multOf D (2 * Real.pi / 3 - α) 1 + multOf D (2 * Real.pi / 3 - α) 2 = 0 := by
      have h : S23 = 0 := hs0; simp only [S23] at h; exact h
    have hmα : ∀ j : Fin 3, multOf D α j = 0 := by
      have hsum : multOf D α 0 + multOf D α 1 + multOf D α 2 = 0 := by exact_mod_cast hSA_exp
      have e0 : multOf D α 0 = 0 := by omega
      have e1 : multOf D α 1 = 0 := by omega
      have e2 : multOf D α 2 = 0 := by omega
      intro j; fin_cases j; exact e0; exact e1; exact e2
    have hm23 : ∀ j : Fin 3, multOf D (2 * Real.pi / 3 - α) j = 0 := by
      have hsum : multOf D (2 * Real.pi / 3 - α) 0 + multOf D (2 * Real.pi / 3 - α) 1 +
          multOf D (2 * Real.pi / 3 - α) 2 = 0 := by exact_mod_cast hS23_exp
      have e0 : multOf D (2 * Real.pi / 3 - α) 0 = 0 := by omega
      have e1 : multOf D (2 * Real.pi / 3 - α) 1 = 0 := by omega
      have e2 : multOf D (2 * Real.pi / 3 - α) 2 = 0 := by omega
      intro j; fin_cases j; exact e0; exact e1; exact e2
    have ha : ∀ j : Fin 3, D.target.angleAt j = (multOf D (Real.pi / 3) j : ℝ) * (Real.pi / 3) := by
      intro j
      have hpv := per_vertex_eq D hα hd j
      have hαj : multOf D α j = 0 := hmα j
      have h23j : multOf D (2 * Real.pi / 3 - α) j = 0 := hm23 j
      rw [hpv, hαj, h23j]; push_cast; ring
    have hn13_each : ∀ j : Fin 3, multOf D (Real.pi / 3) j = 1 := by
      have hpos : ∀ j : Fin 3, 1 ≤ multOf D (Real.pi / 3) j := by
        intro j; by_contra hlt; push_neg at hlt
        have hj0 : multOf D (Real.pi / 3) j = 0 := Nat.lt_one_iff.mp hlt
        have hay := ha j; rw [hj0] at hay; push_cast at hay
        linarith [Tri.angleAt_pos' D.target j]
      have htot' : multOf D (Real.pi / 3) 0 + multOf D (Real.pi / 3) 1 +
          multOf D (Real.pi / 3) 2 = 3 := by
        have h : S13 = 3 := hS130; simp only [S13] at h; exact_mod_cast h
      have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
      have e0 : multOf D (Real.pi / 3) 0 = 1 := by omega
      have e1 : multOf D (Real.pi / 3) 1 = 1 := by omega
      have e2 : multOf D (Real.pi / 3) 2 = 1 := by omega
      intro j; fin_cases j
      · exact e0
      · exact e1
      · exact e2
    have hk := ha k; rw [hn13_each k] at hk; push_cast at hk; linarith
  · 
    exfalso; apply hB
    have hSA1 : SA = 1 := heqA.trans hs1
    have hS131 : S13 = 1 := by omega
    have hα_n : multOf D α 0 + multOf D α 1 + multOf D α 2 = 1 := by
      have h : SA = 1 := hSA1; simp only [SA] at h; exact_mod_cast h
    have h23_n : multOf D (2*Real.pi/3-α) 0 + multOf D (2*Real.pi/3-α) 1 +
        multOf D (2*Real.pi/3-α) 2 = 1 := by
      have h : S23 = 1 := hs1; simp only [S23] at h; exact_mod_cast h
    have h13_n : multOf D (Real.pi/3) 0 + multOf D (Real.pi/3) 1 +
        multOf D (Real.pi/3) 2 = 1 := by
      have h : S13 = 1 := hS131; simp only [S13] at h; exact_mod_cast h
    have hT_pos : ∀ j : Fin 3, 0 < multOf D α j + multOf D (2*Real.pi/3-α) j + multOf D (Real.pi/3) j := by
      intro j; by_contra hc; push_neg at hc
      have h0 : multOf D α j = 0 := by omega
      have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
      have h2 : multOf D (Real.pi/3) j = 0 := by omega
      have := per_vertex_eq D hα hd j; rw [h0, h1, h2] at this; push_cast at this
      linarith [Tri.angleAt_pos' D.target j]
    have hTe0 : multOf D α 0 + multOf D (2*Real.pi/3-α) 0 + multOf D (Real.pi/3) 0 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    have hTe1 : multOf D α 1 + multOf D (2*Real.pi/3-α) 1 + multOf D (Real.pi/3) 1 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    have hTe2 : multOf D α 2 + multOf D (2*Real.pi/3-α) 2 + multOf D (Real.pi/3) 2 = 1 := by
      have p0 := hT_pos 0; have p1 := hT_pos 1; have p2 := hT_pos 2; omega
    have hpv_val : ∀ j : Fin 3,
        (multOf D α j = 1 → D.target.angleAt j = α) ∧
        (multOf D (2*Real.pi/3-α) j = 1 → D.target.angleAt j = 2*Real.pi/3-α) ∧
        (multOf D (Real.pi/3) j = 1 → D.target.angleAt j = Real.pi/3) := by
      intro j
      have hTj : multOf D α j + multOf D (2*Real.pi/3-α) j + multOf D (Real.pi/3) j = 1 := by
        fin_cases j; exact hTe0; exact hTe1; exact hTe2
      have hpv := per_vertex_eq D hα hd j
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
        have h2 : multOf D (Real.pi/3) j = 0 := by omega
        rw [hpv, h, h1, h2]; push_cast; ring
      · have h0 : multOf D α j = 0 := by omega
        have h2 : multOf D (Real.pi/3) j = 0 := by omega
        rw [hpv, h0, h, h2]; push_cast; ring
      · have h0 : multOf D α j = 0 := by omega
        have h1 : multOf D (2*Real.pi/3-α) j = 0 := by omega
        rw [hpv, h0, h1, h]; push_cast; ring
    obtain ⟨σ, hσα, hσα_len, hσ23, hσ23_len, hσ13, hσ13_len⟩ := hd
    have oppLen_ratio : ∀ (τ : Equiv.Perm (Fin 3)) (k : Fin 3),
        (∀ j : Fin 3, D.target.angleAt j = D.model.angleAt (τ j)) →
        D.target.oppLen k * D.model.oppLen (τ 0) = D.target.oppLen 0 * D.model.oppLen (τ k) := by
      intro τ k hangle
      have hls_t : Real.sin (D.model.angleAt (τ 0)) * D.target.oppLen k =
          Real.sin (D.model.angleAt (τ k)) * D.target.oppLen 0 := by
        have := Tri.lawSin D.target 0 k; rw [hangle 0, hangle k] at this; exact this
      have hls_m : Real.sin (D.model.angleAt (τ 0)) * D.model.oppLen (τ k) =
          Real.sin (D.model.angleAt (τ k)) * D.model.oppLen (τ 0) :=
        Tri.lawSin D.model (τ 0) (τ k)
      have hsin0 : 0 < Real.sin (D.model.angleAt (τ 0)) :=
        Real.sin_pos_of_pos_of_lt_pi (Tri.angleAt_pos' D.model (τ 0)) (cornerAngle_lt_pi D.model (τ 0))
      have step : Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen k * D.model.oppLen (τ 0)) =
          Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen 0 * D.model.oppLen (τ k)) :=
        calc Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen k * D.model.oppLen (τ 0))
            = Real.sin (D.model.angleAt (τ 0)) * D.target.oppLen k * D.model.oppLen (τ 0) := by ring
          _ = Real.sin (D.model.angleAt (τ k)) * D.target.oppLen 0 * D.model.oppLen (τ 0) := by rw [hls_t]
          _ = D.target.oppLen 0 * (Real.sin (D.model.angleAt (τ k)) * D.model.oppLen (τ 0)) := by ring
          _ = D.target.oppLen 0 * (Real.sin (D.model.angleAt (τ 0)) * D.model.oppLen (τ k)) := by rw [hls_m]
          _ = Real.sin (D.model.angleAt (τ 0)) * (D.target.oppLen 0 * D.model.oppLen (τ k)) := by ring
      exact mul_left_cancel₀ (ne_of_gt hsin0) step
    have hα_case : (multOf D α 0 = 1 ∧ multOf D α 1 = 0 ∧ multOf D α 2 = 0) ∨
        (multOf D α 0 = 0 ∧ multOf D α 1 = 1 ∧ multOf D α 2 = 0) ∨
        (multOf D α 0 = 0 ∧ multOf D α 1 = 0 ∧ multOf D α 2 = 1) := by omega
    have build_similar : ∀ (τ : Equiv.Perm (Fin 3)),
        (∀ j : Fin 3, D.target.angleAt j = D.model.angleAt (τ j)) → SimilarTM D := by
      intro τ hangle
      exact ⟨D.target.oppLen 0 / D.model.oppLen (τ 0), τ, fun k => ⟨hangle k, by
        rcases Nat.eq_zero_or_pos k.val with hk | hk
        · have : k = 0 := by ext; exact hk
          subst this; simp [div_mul_cancel₀, ne_of_gt (Tri.oppLen_pos D.model (τ 0))]
        · have hrat := oppLen_ratio τ k hangle
          have hpos := Tri.oppLen_pos D.model (τ 0)
          field_simp [ne_of_gt hpos]; linarith [hrat]⟩⟩
    rcases hα_case with ⟨hα0, hα10, hα20⟩ | ⟨hα00, hα1, hα20⟩ | ⟨hα00, hα10, hα2⟩
    · 
      have h23_02 : multOf D (2*Real.pi/3-α) 0 = 0 := by have := hTe0; omega
      have h13_02 : multOf D (Real.pi/3) 0 = 0 := by have := hTe0; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 1 = 1 ∧ multOf D (2*Real.pi/3-α) 2 = 0) ∨
          (multOf D (2*Real.pi/3-α) 1 = 0 ∧ multOf D (2*Real.pi/3-α) 2 = 1) := by omega
      rcases h23_case with ⟨h231, h232⟩ | ⟨h231, h232⟩
      · 
        have h13_2 : multOf D (Real.pi/3) 2 = 1 := by have := hTe2; omega
        have hta0 := (hpv_val 0).1 hα0
        have hta1 := (hpv_val 1).2.1 h231
        have hta2 := (hpv_val 2).2.2 h13_2
        exact build_similar σ (fun k => by
          fin_cases k
          · simp [hta0, hσα]
          · simp [hta1, hσ23]
          · simp [hta2, hσ13])
      · 
        have h13_1 : multOf D (Real.pi/3) 1 = 1 := by have := hTe1; omega
        have hta0 := (hpv_val 0).1 hα0
        have hta1 := (hpv_val 1).2.2 h13_1
        have hta2 := (hpv_val 2).2.1 h232
        exact build_similar ((Equiv.swap (1:Fin 3) 2).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 0); rw [hta0, hσα]
          · change D.target.angleAt 1 = D.model.angleAt (σ 2); rw [hta1, hσ13]
          · change D.target.angleAt 2 = D.model.angleAt (σ 1); rw [hta2, hσ23])
    · 
      have h23_12 : multOf D (2*Real.pi/3-α) 1 = 0 := by have := hTe1; omega
      have h13_12 : multOf D (Real.pi/3) 1 = 0 := by have := hTe1; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 0 = 1 ∧ multOf D (2*Real.pi/3-α) 2 = 0) ∨
          (multOf D (2*Real.pi/3-α) 0 = 0 ∧ multOf D (2*Real.pi/3-α) 2 = 1) := by omega
      rcases h23_case with ⟨h230, h232⟩ | ⟨h230, h232⟩
      · 
        have h13_2 : multOf D (Real.pi/3) 2 = 1 := by have := hTe2; omega
        have hta0 := (hpv_val 0).2.1 h230
        have hta1 := (hpv_val 1).1 hα1
        have hta2 := (hpv_val 2).2.2 h13_2
        exact build_similar ((Equiv.swap (0:Fin 3) 1).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 1); rw [hta0, hσ23]
          · change D.target.angleAt 1 = D.model.angleAt (σ 0); rw [hta1, hσα]
          · change D.target.angleAt 2 = D.model.angleAt (σ 2); rw [hta2, hσ13])
      · 
        have h13_0 : multOf D (Real.pi/3) 0 = 1 := by have := hTe0; omega
        have hta0 := (hpv_val 0).2.2 h13_0
        have hta1 := (hpv_val 1).1 hα1
        have hta2 := (hpv_val 2).2.1 h232
        exact build_similar (((Equiv.swap (0:Fin 3) 2).trans (Equiv.swap 0 1)).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 2); rw [hta0, hσ13]
          · change D.target.angleAt 1 = D.model.angleAt (σ 0); rw [hta1, hσα]
          · change D.target.angleAt 2 = D.model.angleAt (σ 1); rw [hta2, hσ23])
    · 
      have h23_22 : multOf D (2*Real.pi/3-α) 2 = 0 := by have := hTe2; omega
      have h13_22 : multOf D (Real.pi/3) 2 = 0 := by have := hTe2; omega
      have h23_case : (multOf D (2*Real.pi/3-α) 0 = 1 ∧ multOf D (2*Real.pi/3-α) 1 = 0) ∨
          (multOf D (2*Real.pi/3-α) 0 = 0 ∧ multOf D (2*Real.pi/3-α) 1 = 1) := by omega
      rcases h23_case with ⟨h230, h231⟩ | ⟨h230, h231⟩
      · 
        have h13_1 : multOf D (Real.pi/3) 1 = 1 := by have := hTe1; omega
        have hta0 := (hpv_val 0).2.1 h230
        have hta1 := (hpv_val 1).2.2 h13_1
        have hta2 := (hpv_val 2).1 hα2
        exact build_similar (((Equiv.swap (0:Fin 3) 1).trans (Equiv.swap 0 2)).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 1); rw [hta0, hσ23]
          · change D.target.angleAt 1 = D.model.angleAt (σ 2); rw [hta1, hσ13]
          · change D.target.angleAt 2 = D.model.angleAt (σ 0); rw [hta2, hσα])
      · 
        have h13_0 : multOf D (Real.pi/3) 0 = 1 := by have := hTe0; omega
        have hta0 := (hpv_val 0).2.2 h13_0
        have hta1 := (hpv_val 1).2.1 h231
        have hta2 := (hpv_val 2).1 hα2
        exact build_similar ((Equiv.swap (0:Fin 3) 2).trans σ) (fun k => by
          fin_cases k
          · change D.target.angleAt 0 = D.model.angleAt (σ 2); rw [hta0, hσ13]
          · change D.target.angleAt 1 = D.model.angleAt (σ 1); rw [hta1, hσ23]
          · change D.target.angleAt 2 = D.model.angleAt (σ 0); rw [hta2, hσα])
end Erdos634.Draft.LemmaPProof
end

section
open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Draft.TheoremPConditional Erdos634.Draft.LemmaCFinal
namespace Erdos634.Draft.LaczFormal
theorem tgt_mem {N : ℕ} {D : CongruentDissection N} {x y z : ℝ} (h : TgtAngles D x y z) :
    (∃ k, D.target.angleAt k = x) ∧ (∃ k, D.target.angleAt k = y) ∧ ∃ k, D.target.angleAt k = z := by
  obtain ⟨σ, h0, h1, h2⟩ := h
  exact ⟨⟨_, h0⟩, ⟨_, h1⟩, ⟨_, h2⟩⟩
theorem lemma1b {N : ℕ} (D : CongruentDissection N) (hne : ¬ Equilateral D)
    (h : CommAngles D.target) : CommAngles D.model := by
  by_contra hm
  rw [commAngles_iff] at h hm
  have hirr : ∃ k, IrrPi (D.model.angleAt k) := by
    by_contra hc; push Not at hc
    exact hm (fun k => by by_contra hk; exact hc k hk)
  have hT : ∀ x : ℝ, (∃ k, D.target.angleAt k = x) → ∃ q : ℚ, x = (q : ℝ) * Real.pi := by
    rintro x ⟨k, rfl⟩; exact h k
  by_cases hs : SimilarTM D
  · obtain ⟨μ, τ, hh⟩ := hs
    obtain ⟨k, hk⟩ := hirr
    obtain ⟨q, hq⟩ := h (τ.symm k)
    have := (hh (τ.symm k)).1
    rw [Equiv.apply_symm_apply] at this
    exact hk ⟨q, by rw [← this]; exact hq⟩
  rcases lemmaC_general D hirr hs with hc | hc | hc | hc | hc
  · 
    obtain ⟨α, -, -, hα0, -, γ, hγ, i, j, -, hi, -⟩ := hc
    have hα := irrPi_of_irrational hα0
    obtain ⟨q, hq⟩ := hT γ ⟨i, hi⟩
    rcases hγ with e | e
    · exact irrPi_ne hα q (by rw [← e]; exact hq)
    · exact irrPi_ne hα (1 / 2 - q) (by push_cast; linarith)
  · obtain ⟨α, a, b, c, hα, -, i, j, -, hi, -⟩ := hc
    obtain ⟨q, hq⟩ := hT α ⟨i, hi⟩
    exact irrPi_ne hα q hq
  · obtain ⟨α, a, b, c, hα, hd⟩ := hc
    exact hne (Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hs)
  · obtain ⟨α, a, b, c, hα, hd, hsh⟩ := hc
    rcases hsh with hE | hI | hF1 | hF2
    · exact hne hE
    · rcases hI with e | e
      · obtain ⟨q, hq⟩ := hT α (tgt_mem e).1
        exact irrPi_ne hα q hq
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα (1 / 3 - q) (by push_cast; linarith)
    · rcases hF1 with e | e
      · obtain ⟨q, hq⟩ := hT α (tgt_mem e).1
        exact irrPi_ne hα q hq
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα (1 / 3 - q) (by push_cast; linarith)
    · rcases hF2 with e | e | e | e | e
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα (q / 2) (by push_cast; linarith)
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα q hq
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα (1 / 3 - q) (by push_cast; linarith)
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα q hq
      · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
        exact irrPi_ne hα (1 / 3 - q) (by push_cast; linarith)
  · obtain ⟨α, β, a, b, c, hα, hrel, hd, hsh⟩ := hc
    rcases hsh with e | e | e | e | e
    · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
      exact irrPi_ne hα ((1 - 2 * q) / 3) (by push_cast; linarith)
    · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).2.2
      exact irrPi_ne hα q hq
    · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
      exact irrPi_ne hα (q / 2) (by push_cast; linarith)
    · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).2.1
      exact irrPi_ne hα q hq
    · obtain ⟨q, hq⟩ := hT _ (tgt_mem e).1
      exact irrPi_ne hα q hq
theorem lemma1 {N : ℕ} (D : CongruentDissection N) :
    (CommAngles D.model → CommAngles D.target) ∧
      (¬ Equilateral D → CommAngles D.target → CommAngles D.model) :=
  ⟨lemma1a D, lemma1b D⟩
end Erdos634.Draft.LaczFormal
end

section
namespace TriangleTiling.Prime
open Erdos634.Geometry EuclideanGeometry Real
open Erdos634.Draft.LaczFormal (CommAngles commAngles_iff)
theorem RandT {N : ℕ} (D : CongruentDissection N) :
    (CommAngles D.model → CommAngles D.target) ∧
      (¬ Erdos634.Draft.TheoremPConditional.Equilateral D → CommAngles D.target →
        CommAngles D.model) :=
  Erdos634.Draft.LaczFormal.lemma1 D
end TriangleTiling.Prime
end

section
namespace TriangleTiling.Laczkovich
open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles TileAngles.swap)
variable {N : ℕ} (D : CongruentDissection N)
def RightRow : Prop :=
  ∃ α β : ℝ, TileAngles D α β (Real.pi / 2) ∧ TgtAngles D α α (2 * β)
theorem fin3_third : ∀ p q : Fin 3, p ≠ q → ∃ r, r ≠ p ∧ r ≠ q := by decide
theorem angleAt_sum3 (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    T.angleAt p + T.angleAt q + T.angleAt r = Real.pi := by
  rw [Erdos634.Draft.LemmaCFinal.sum3 T.angleAt p q r hpq hpr hqr]
  exact T.angleAt_sum
theorem triple_of (T : Tri) {p q r : Fin 3} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ σ : Equiv.Perm (Fin 3), T.angleAt (σ 0) = T.angleAt p ∧ T.angleAt (σ 1) = T.angleAt q ∧
      T.angleAt (σ 2) = T.angleAt r := by
  refine ⟨Erdos634.Draft.LemmaCFinal.permOf p q r hpq hpr hqr, ?_, ?_, ?_⟩
  · rw [Erdos634.Draft.LemmaCFinal.permOf_0]
  · rw [Erdos634.Draft.LemmaCFinal.permOf_1]
  · rw [Erdos634.Draft.LemmaCFinal.permOf_2]
theorem tgt_of_two {i j : Fin 3} (hij : i ≠ j) {x : ℝ} (hi : D.target.angleAt i = x)
    (hj : D.target.angleAt j = x) : TgtAngles D x x (Real.pi - 2 * x) := by
  obtain ⟨r, hri, hrj⟩ := fin3_third i j hij
  have hs := angleAt_sum3 D.target hij hri.symm hrj.symm
  obtain ⟨σ, h0, h1, h2⟩ := triple_of D.target hij hri.symm hrj.symm
  exact ⟨σ, h0.trans hi, h1.trans hj, by rw [h2]; linarith⟩
theorem rightRow_of {k l : Fin 3} (hlk : l ≠ k) (hk : D.model.angleAt k = Real.pi / 2)
    {j₁ j₂ : Fin 3} (hj : j₁ ≠ j₂) (h1 : D.target.angleAt j₁ = D.model.angleAt l)
    (h2 : D.target.angleAt j₂ = D.model.angleAt l) : RightRow D := by
  obtain ⟨m, hml, hmk⟩ := fin3_third l k hlk
  have hs := angleAt_sum3 D.model hml.symm hlk hmk
  obtain ⟨σ, h0, h1', h2'⟩ := triple_of D.model hml.symm hlk hmk
  refine ⟨D.model.angleAt l, D.model.angleAt m, ⟨σ, h0, h1', h2'.trans hk⟩, ?_⟩
  obtain ⟨τ, t0, t1, t2⟩ := tgt_of_two D hj h1 h2
  exact ⟨τ, t0, t1, by rw [t2]; linarith⟩
theorem tgtAngles_of_eq {x y z x' y' z' : ℝ} (h : TgtAngles D x y z) (hx : x = x') (hy : y = y')
    (hz : z = z') : TgtAngles D x' y' z' := by
  subst hx hy hz; exact h
theorem table_incommensurable (hirr : ∃ k, IrrPi (D.model.angleAt k)) :
    SimilarTM D ∨ RightRow D ∨
    (Equilateral D ∧ ∃ α, IrrPi α ∧ TileAngles D α (2 * Real.pi / 3 - α) (Real.pi / 3)) ∨
    (∃ α, IrrPi α ∧ TileAngles D α (Real.pi - 3 * α) (2 * α) ∧
      TgtAngles D α α (Real.pi - 2 * α)) ∨
    (∃ α β, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      (TgtAngles D β β (3 * α) ∨ TgtAngles D (α + β) (α + β) α ∨
        TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D (2 * α) α (2 * β) ∨
        TgtAngles D α α (α + 2 * β))) ∨
    (∃ α, IrrPi α ∧ TileAngles D α (Real.pi / 3 - α) (2 * Real.pi / 3) ∧
      (Equilateral D ∨ IsoTP D α ∨ F1Shape D α ∨ F2to4Shape D α)) := by
  by_cases hs : SimilarTM D
  · exact Or.inl hs
  right
  rcases Erdos634.Draft.LemmaCFinal.lemmaC_general D hirr hs with h | h | h | h | h
  · 
    obtain ⟨α, -, -, -, ⟨p, q, hpq, hp, hq⟩, γ, hγ, i, j, hij, hi, hj⟩ := h
    left
    obtain ⟨r, hrp, hrq⟩ := fin3_third p q hpq
    have hs3 := angleAt_sum3 D.model hpq hrp.symm hrq.symm
    rcases hγ with rfl | rfl
    · exact rightRow_of D hpq hq hij (hi.trans hp.symm) (hj.trans hp.symm)
    · have hr : D.model.angleAt r = Real.pi / 2 - α := by linarith
      exact rightRow_of D hrq hq hij (hi.trans hr.symm) (hj.trans hr.symm)
  · 
    obtain ⟨α, a, b, c, hα, ⟨σ, h0, -, h1, -, h2, -⟩, i, j, hij, hi, hj⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨α, hα, ⟨σ, h0, h1, h2⟩, tgt_of_two D hij hi hj⟩))
  · 
    obtain ⟨α, a, b, c, hα, hd⟩ := h
    have heq := Erdos634.Draft.LemmaPProof.lemmaP_general D α a b c hα hd hs
    obtain ⟨σ, h0, -, h1, -, h2, -⟩ := hd
    exact Or.inr (Or.inl ⟨heq, α, hα, ⟨σ, h0, h1, h2⟩⟩)
  · 
    obtain ⟨α, a, b, c, hα, ⟨σ, h0, -, h1, -, h2, -⟩, hshape⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨α, hα, ⟨σ, h0, h1, h2⟩, hshape⟩)))
  · 
    obtain ⟨α, β, a, b, c, hα, hrel, ⟨σ, h0, -, h1, -, h2, -⟩, hshape⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨α, β, hα, hrel, ⟨σ, h0, h1, h2⟩, hshape⟩)))
end TriangleTiling.Laczkovich
end

section
namespace TriangleTiling.Prime
open Erdos634.Geometry EuclideanGeometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles TileAngles.swap)
open TriangleTiling.Laczkovich
variable {N : ℕ} (D : CongruentDissection N)
theorem not_iso_tgt (hniso : ∀ i j : Fin 3, i ≠ j → D.target.angleAt i ≠ D.target.angleAt j)
    {x z : ℝ} (h : TgtAngles D x x z) : False := by
  obtain ⟨σ, h0, h1, -⟩ := h
  exact hniso (σ 0) (σ 1) (fun e => absurd (σ.injective e) (by decide)) (h0.trans h1.symm)
theorem irr_compl {α : ℝ} (h : IrrPi α) : IrrPi (Real.pi / 3 - α) := by
  rintro ⟨r, hr⟩
  exact h ⟨1 / 3 - r, by push_cast; linarith⟩
theorem «l1995-4.1» (hirr : ∃ k, IrrPi (D.model.angleAt k))
    (hniso : ∀ i j : Fin 3, i ≠ j → D.target.angleAt i ≠ D.target.angleAt j) :
    SimilarTM D ∨
    (∃ α β : ℝ, IrrPi α ∧ 3 * α + 2 * β = Real.pi ∧ TileAngles D α β (2 * α + β) ∧
      (TgtAngles D α (2 * α) (2 * β) ∨ TgtAngles D (2 * α) β (α + β))) ∨
    (∃ α β : ℝ, IrrPi α ∧ 3 * α + 3 * β = Real.pi ∧ TileAngles D α β (2 * Real.pi / 3) ∧
      (TgtAngles D α (2 * α) (3 * β) ∨ TgtAngles D α (2 * β) (2 * α + β) ∨
        TgtAngles D α (α + β) (α + 2 * β) ∨ TgtAngles D (2 * α) (2 * β) (α + β))) := by
  have heq : ¬ Equilateral D := fun h =>
    hniso 0 1 (by decide) ((h 0).trans (h 1).symm)
  rcases table_incommensurable D hirr with h | ⟨α, β, -, h⟩ | ⟨h, -⟩ | ⟨α, -, -, h⟩ |
      ⟨α, β, hα, hrel, hT, h⟩ | ⟨α, hα, hT, h⟩
  · exact Or.inl h
  · exact (not_iso_tgt D hniso h).elim
  · exact (heq h).elim
  · exact (not_iso_tgt D hniso h).elim
  · 
    rcases h with h | h | h | h | h
    · exact (not_iso_tgt D hniso h).elim
    · exact (not_iso_tgt D hniso h).elim
    · exact Or.inr (Or.inl ⟨α, β, hα, hrel, hT, Or.inr h⟩)
    · obtain ⟨σ, h0, h1, h2⟩ := h
      refine Or.inr (Or.inl ⟨α, β, hα, hrel, hT, Or.inl ⟨(Equiv.swap (0 : Fin 3) 1).trans σ,
        ?_, ?_, ?_⟩⟩)
      · simpa using h1
      · simpa using h0
      · simp only [Equiv.trans_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; exact h2
    · exact (not_iso_tgt D hniso h).elim
  · 
    right; right
    have hrel : 3 * α + 3 * (Real.pi / 3 - α) = Real.pi := by ring
    have hrel' : 3 * (Real.pi / 3 - α) + 3 * α = Real.pi := by ring
    have hT' := TileAngles.swap hT
    have hα' := irr_compl hα
    rcases h with h | h | h | h
    · exact (heq h).elim
    · rcases h with h | h <;> exact (not_iso_tgt D hniso h).elim
    · rcases h with h | h
      · exact ⟨α, _, hα, hrel, hT, Or.inr (Or.inr (Or.inl h))⟩
      · refine ⟨_, α, hα', hrel', hT', Or.inr (Or.inr (Or.inl ?_))⟩
        exact tgtAngles_of_eq D h rfl (by ring) (by ring)
    · rcases h with h | h | h | h | h
      · exact ⟨α, _, hα, hrel, hT, Or.inr (Or.inr (Or.inr h))⟩
      · exact ⟨α, _, hα, hrel, hT, Or.inl h⟩
      · refine ⟨_, α, hα', hrel', hT', Or.inl ?_⟩
        exact tgtAngles_of_eq D h rfl rfl (by ring)
      · exact ⟨α, _, hα, hrel, hT, Or.inr (Or.inl h)⟩
      · refine ⟨_, α, hα', hrel', hT', Or.inr (Or.inl ?_)⟩
        exact tgtAngles_of_eq D h rfl rfl (by ring)
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


namespace OMA.E634H

theorem comp_vec {f : Fin 3 → ℝ} {σ : Equiv.Perm (Fin 3)} {x y z : ℝ} (h0 : f (σ 0) = x)
    (h1 : f (σ 1) = y) (h2 : f (σ 2) = z) : f ∘ σ = ![x, y, z] := by
  funext k; fin_cases k <;> simp [h0, h1, h2]

theorem vec_comp {f : Fin 3 → ℝ} {σ : Equiv.Perm (Fin 3)} {x y z : ℝ} (h : f ∘ σ = ![x, y, z]) :
    f (σ 0) = x ∧ f (σ 1) = y ∧ f (σ 2) = z :=
  ⟨by simpa using congrFun h 0, by simpa using congrFun h 1, by simpa using congrFun h 2⟩

end OMA.E634H


/-- Step H1 of erdos-634.R1.H4.R1: Laczkovich's classification (1995, Theorem 4.1) for a scalene
target with an angle not in Q pi, not similar to the tile. -/
theorem OMA.solution : OMA.R_erdos_634_R1_H4_R1.H1 := by
  intro p hp h3 T Ts hc hd hu t A B hA hB hiso hcomm hsim
  obtain rfl : A = _ := funext hA
  obtain rfl : B = _ := funext hB
  let D := OMA.E634S.mk T Ts hc hd hu t
  have hniso : ∀ i j : Fin 3, i ≠ j → D.target.angleAt i ≠ D.target.angleAt j := hiso
  have hnc : ¬ Erdos634.Draft.LaczFormal.CommAngles D.target := by
    intro h
    rw [Erdos634.Draft.LaczFormal.commAngles_iff] at h
    exact hcomm h
  have hirr : ∃ k, Erdos634.Draft.TheoremPConditional.IrrPi (D.model.angleAt k) := by
    by_contra h
    apply hnc
    apply (TriangleTiling.Prime.RandT D).1
    rw [Erdos634.Draft.LaczFormal.commAngles_iff]
    intro k
    exact not_not.mp (fun hk => h ⟨k, hk⟩)
  rcases TriangleTiling.Prime.«l1995-4.1» D hirr hniso with h | ⟨α, β, hα, hrel, hTA, h⟩ |
      ⟨α, β, hα, hrel, hTA, h⟩
  · obtain ⟨μ, τ, hμ⟩ := h
    exact (hsim ⟨τ, funext fun k => (hμ k).1⟩).elim
  · left
    obtain ⟨σ, h0, h1, h2⟩ := hTA
    refine ⟨α, β, hα, hrel, ⟨σ, OMA.E634H.comp_vec h0 h1 h2⟩, ?_⟩
    rcases h with ⟨τ, g0, g1, g2⟩ | ⟨τ, g0, g1, g2⟩
    · exact ⟨τ, Or.inl (OMA.E634H.comp_vec g0 g1 g2)⟩
    · exact ⟨τ, Or.inr (OMA.E634H.comp_vec g0 g1 g2)⟩
  · right
    obtain ⟨σ, h0, h1, h2⟩ := hTA
    refine ⟨α, β, hα, hrel, ⟨σ, OMA.E634H.comp_vec h0 h1 h2⟩, ?_⟩
    rcases h with ⟨τ, g0, g1, g2⟩ | ⟨τ, g0, g1, g2⟩ | ⟨τ, g0, g1, g2⟩ | ⟨τ, g0, g1, g2⟩
    · exact ⟨τ, Or.inl (OMA.E634H.comp_vec g0 g1 g2)⟩
    · exact ⟨τ, Or.inr (Or.inl (OMA.E634H.comp_vec g0 g1 g2))⟩
    · exact ⟨τ, Or.inr (Or.inr (Or.inl (OMA.E634H.comp_vec g0 g1 g2)))⟩
    · exact ⟨τ, Or.inr (Or.inr (Or.inr (OMA.E634H.comp_vec g0 g1 g2)))⟩

