import OMAReductions.R_Borsuk_borsuk_conjecture_four_eight_parts_R1
import Mathlib.Analysis.Matrix.Order
import Mathlib

/-!
This file adapts the high-circumradius part of Logan R. Chalmers,
Lean formalisation of the four-dimensional six-part theorem (2026),
https://doi.org/10.5281/zenodo.23966881, distributed under CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/).
The contact-simplex and covariance arguments below are Chalmers's work.
Adaptations for this project are the combination of source modules, selection of
required lemmas, compatibility with Lean 4.33, and the final rescaling argument.
-/
noncomputable section
namespace BorsukSix.Support
theorem inner_eq_sum {ι : Type*} [Fintype ι]
    (n x : EuclideanSpace ℝ ι) : inner ℝ n x = ∑ i, n i * x i := by
  simp [PiLp.inner_apply, mul_comm]

theorem norm_smul_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : ℝ) (x : E) : ‖D • x‖ ^ 2 = D ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]


end BorsukSix.Support

section









namespace BorsukSix.CompactNormalization
open scoped Pointwise

abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- Closing a bounded positive-diameter set and dividing by its diameter gives
an actual compact diameter-one set, with no finiteness assumption on the input. -/
theorem compact_diameter_one_normalization {S : Set E4}
    (hS : Bornology.IsBounded S) (hD : 0 < Metric.diam S) :
    IsCompact ((Metric.diam S)⁻¹ • closure S) ∧
      Metric.diam ((Metric.diam S)⁻¹ • closure S) = 1 := by
  constructor
  · exact (Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, hS.closure⟩).image (continuous_const_smul ((Metric.diam S)⁻¹))
  · rw [diam_smul₀, Metric.diam_closure, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hD), inv_mul_cancel₀ hD.ne']

/-- The maximum distance from a proposed enclosing-ball center. Its supremum is
shown below to be attained whenever the point set is nonempty and compact. -/
noncomputable def radiusAt {E : Type*} [PseudoMetricSpace E] (K : Set E) (c : E) : ℝ :=
  sSup ((fun x => dist x c) '' K)

theorem radiusAt_attained {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (c : E) :
    ∃ x ∈ K, radiusAt K c = dist x c ∧ ∀ y ∈ K, dist y c ≤ radiusAt K c := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_id.dist continuous_const).continuousOn
  have hg : IsGreatest ((fun y => dist y c) '' K) (dist x c) := by
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy
  have hr : radiusAt K c = dist x c := hg.csSup_eq
  exact ⟨x, hx, hr, fun y hy => hr ▸ hmax hy⟩

theorem dist_le_radiusAt {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) {x : E} (hx : x ∈ K) (c : E) :
    dist x c ≤ radiusAt K c := (radiusAt_attained hK hne c).choose_spec.2.2 x hx

theorem radiusAt_nonneg {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (c : E) : 0 ≤ radiusAt K c := by
  obtain ⟨x, hx⟩ := hne
  exact dist_nonneg.trans (dist_le_radiusAt hK ⟨x, hx⟩ hx c)

theorem radiusAt_lipschitz {E : Type*} [PseudoMetricSpace E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) : LipschitzWith 1 (radiusAt K) := by
  apply LipschitzWith.of_le_add
  intro c d
  obtain ⟨x, hx, hr, _⟩ := radiusAt_attained hK hne c
  rw [hr]
  exact (dist_triangle_right x c d).trans
    (add_le_add (dist_le_radiusAt hK hne hx d) le_rfl)

/-- Every nonempty compact set in a proper metric space admits a minimum-radius
enclosing ball. The proof minimizes a proved-continuous maximum-distance function
on a compact ball; centers outside that ball cannot improve the result. -/
theorem exists_minimum_center {E : Type*} [MetricSpace E] [ProperSpace E]
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ c : E, ∀ d : E, radiusAt K c ≤ radiusAt K d := by
  obtain ⟨p, hp⟩ := hne
  have hpball : p ∈ Metric.closedBall p (radiusAt K p) := by
    simpa using radiusAt_nonneg hK ⟨p, hp⟩ p
  obtain ⟨c, hc, hmin⟩ := (isCompact_closedBall p (radiusAt K p)).exists_isMinOn
    ⟨p, hpball⟩ (radiusAt_lipschitz hK ⟨p, hp⟩).continuous.continuousOn
  refine ⟨c, fun d => ?_⟩
  by_cases hd : d ∈ Metric.closedBall p (radiusAt K p)
  · exact hmin hd
  · have hout : radiusAt K p < dist p d := by
      simpa only [Metric.mem_closedBall, not_le, dist_comm] using hd
    exact (hmin hpball).trans (hout.le.trans (dist_le_radiusAt hK ⟨p, hp⟩ hp d))

/-- Translation preserves the exact maximum-distance radius after translating
the proposed center by the same amount. -/
theorem radiusAt_translate (K : Set E4) (c d : E4) :
    radiusAt ((fun x => x - c) '' K) d = radiusAt K (d + c) := by
  unfold radiusAt
  congr 1
  rw [Set.image_image]
  congr 1
  funext x
  simp only [Function.comp_apply, dist_eq_norm]
  congr 1
  abel

theorem subtract_isometry (c : E4) : Isometry (fun x : E4 => x - c) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_eq_norm]
  congr 1
  abel

/-- A compact diameter-one set may be translated so that zero is a minimum
enclosing-ball center. This retains its diameter and all its points. -/
theorem compact_centered_diameter_one {K : Set E4}
    (hK : IsCompact K) (hdiam : Metric.diam K = 1) :
    ∃ c : E4, IsCompact ((fun x => x - c) '' K) ∧
      Metric.diam ((fun x => x - c) '' K) = 1 ∧
      ∀ d : E4, radiusAt ((fun x => x - c) '' K) 0 ≤
        radiusAt ((fun x => x - c) '' K) d := by
  have hne : K.Nonempty := by
    by_contra h
    have he : K = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [he] at hdiam
  obtain ⟨c, hc⟩ := exists_minimum_center hK hne
  refine ⟨c, hK.image (subtract_isometry c).continuous,
    (subtract_isometry c).diam_image K |>.trans hdiam, ?_⟩
  intro d
  rw [radiusAt_translate, radiusAt_translate, zero_add]
  exact hc (d + c)

/-- Complete closure/scaling/translation normalization, before the contact-simplex
and geometric selection arguments. The original set need not be closed or finite. -/
theorem exists_compact_centered_normalization {S : Set E4}
    (hS : Bornology.IsBounded S) (hD : 0 < Metric.diam S) :
    ∃ c : E4, let K := (fun x => x - c) '' ((Metric.diam S)⁻¹ • closure S)
      IsCompact K ∧ Metric.diam K = 1 ∧
        ∀ d : E4, radiusAt K 0 ≤ radiusAt K d := by
  obtain ⟨hcompact, hdiam⟩ := compact_diameter_one_normalization hS hD
  exact compact_centered_diameter_one hcompact hdiam


end BorsukSix.CompactNormalization

end

section










namespace BorsukSix.ContactSimplex
open scoped BigOperators
open CompactNormalization

/-- Convex combinations of exactly `n` (not necessarily distinct) points. -/
def combinations (n : ℕ) (K : Set E4) : Set E4 :=
  (fun wz : (Fin n → ℝ) × (Fin n → E4) => ∑ i, wz.1 i • wz.2 i) ''
    (stdSimplex ℝ (Fin n) ×ˢ {z : Fin n → E4 | ∀ i, z i ∈ K})

theorem combinations_isCompact (n : ℕ) {K : Set E4} (hK : IsCompact K) :
    IsCompact (combinations n K) := by
  apply ((isCompact_stdSimplex ℝ (Fin n)).prod
    (isCompact_pi_infinite (fun _ => hK))).image
  fun_prop

theorem combinations_subset_hull (n : ℕ) (K : Set E4) :
    combinations n K ⊆ convexHull ℝ K := by
  rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
  exact (convex_convexHull ℝ K).sum_mem (fun i _ => hw.1 i) hw.2
    (fun i _ => subset_convexHull ℝ K (hz i))

theorem affineIndependent_card_le_five {ι : Type} [Fintype ι] {z : ι → E4}
    (hz : AffineIndependent ℝ z) : Fintype.card ι ≤ 5 := by
  have h := hz.card_le_finrank_succ
  have hdim := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
  have he : Module.finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  omega

/-- Finite-dimensional Carathéodory with explicit uniform arity: at most five
points suffice in Euclidean four-space. This includes empty input sets. -/
theorem convexHull_eq_five_combinations (K : Set E4) :
    convexHull ℝ K = ⋃ n : Fin 6, combinations n.val K := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨ι, hι, z, w, hzK, hz, hwpos, hwsum, hwz⟩ :=
      eq_pos_convex_span_of_mem_convexHull hx
    letI := hι
    let n : Fin 6 := ⟨Fintype.card ι, by have := affineIndependent_card_le_five hz; omega⟩
    let e : Fin n.val ≃ ι := (Fintype.equivFin ι).symm
    apply Set.mem_iUnion.mpr
    refine ⟨n, ⟨(w ∘ e, z ∘ e), ⟨?_, ?_⟩, ?_⟩⟩
    · exact ⟨fun i => (hwpos (e i)).le, (e.sum_comp w).trans hwsum⟩
    · intro i
      exact hzK ⟨e i, rfl⟩
    · exact (e.sum_comp (fun i => w i • z i)).trans hwz
  · apply Set.iUnion_subset
    intro n
    exact combinations_subset_hull n.val K

/-- Compactness of the convex hull of an arbitrary compact subset of E4.
This is not restricted to finite contact sets. -/
theorem convexHull_isCompact {K : Set E4} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  rw [convexHull_eq_five_combinations]
  exact isCompact_iUnion (fun n => combinations_isCompact n.val hK)

/-- Active contacts of the enclosing ball centered at zero. -/
def contacts (K : Set E4) : Set E4 :=
  {x | x ∈ K ∧ ‖x‖ = radiusAt K 0}

theorem contacts_isCompact {K : Set E4} (hK : IsCompact K) :
    IsCompact (contacts K) :=
  hK.inter_right (isClosed_eq continuous_norm continuous_const)

theorem contacts_nonempty {K : Set E4} (hK : IsCompact K) (hne : K.Nonempty) :
    (contacts K).Nonempty := by
  obtain ⟨x, hx, hr, _⟩ := radiusAt_attained hK hne 0
  exact ⟨x, hx, by simpa using hr.symm⟩

/-- If one direction has a uniformly positive inner product with all active
contacts, shifting the center slightly in that direction strictly reduces radius.
Compactness controls inactive points; no finiteness of the contact set is assumed. -/
theorem exists_improved_center_of_contact_direction {K : Set E4}
    (hK : IsCompact K) (hne : K.Nonempty) (v : E4) (a : ℝ) (ha : 0 < a)
    (hcontact : ∀ x ∈ contacts K, a < inner ℝ v x) :
    ∃ c : E4, radiusAt K c < radiusAt K 0 := by
  let R := radiusAt K 0
  have hnorm (x : E4) (hx : x ∈ K) : ‖x‖ ≤ R := by
    simpa [R] using dist_le_radiusAt hK hne hx 0
  have hR : 0 < R := by
    by_contra hn
    have hrzero : R = 0 := le_antisymm (le_of_not_gt hn) (radiusAt_nonneg hK hne 0)
    obtain ⟨x, hx⟩ := contacts_nonempty hK hne
    have hxzero : x = 0 := norm_eq_zero.mp (hx.2.trans hrzero)
    have := hcontact x hx
    simp only [hxzero, inner_zero_right] at this
    linarith
  let B : Set E4 := {x | x ∈ K ∧ inner ℝ v x ≤ a / 2}
  have hB : IsCompact B := by
    change IsCompact (K ∩ {x : E4 | inner ℝ v x ≤ a / 2})
    exact hK.inter_right (isClosed_le
      (show Continuous (fun x : E4 => inner ℝ v x) by fun_prop) continuous_const)
  have hbad : ∃ r : ℝ, 0 ≤ r ∧ r < R ∧
      ∀ x ∈ K, inner ℝ v x ≤ a / 2 → ‖x‖ ≤ r := by
    rcases B.eq_empty_or_nonempty with he | hneB
    · refine ⟨0, le_rfl, hR, ?_⟩
      intro x hx hv
      have : x ∈ B := ⟨hx, hv⟩
      simpa [he] using this
    · obtain ⟨z, hz, hmax⟩ := hB.exists_isMaxOn hneB continuous_norm.continuousOn
      have hlt : ‖z‖ < R := by
        apply lt_of_le_of_ne (hnorm z hz.1)
        intro he
        have hc := hcontact z ⟨hz.1, he⟩
        linarith [hz.2]
      exact ⟨‖z‖, norm_nonneg _, hlt, fun x hx hv => hmax ⟨hx, hv⟩⟩
  obtain ⟨r, hr0, hrR, hbad⟩ := hbad
  have hdena : 0 < ‖v‖ ^ 2 + 1 := by positivity
  have hdenb : 0 < ‖v‖ + 1 := by positivity
  obtain ⟨t, ht, htmin⟩ := exists_between (lt_min
    (div_pos ha hdena) (div_pos (sub_pos.mpr hrR) hdenb))
  have hta : t * (‖v‖ ^ 2 + 1) < a := (lt_div_iff₀ hdena).mp (lt_min_iff.mp htmin).1
  have htb : t * (‖v‖ + 1) < R - r := (lt_div_iff₀ hdenb).mp (lt_min_iff.mp htmin).2
  have himprove : ∀ x ∈ K, dist x (t • v) < R := by
    intro x hx
    rw [dist_eq_norm]
    by_cases hb : inner ℝ v x ≤ a / 2
    · calc
        ‖x - t • v‖ ≤ ‖x‖ + ‖t • v‖ := norm_sub_le _ _
        _ ≤ r + t * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
          exact add_le_add (hbad x hx hb) le_rfl
        _ < R := by nlinarith
    · have hxn : ‖x‖ ^ 2 ≤ R ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hR.le).mpr (hnorm x hx)
      have hdir : t * (t * ‖v‖ ^ 2) < t * (2 * inner ℝ v x) := by
        apply mul_lt_mul_of_pos_left _ ht
        nlinarith
      have hs : ‖x - t • v‖ ^ 2 < R ^ 2 := by
        rw [norm_sub_sq_real, real_inner_smul_right, ← real_inner_comm x v,
          norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        nlinarith
      nlinarith [norm_nonneg (x - t • v)]
  obtain ⟨x, hx, he, _⟩ := radiusAt_attained hK hne (t • v)
  exact ⟨t • v, he ▸ himprove x hx⟩

/-- The minimum enclosing-ball optimality condition for an arbitrary nonempty
compact E4 set: the origin lies in the convex hull of its active contact points. -/
theorem zero_mem_convexHull_contacts {K : Set E4} (hK : IsCompact K)
    (hne : K.Nonempty) (hmin : ∀ c : E4, radiusAt K 0 ≤ radiusAt K c) :
    (0 : E4) ∈ convexHull ℝ (contacts K) := by
  by_contra hout
  obtain ⟨f, a, ha, hsep⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (contacts K))
    (convexHull_isCompact (contacts_isCompact hK)).isClosed hout
  have ha0 : 0 < a := by simpa using ha
  let v := (InnerProductSpace.toDual ℝ E4).symm f
  have hdir : ∀ x ∈ contacts K, a < inner ℝ v x := by
    intro x hx
    simpa [v] using hsep x (subset_convexHull ℝ (contacts K) hx)
  obtain ⟨c, hc⟩ := exists_improved_center_of_contact_direction hK hne v a ha0 hdir
  exact (not_lt_of_ge (hmin c)) hc

/-- A minimum enclosing ball in E4 has a positive, affinely independent contact
simplex with at most five vertices whose weighted barycenter is its center. -/
theorem exists_positive_contact_simplex {K : Set E4} (hK : IsCompact K)
    (hne : K.Nonempty) (hmin : ∀ c : E4, radiusAt K 0 ≤ radiusAt K c) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ 5 ∧ ∃ (p : Fin n → E4) (w : Fin n → ℝ),
      (∀ i, p i ∈ K ∧ ‖p i‖ = radiusAt K 0) ∧ AffineIndependent ℝ p ∧
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ (∑ i, w i • p i) = 0 := by
  obtain ⟨ι, hι, z, w, hzK, hz, hwpos, hwsum, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull (zero_mem_convexHull_contacts hK hne hmin)
  letI := hι
  have hn : 1 ≤ Fintype.card ι := by
    by_contra h
    have he : Fintype.card ι = 0 := by omega
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp he
    simp at hwsum
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, hn, affineIndependent_card_le_five hz,
    z ∘ e, w ∘ e, ?_, hz.comp_embedding e.toEmbedding, ?_, ?_, ?_⟩
  · intro i
    exact hzK ⟨e i, rfl⟩
  · intro i
    exact hwpos (e i)
  · exact (e.sum_comp w).trans hwsum
  · exact (e.sum_comp (fun i => w i • z i)).trans hwz

/-- The contact barycenter identity in Euclidean space. -/
theorem contact_weighted_distance_identity {n : ℕ} (p : Fin n → E4) (w : Fin n → ℝ)
    (R : ℝ) (hnorm : ∀ i, ‖p i‖ = R) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (c : E4) :
    (∑ i, w i * ‖p i - c‖ ^ 2) = R ^ 2 + ‖c‖ ^ 2 := by
  have hi : (∑ i, w i * inner ℝ (p i) c) = 0 := by
    simp only [← real_inner_smul_left, ← sum_inner, hbary, inner_zero_left]
  calc
    (∑ i, w i * ‖p i - c‖ ^ 2) =
      (∑ i, w i * R ^ 2) - 2 * (∑ i, w i * inner ℝ (p i) c) +
        (∑ i, w i * ‖c‖ ^ 2) := by
      simp only [norm_sub_sq_real, hnorm, mul_add, mul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 2
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, hw, hi]; ring

/-- The exact weighted pair-variance identity for a contact simplex. -/
theorem contact_pair_variance {n : ℕ} (p : Fin n → E4) (w : Fin n → ℝ)
    (R : ℝ) (hnorm : ∀ i, ‖p i‖ = R) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) :
    (∑ i, ∑ j, w i * w j * dist (p i) (p j) ^ 2) = 2 * R ^ 2 := by
  have hrow (i : Fin n) : (∑ j, w j * dist (p i) (p j) ^ 2) = 2 * R ^ 2 := by
    simp_rw [dist_comm (p i), dist_eq_norm]
    rw [contact_weighted_distance_identity p w R hnorm hw hbary, hnorm i]
    ring
  calc
    (∑ i, ∑ j, w i * w j * dist (p i) (p j) ^ 2) =
        ∑ i, w i * (∑ j, w j * dist (p i) (p j) ^ 2) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ i, w i * (2 * R ^ 2) := by simp_rw [hrow]
    _ = 2 * R ^ 2 := by rw [← Finset.sum_mul, hw, one_mul]

/-- Diameter one, diagonal zero, and positive contact weights give the sharp
finite-contact upper estimate before Cauchy--Schwarz is applied. -/
theorem contact_radius_sq_le_weight_bound {n : ℕ}
    (p : Fin n → E4) (w : Fin n → ℝ) (R : ℝ)
    (hnorm : ∀ i, ‖p i‖ = R) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (hd : ∀ i j, dist (p i) (p j) ≤ 1) :
    2 * R ^ 2 ≤ 1 - ∑ i, w i ^ 2 := by
  have hrow (i : Fin n) : (∑ j, w j * dist (p i) (p j) ^ 2) ≤ 1 - w i := by
    calc
      (∑ j, w j * dist (p i) (p j) ^ 2) ≤
          ∑ j, (w j - if j = i then w i else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hji : j = i
        · simp [hji]
        · simp only [hji, ↓reduceIte, sub_zero]
          have hs : dist (p i) (p j) ^ 2 ≤ 1 := by
            nlinarith [hd i j, dist_nonneg (x := p i) (y := p j)]
          simpa using mul_le_mul_of_nonneg_left hs (hw0 j)
      _ = 1 - w i := by simp [Finset.sum_sub_distrib, hw]
  rw [← contact_pair_variance p w R hnorm hw hbary]
  calc
    (∑ i, ∑ j, w i * w j * dist (p i) (p j) ^ 2) =
        ∑ i, w i * (∑ j, w j * dist (p i) (p j) ^ 2) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i, w i * (1 - w i) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hrow i) (hw0 i))
    _ = 1 - ∑ i, w i ^ 2 := by simp [mul_sub, Finset.sum_sub_distrib, hw, pow_two]

/-- Jung's finite-contact bound: `R² ≤ (n−1)/(2n)`, with real subtraction.
The ambient dimension only enters later through the at-most-five contact bound. -/
theorem contact_jung_bound {n : ℕ} (hn : 0 < n)
    (p : Fin n → E4) (w : Fin n → ℝ) (R : ℝ)
    (hnorm : ∀ i, ‖p i‖ = R) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (hd : ∀ i j, dist (p i) (p j) ≤ 1) :
    R ^ 2 ≤ ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
  have hweight := contact_radius_sq_le_weight_bound p w R hnorm hw0 hw hbary hd
  have hcs : 1 ≤ (n : ℝ) * ∑ i, w i ^ 2 := by
    simpa [hw] using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := w))
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ (mul_pos (by norm_num) hnreal)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hweight hnreal.le]

theorem contact_radius_sq_le_two_fifths {n : ℕ} (hn : 0 < n) (hn5 : n ≤ 5)
    (p : Fin n → E4) (w : Fin n → ℝ) (R : ℝ)
    (hnorm : ∀ i, ‖p i‖ = R) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (hd : ∀ i j, dist (p i) (p j) ≤ 1) :
    R ^ 2 ≤ 2 / 5 := by
  apply (contact_jung_bound hn p w R hnorm hw0 hw hbary hd).trans
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hn5real : (n : ℝ) ≤ 5 := by exact_mod_cast hn5
  apply (div_le_iff₀ (mul_pos (by norm_num) hnreal)).mpr
  nlinarith

theorem contact_radius_sq_le_quarter_of_at_most_two {n : ℕ}
    (hn : 0 < n) (hn2 : n ≤ 2)
    (p : Fin n → E4) (w : Fin n → ℝ) (R : ℝ)
    (hnorm : ∀ i, ‖p i‖ = R) (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hbary : ∑ i, w i • p i = 0) (hd : ∀ i j, dist (p i) (p j) ≤ 1) :
    R ^ 2 ≤ 1 / 4 := by
  apply (contact_jung_bound hn p w R hnorm hw0 hw hbary hd).trans
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hn2real : (n : ℝ) ≤ 2 := by exact_mod_cast hn2
  apply (div_le_iff₀ (mul_pos (by norm_num) hnreal)).mpr
  nlinarith

/-- Jung's `R² ≤ 2/5` bound for arbitrary compact diameter-at-most-one subsets
of real Euclidean four-space, derived from minimum-ball contacts. -/
theorem minimum_center_jung_bound {K : Set E4} (hK : IsCompact K)
    (hne : K.Nonempty) (hdiam : Metric.diam K ≤ 1)
    (hmin : ∀ c : E4, radiusAt K 0 ≤ radiusAt K c) :
    radiusAt K 0 ^ 2 ≤ 2 / 5 := by
  obtain ⟨n, hn, hn5, p, w, hp, _, hwpos, hw, hbary⟩ :=
    exists_positive_contact_simplex hK hne hmin
  apply contact_radius_sq_le_two_fifths hn hn5 p w _
    (fun i => (hp i).2) (fun i => (hwpos i).le) hw hbary
  intro i j
  exact (Metric.dist_le_diam_of_mem hK.isBounded (hp i).1 (hp j).1).trans hdiam

/-- In the middle/high radius regime, one or two contact points are impossible;
the positive affinely independent selector simplex has three, four, or five points. -/
theorem exists_three_to_five_contact_simplex {K : Set E4} (hK : IsCompact K)
    (hne : K.Nonempty) (hdiam : Metric.diam K ≤ 1)
    (hmin : ∀ c : E4, radiusAt K 0 ≤ radiusAt K c)
    (hR : 1 / 4 < radiusAt K 0 ^ 2) :
    ∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ ∃ (p : Fin n → E4) (w : Fin n → ℝ),
      (∀ i, p i ∈ K ∧ ‖p i‖ = radiusAt K 0) ∧ AffineIndependent ℝ p ∧
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ (∑ i, w i • p i) = 0 := by
  obtain ⟨n, hn, hn5, p, w, hp, haff, hwpos, hw, hbary⟩ :=
    exists_positive_contact_simplex hK hne hmin
  have hn3 : 3 ≤ n := by
    by_contra hn3
    have hn2 : n ≤ 2 := by omega
    have hq := contact_radius_sq_le_quarter_of_at_most_two hn hn2 p w _
      (fun i => (hp i).2) (fun i => (hwpos i).le) hw hbary (fun i j =>
        (Metric.dist_le_diam_of_mem hK.isBounded (hp i).1 (hp j).1).trans hdiam)
    exact (not_lt_of_ge hq) hR
  exact ⟨n, hn3, hn5, p, w, hp, haff, hwpos, hw, hbary⟩









end BorsukSix.ContactSimplex

end

section




/- Exact scalar contradiction for the high-radius residual argument. Geometry
must supply both covariance bounds; this file alone is not the high-tail theorem. -/

namespace BorsukSix.HighRadiusTailScalar

def alpha : ℝ := 2 / 5
def rho : ℝ := 9999 / 20000
def sigma : ℝ := rho ^ 2
def U (r : ℝ) : ℝ := 1 / 2 - r
def kappa (r : ℝ) : ℝ := (2 - 5 * r) / 2
def eta (r : ℝ) : ℝ := (3 * r - 1) / 2
def A (r : ℝ) : ℝ := alpha ^ 2 * r - sigma
def V (Q D r : ℝ) : ℝ :=
  ((1 - r) * (Q + 2 * A r) - (Q ^ 2 + D ^ 2) / 2 - A r * Q) / (4 * alpha)
def G0 (Q r : ℝ) : ℝ := U r * Q - kappa r - V Q 0 r
def B (r : ℝ) : ℝ := -22 * r / 25 - 179980001 / 200000000
def C (r : ℝ) : ℝ := 16 * r ^ 2 / 25 + 636019999 * r / 100000000 - 220019999 / 100000000
def delta (r : ℝ) : ℝ := 279 * r ^ 2 / 625 + 29821219939 * r / 5000000000 -
  384424799159960001 / 160000000000000000

lemma G0_identity (Q r : ℝ) : 8 * alpha * G0 Q r = Q ^ 2 + B r * Q + C r := by
  unfold G0 U kappa V A sigma rho B C alpha
  ring
lemma delta_identity (r : ℝ) : delta r = C r - (B r) ^ 2 / 4 := by
  unfold delta B C
  ring
lemma delta_endpoint : delta (1957 / 5000) = 21741731067199 / 160000000000000000 := by
  norm_num [delta]
lemma delta_pos {r : ℝ} (hr : 1957 / 5000 ≤ r) : 0 < delta r := by
  have hr0 : 0 ≤ r := by linarith
  have hrsq : (1957 / 5000 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith
  have hd : delta (1957 / 5000) ≤ delta r := by unfold delta; nlinarith
  rw [delta_endpoint] at hd
  linarith
lemma G0_pos (Q : ℝ) {r : ℝ} (hr : 1957 / 5000 ≤ r) : 0 < G0 Q r := by
  have hd := delta_pos hr
  rw [delta_identity] at hd
  have hg := G0_identity Q r
  unfold alpha at hg
  nlinarith [sq_nonneg (Q + B r / 2)]

lemma sqrt_tangent (a D : ℝ) (ha : 0 < a) :
    Real.sqrt (a ^ 2 + D ^ 2) ≤ a + D ^ 2 / (2 * a) := by
  have ht : 0 ≤ D ^ 2 / (2 * a) := by positivity
  have hid : 2 * a * (D ^ 2 / (2 * a)) = D ^ 2 := by field_simp
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith [sq_nonneg (D ^ 2 / (2 * a))]

/-- A real number cannot obey both geometric covariance estimates on the actual
high-tail radius interval. The imbalance D may be arbitrary. -/
theorem covariance_bounds_incompatible (r Q D P : ℝ)
    (hrlo : 1957 / 5000 ≤ r) (hrhi : r ≤ 2 / 5) (hQ : Q ≤ 2 * r)
    (hupper : P ≤ V Q D r)
    (hlower : eta r * Q - kappa r * Real.sqrt (D ^ 2 + (1 - Q) ^ 2) ≤ P) : False := by
  have ha : 0 < 1 - Q := by linarith
  have hk : 0 ≤ kappa r := by unfold kappa; linarith
  have hcoef : 4 * alpha * kappa r ≤ 1 - Q := by
    unfold alpha kappa
    nlinarith
  have hroot := sqrt_tangent (1 - Q) D ha
  rw [add_comm ((1-Q)^2)] at hroot
  have hmul := mul_le_mul_of_nonneg_left hroot hk
  have hsmall : eta r * Q - kappa r * ((1 - Q) + D ^ 2 / (2 * (1 - Q))) ≤ P := by linarith
  have hpos := G0_pos Q hrlo
  have hden : 0 < 2 * (1 - Q) := by linarith
  have hid :
      2 * (1 - Q) *
        (eta r * Q - kappa r * ((1 - Q) + D ^ 2 / (2 * (1 - Q))) - V Q D r) =
      2 * (1 - Q) * G0 Q r +
        D ^ 2 * ((1 - Q) / (4 * alpha) - kappa r) := by
    unfold eta G0 U V
    field_simp
    unfold alpha kappa
    ring
  have hcoef' : 0 ≤ (1 - Q) / (4 * alpha) - kappa r := by
    unfold alpha at *
    norm_num at hcoef ⊢
    linarith
  have hrest := mul_nonneg (sq_nonneg D) hcoef'
  have hstrict := mul_pos hden hpos
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hden.le (show
      eta r * Q - kappa r * ((1 - Q) + D ^ 2 / (2 * (1 - Q))) - V Q D r ≤ 0 by linarith)
  linarith


end BorsukSix.HighRadiusTailScalar

end

section





/- Joint two-point covariance estimate. The spectral bound is derived from a
real Gram identity and positive-semidefinite trace duality; no eigenvalue
ordering assumption is supplied by a certificate. -/

namespace BorsukSix.HighRadiusTailSpectral
open scoped BigOperators MatrixOrder
open Matrix
abbrev E4 := EuclideanSpace ℝ (Fin 4)

def gramTop (q t s : ℝ) : ℝ := (q + t + Real.sqrt ((q - t) ^ 2 + 4 * s ^ 2)) / 2

lemma gram_quadratic_bound (q t s a b : ℝ) :
    q * a ^ 2 + 2 * s * a * b + t * b ^ 2 ≤ gramTop q t s * (a ^ 2 + b ^ 2) := by
  let R := Real.sqrt ((q - t) ^ 2 + 4 * s ^ 2)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = (q - t) ^ 2 + 4 * s ^ 2 := Real.sq_sqrt (by positivity)
  have hid : (R * (a ^ 2 + b ^ 2)) ^ 2 -
      ((q - t) * (a ^ 2 - b ^ 2) + 4 * s * a * b) ^ 2 =
      (2 * s * (a ^ 2 - b ^ 2) - 2 * (q - t) * a * b) ^ 2 := by
    rw [mul_pow, hR2]
    ring
  have hleft : (q - t) * (a ^ 2 - b ^ 2) + 4 * s * a * b ≤ R * (a ^ 2 + b ^ 2) := by
    have hnn : 0 ≤ R * (a ^ 2 + b ^ 2) := by positivity
    nlinarith only [hid, hnn, sq_nonneg (2 * s * (a ^ 2 - b ^ 2) - 2 * (q - t) * a * b)]
  change q * a ^ 2 + 2 * s * a * b + t * b ^ 2 ≤ ((q+t+R)/2)*(a^2+b^2)
  nlinarith only [hleft]

lemma gram_pair_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y z : E) :
    (inner ℝ x z) ^ 2 + (inner ℝ y z) ^ 2 ≤
      gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) * ‖z‖ ^ 2 := by
  let a := inner ℝ x z
  let b := inner ℝ y z
  let w := a • x + b • y
  have hi : inner ℝ w z = a ^ 2 + b ^ 2 := by
    simp [w, a, b, inner_add_left, inner_smul_left, pow_two]
  have hn : ‖w‖ ^ 2 = ‖x‖ ^ 2 * a ^ 2 + 2 * inner ℝ x y * a * b + ‖y‖ ^ 2 * b ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (a • x + b • y) (a • x + b • y) = _
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      conj_trivial, real_inner_self_eq_norm_sq, real_inner_comm y x]
    ring
  have hcs := real_inner_mul_inner_self_le w z
  rw [hi, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hn] at hcs
  have hg := gram_quadratic_bound (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) a b
  have hmul := mul_le_mul_of_nonneg_right hg (sq_nonneg ‖z‖)
  have htop : 0 ≤ gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) := by unfold gramTop; positivity
  have hprod : 0 ≤ gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) * ‖z‖ ^ 2 := by positivity
  change a^2+b^2 ≤ _
  nlinarith only [hcs, hmul, hprod, sq_nonneg a, sq_nonneg b]

lemma trace_mul_nonneg {N T : Matrix (Fin 4) (Fin 4) ℝ}
    (hN : N.PosSemidef) (hT : T.PosSemidef) : 0 ≤ (N * T).trace := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN.nonneg
  have h := (hT.mul_mul_conjTranspose_same B).trace_nonneg
  rw [trace_mul_cycle] at h
  simpa only [star_eq_conjTranspose] using h

/-- Coordinate covariance quadratic form, using the Euclidean L2 coordinates. -/
def quad (N : Matrix (Fin 4) (Fin 4) ℝ) (x : E4) : ℝ := x.ofLp ⬝ᵥ (N *ᵥ x.ofLp)
def pairMatrix (x y : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  vecMulVec x.ofLp x.ofLp + vecMulVec y.ofLp y.ofLp

lemma quad_pairMatrix (x y z : E4) : quad (pairMatrix x y) z =
    (inner ℝ x z) ^ 2 + (inner ℝ y z) ^ 2 := by
  simp [quad, pairMatrix, Matrix.mulVec, dotProduct, vecMulVec, Fin.sum_univ_succ, Support.inner_eq_sum]
  ring

lemma quad_identity (x : E4) : quad (1 : Matrix (Fin 4) (Fin 4) ℝ) x = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [quad, dotProduct, pow_two]

lemma pairMatrix_upper (x y : E4) :
    (gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) • (1 : Matrix (Fin 4) (Fin 4) ℝ) -
      pairMatrix x y).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · apply IsHermitian.sub
    · exact IsHermitian.smul isHermitian_one (IsSelfAdjoint.all _)
    · apply IsHermitian.add <;> apply isHermitian_iff_isSymm.mpr <;> ext i j <;>
        simp [vecMulVec, transpose_apply, mul_comm]
  · intro z
    have h := gram_pair_bound x y (WithLp.toLp 2 z)
    rw [← quad_pairMatrix, ← quad_identity (WithLp.toLp 2 z)] at h
    simpa [quad, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] using sub_nonneg.mpr h

lemma trace_mul_pairMatrix (N : Matrix (Fin 4) (Fin 4) ℝ) (x y : E4) :
    (N * pairMatrix x y).trace = quad N x + quad N y := by
  simp [pairMatrix, Matrix.mul_add, trace_add, mul_vecMulVec, trace_vecMulVec, quad, dotProduct_comm]

/-- Positive trace duality bounds the covariance defect on a pair jointly. -/
theorem joint_quad_bound (N : Matrix (Fin 4) (Fin 4) ℝ) (hN : N.PosSemidef) (x y : E4) :
    quad N x + quad N y ≤ N.trace * gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) := by
  have h := trace_mul_nonneg hN (pairMatrix_upper x y)
  rw [Matrix.mul_sub, trace_sub, Matrix.mul_smul, Matrix.mul_one, trace_smul,
    trace_mul_pairMatrix] at h
  simpa only [smul_eq_mul, mul_comm, sub_nonneg] using h


end BorsukSix.HighRadiusTailSpectral

end

section




/- Covariance inequalities derived from physical contact data. -/

namespace BorsukSix.HighRadiusTailCovariance
open scoped BigOperators MatrixOrder
open BorsukSix.HighRadiusTailSpectral BorsukSix.HighRadiusTailScalar
open Matrix

lemma sum_mul_separated {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    (∑ i, ∑ j, f i * g j) = (∑ i, f i) * ∑ j, g j := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

lemma scalar_covariance_identity {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (t : ι → ι → ℝ) (C : ℝ)
    (hw : ∑ i, w i = 1) (ha : ∑ i, w i * a i = 0)
    (ht : ∀ i j, t i j = t j i) (hrow : ∀ i, ∑ j, w j * t i j = 0) :
    (∑ i, ∑ j, w i * w j * (C + 2 * t i j) * (a i - a j) ^ 2) =
      2 * C * (∑ i, w i * a i ^ 2) -
      4 * ∑ i, ∑ j, (w i * a i) * (w j * a j) * t i j := by
  have hrow' : (∑ i, ∑ j, (w i * a i ^ 2) * (w j * t i j)) = 0 := by
    simp_rw [← Finset.mul_sum, hrow, mul_zero, Finset.sum_const_zero]
  have hcol' : (∑ i, ∑ j, (w j * a j ^ 2) * (w i * t i j)) = 0 := by
    rw [Finset.sum_comm]
    simpa only [ht] using hrow'
  calc
    _ = ∑ i, ∑ j,
      (C * ((w i * a i ^ 2) * w j) + C * (w i * (w j * a j ^ 2)) -
        (2 * C) * ((w i * a i) * (w j * a j)) +
        2 * ((w i * a i ^ 2) * (w j * t i j)) +
        2 * ((w j * a j ^ 2) * (w i * t i j)) -
        4 * ((w i * a i) * (w j * a j) * t i j)) := by
      apply Finset.sum_congr rfl; intro i hi
      apply Finset.sum_congr rfl; intro j hj
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hcol']
      simp only [hw, ha, hrow, mul_one, mul_zero, Finset.sum_const_zero, ← Finset.sum_mul]
      ring

def Phi (w : Fin 5 → ℝ) (p : Fin 5 → E4) (v : E4) : ℝ :=
  ∑ i, w i * (inner ℝ v (p i)) ^ 2

def covVec (w : Fin 5 → ℝ) (p : Fin 5 → E4) (v : E4) : E4 :=
  ∑ i, (w i * inner ℝ v (p i)) • p i

def covariance (w : Fin 5 → ℝ) (p : Fin 5 → E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  ∑ i, w i • vecMulVec (p i).ofLp (p i).ofLp

lemma weighted_inner_zero (w : Fin 5 → ℝ) (p : Fin 5 → E4)
    (hp : ∑ i, w i • p i = 0) (v : E4) : ∑ i, w i * inner ℝ v (p i) = 0 := by
  have h := congrArg (inner ℝ v) hp
  simpa only [inner_sum, inner_smul_right, inner_zero_right] using h

lemma inner_covVec (w : Fin 5 → ℝ) (p : Fin 5 → E4) (v : E4) :
    inner ℝ v (covVec w p v) = Phi w p v := by
  simp only [covVec, Phi, inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma covVec_norm_sq (w : Fin 5 → ℝ) (p : Fin 5 → E4) (v : E4) :
    ‖covVec w p v‖ ^ 2 =
      ∑ i, ∑ j, (w i * inner ℝ v (p i)) * (w j * inner ℝ v (p j)) * inner ℝ (p i) (p j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [covVec, sum_inner, inner_sum, inner_smul_left, inner_smul_right, conj_trivial]
  apply Finset.sum_congr rfl; intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j hj
  rw [real_inner_comm (p j) (p i)]
  ring

lemma contact_covariance_identity (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (v : E4) :
    (∑ i, ∑ j, w i * w j * (1 - dist (p i) (p j) ^ 2) *
      (inner ℝ v (p i) - inner ℝ v (p j)) ^ 2) =
      4 * U r * Phi w p v - 4 * ‖covVec w p v‖ ^ 2 := by
  have hdist (i j : Fin 5) : 1 - dist (p i) (p j) ^ 2 = 1 - 2*r + 2*inner ℝ (p i) (p j) := by
    rw [dist_eq_norm, norm_sub_sq_real, hr i, hr j]
    ring
  simp_rw [hdist]
  rw [scalar_covariance_identity w (fun i => inner ℝ v (p i))
    (fun i j => inner ℝ (p i) (p j)) (1-2*r) hw (weighted_inner_zero w p hp v)
    (fun i j => real_inner_comm _ _) (fun i => weighted_inner_zero w p hp (p i))]
  rw [← covVec_norm_sq]
  unfold Phi U
  ring

/-- The upper covariance inequality follows solely from diameter-one contacts,
common radius, normalized nonnegative weights, and their zero barycenter. -/
theorem Phi_le_U_norm_sq (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (hrhi : r ≤ 1 / 2)
    (hdiam : ∀ i j, dist (p i) (p j) ≤ 1) (v : E4) :
    Phi w p v ≤ U r * ‖v‖ ^ 2 := by
  have hsum : 0 ≤ ∑ i, ∑ j, w i * w j * (1 - dist (p i) (p j) ^ 2) *
      (inner ℝ v (p i) - inner ℝ v (p j)) ^ 2 := by
    apply Finset.sum_nonneg; intro i hi
    apply Finset.sum_nonneg; intro j hj
    have hd : 0 ≤ 1 - dist (p i) (p j) ^ 2 := by nlinarith [hdiam i j, dist_nonneg (x:=p i) (y:=p j)]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hw0 i) (hw0 j)) hd) (sq_nonneg _)
  rw [contact_covariance_identity w p r hw hp hr v] at hsum
  have hPhi0 : 0 ≤ Phi w p v := Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (sq_nonneg _)
  have hcs := real_inner_mul_inner_self_le v (covVec w p v)
  rw [inner_covVec, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  have hmul := mul_le_mul_of_nonneg_left (show ‖covVec w p v‖ ^ 2 ≤ U r * Phi w p v by linarith) (sq_nonneg ‖v‖)
  by_cases hzero : Phi w p v = 0
  · rw [hzero]
    exact mul_nonneg (by unfold U; linarith) (sq_nonneg _)
  · have hpos : 0 < Phi w p v := lt_of_le_of_ne hPhi0 (Ne.symm hzero)
    apply (mul_le_mul_iff_left₀ hpos).mp
    calc
      _ ≤ ‖v‖ ^ 2 * (U r * Phi w p v) := hcs.trans hmul
      _ = _ := by ring

lemma quad_add (M N : Matrix (Fin 4) (Fin 4) ℝ) (x : E4) :
    quad (M+N) x = quad M x + quad N x := by simp [quad, add_mulVec, dotProduct_add]
lemma quad_sub (M N : Matrix (Fin 4) (Fin 4) ℝ) (x : E4) :
    quad (M-N) x = quad M x - quad N x := by simp [quad, sub_mulVec, dotProduct_sub]
lemma quad_smul (a : ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (x : E4) :
    quad (a • M) x = a * quad M x := by simp [quad, smul_mulVec, dotProduct_smul]
lemma quad_rank_one (p x : E4) :
    quad (vecMulVec p.ofLp p.ofLp) x = (inner ℝ x p) ^ 2 := by
  simp [quad, Matrix.mulVec, dotProduct, vecMulVec, Fin.sum_univ_succ, Support.inner_eq_sum]
  ring

lemma quad_covariance (w : Fin 5 → ℝ) (p : Fin 5 → E4) (x : E4) :
    quad (covariance w p) x = Phi w p x := by
  simp [covariance, Phi, Fin.sum_univ_succ, quad_add, quad_smul, quad_rank_one]

lemma covariance_isHermitian (w : Fin 5 → ℝ) (p : Fin 5 → E4) :
    (covariance w p).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  ext k l
  simp only [covariance, transpose_apply, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma trace_covariance (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw : ∑ i, w i = 1) (hr : ∀ i, ‖p i‖ ^ 2 = r) : (covariance w p).trace = r := by
  have hnorm (i : Fin 5) : (p i).ofLp ⬝ᵥ (p i).ofLp = r := by
    rw [← hr i, EuclideanSpace.real_norm_sq_eq]
    simp only [dotProduct, pow_two]
  simp only [covariance, trace_sum, trace_smul, trace_vecMulVec, hnorm, smul_eq_mul,
    ← Finset.sum_mul, hw, one_mul]

def defect (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  U r • 1 - covariance w p

lemma quad_defect (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ) (x : E4) :
    quad (defect w p r) x = U r * ‖x‖ ^ 2 - Phi w p x := by
  rw [defect, quad_sub, quad_smul, quad_identity, quad_covariance]

lemma defect_posSemidef (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (hrhi : r ≤ 1 / 2)
    (hdiam : ∀ i j, dist (p i) (p j) ≤ 1) : (defect w p r).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (isHermitian_one.smul (IsSelfAdjoint.all _)).sub (covariance_isHermitian w p)
  · intro v
    have h := Phi_le_U_norm_sq w p r hw0 hw hp hr hrhi hdiam (WithLp.toLp 2 v)
    have hnonneg := sub_nonneg.mpr h
    rw [← quad_defect] at hnonneg
    simpa [quad] using hnonneg

lemma trace_defect (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw : ∑ i, w i = 1) (hr : ∀ i, ‖p i‖ ^ 2 = r) : (defect w p r).trace = 2-5*r := by
  rw [defect, trace_sub, trace_smul, trace_one, trace_covariance w p r hw hr]
  norm_num [U]
  ring

/-- Lower covariance estimate for an actual unit-distance pair, proved jointly
rather than by a separate minimum-eigenvalue estimate for each point. -/
theorem pair_lower_covariance (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (hrhi : r ≤ 1 / 2)
    (hdiam : ∀ i j, dist (p i) (p j) ≤ 1) (x y : E4) (hxy : dist x y = 1) :
    eta r * (‖x‖ ^ 2 + ‖y‖ ^ 2) - kappa r *
      Real.sqrt ((‖x‖ ^ 2 - ‖y‖ ^ 2) ^ 2 + (1 - (‖x‖ ^ 2 + ‖y‖ ^ 2)) ^ 2) ≤
      Phi w p x + Phi w p y := by
  have h := joint_quad_bound (defect w p r)
    (defect_posSemidef w p r hw0 hw hp hr hrhi hdiam) x y
  rw [quad_defect, quad_defect, trace_defect w p r hw hr] at h
  have hi : inner ℝ x y = (‖x‖ ^ 2 + ‖y‖ ^ 2 - 1) / 2 := by
    have hdist : ‖x-y‖ ^ 2 = 1 := by rw [← dist_eq_norm, hxy]; norm_num
    rw [norm_sub_sq_real] at hdist
    linarith
  have hg : gramTop (‖x‖ ^ 2) (‖y‖ ^ 2) (inner ℝ x y) =
      ((‖x‖ ^ 2 + ‖y‖ ^ 2) + Real.sqrt ((‖x‖ ^ 2 - ‖y‖ ^ 2) ^ 2 +
        (1 - (‖x‖ ^ 2 + ‖y‖ ^ 2)) ^ 2)) / 2 := by
    rw [gramTop, hi]
    congr 3
    ring
  rw [hg] at h
  unfold eta kappa U at *
  nlinarith only [h]



end BorsukSix.HighRadiusTailCovariance

end

section




namespace BorsukSix.HighRadiusTailMissed
open scoped BigOperators
open BorsukSix.HighRadiusTailSpectral BorsukSix.HighRadiusTailScalar
open BorsukSix.HighRadiusTailCovariance

lemma weighted_variance_le (w a : Fin 5 → ℝ) (l u : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (ha : ∑ i, w i * a i = 0)
    (hl : ∀ i, l ≤ a i) (hu : ∀ i, a i ≤ u) :
    (∑ i, w i * a i ^ 2) ≤ -l*u := by
  have hnonneg : 0 ≤ ∑ i, w i * (a i-l) * (u-a i) := by
    apply Finset.sum_nonneg; intro i hi
    exact mul_nonneg (mul_nonneg (hw0 i) (sub_nonneg.mpr (hl i))) (sub_nonneg.mpr (hu i))
  have hid : (∑ i, w i * (a i-l) * (u-a i)) =
      (u+l)*(∑ i, w i*a i) - (∑ i, w i*a i^2) - (l*u)*(∑ i, w i) := by
    calc
      _ = ∑ i, ((u+l)*(w i*a i) - w i*a i^2 - (l*u)*w i) := by
        apply Finset.sum_congr rfl; intro i hi; ring
      _ = _ := by simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hid,hw,ha] at hnonneg
  linarith

/-- Outside every one of the five open contact balls, with the accepted fixed
radius rho=9999/20000 and scale alpha=2/5. -/
def Missed (p : Fin 5 → E4) (x : E4) : Prop := ∀ i, rho ≤ dist x (alpha • p i)

lemma contact_inner_lower (p x : E4) (r : ℝ) (hr : ‖p‖ ^ 2 = r) (hxp : dist x p ≤ 1) :
    -(1-r-‖x‖^2)/2 ≤ inner ℝ x p := by
  have hd : dist x p ^ 2 ≤ 1 := by nlinarith [dist_nonneg (x:=x) (y:=p)]
  rw [dist_eq_norm, norm_sub_sq_real, hr] at hd
  linarith

lemma missed_inner_upper (p x : E4) (r : ℝ) (hr : ‖p‖ ^ 2 = r)
    (hmiss : rho ≤ dist x (alpha • p)) : inner ℝ x p ≤ (‖x‖^2 + A r)/(2*alpha) := by
  have hrho : 0 ≤ rho := by norm_num [rho]
  have hd : sigma ≤ dist x (alpha • p) ^ 2 := by unfold sigma; nlinarith
  rw [dist_eq_norm, norm_sub_sq_real, Support.norm_smul_sq, hr, inner_smul_right] at hd
  unfold A alpha sigma rho at *
  norm_num at hd ⊢
  linarith

/-- Missed-ball covariance upper estimate, derived from actual contact distances. -/
theorem missed_covariance_upper (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (x : E4)
    (hxp : ∀ i, dist x (p i) ≤ 1) (hmiss : Missed p x) :
    Phi w p x ≤ (1-r-‖x‖^2)*(‖x‖^2+A r)/(4*alpha) := by
  have h := weighted_variance_le w (fun i => inner ℝ x (p i))
    (-(1-r-‖x‖^2)/2) ((‖x‖^2+A r)/(2*alpha)) hw0 hw (weighted_inner_zero w p hp x)
    (fun i => contact_inner_lower (p i) x r (hr i) (hxp i))
    (fun i => missed_inner_upper (p i) x r (hr i) (hmiss i))
  change Phi w p x ≤ _ at h
  convert h using 1
  ring

lemma pair_upper_covariance (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (x y : E4)
    (hxp : ∀ i, dist x (p i) ≤ 1) (hyp : ∀ i, dist y (p i) ≤ 1)
    (hxmiss : Missed p x) (hymiss : Missed p y) :
    Phi w p x + Phi w p y ≤ V (‖x‖^2+‖y‖^2) (‖x‖^2-‖y‖^2) r := by
  have hx := missed_covariance_upper w p r hw0 hw hp hr x hxp hxmiss
  have hy := missed_covariance_upper w p r hw0 hw hp hr y hyp hymiss
  exact (add_le_add hx hy).trans_eq (by unfold V; ring)

/-- There is no unit-distance pair of actual missed points in the high-radius
range. This uses contact constraints, not merely outer-ball membership. -/
theorem missed_pair_ne_one (w : Fin 5 → ℝ) (p : Fin 5 → E4) (r : ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1) (hp : ∑ i, w i • p i = 0)
    (hr : ∀ i, ‖p i‖ ^ 2 = r) (hrlo : 1957/5000 ≤ r) (hrhi : r ≤ 2/5)
    (hdiam : ∀ i j, dist (p i) (p j) ≤ 1) (x y : E4)
    (hx : ‖x‖^2 ≤ r) (hy : ‖y‖^2 ≤ r)
    (hxp : ∀ i, dist x (p i) ≤ 1) (hyp : ∀ i, dist y (p i) ≤ 1)
    (hxmiss : Missed p x) (hymiss : Missed p y) : dist x y ≠ 1 := by
  intro hxy
  exact covariance_bounds_incompatible r (‖x‖^2+‖y‖^2) (‖x‖^2-‖y‖^2)
    (Phi w p x + Phi w p y) hrlo hrhi (by linarith)
    (pair_upper_covariance w p r hw0 hw hp hr x y hxp hyp hxmiss hymiss)
    (pair_lower_covariance w p r hw0 hw hp hr (by linarith) hdiam x y hxy)


end BorsukSix.HighRadiusTailMissed

end

open Metric Bornology BorsukSix.CompactNormalization BorsukSix.ContactSimplex
open BorsukSix.HighRadiusTailMissed BorsukSix.HighRadiusTailScalar
open scoped Pointwise

private theorem change_center (D : ℝ) (hD : 0 < D)
    (c x z : EuclideanSpace ℝ (Fin 4)) :
    dist x (D • (c+z)) = D * dist (D⁻¹ • x - c) z := by
  calc
    _ = dist (D • (D⁻¹ • x)) (D • (c+z)) := by rw [smul_smul, mul_inv_cancel₀ hD.ne', one_smul]
    _ = _ := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hD,dist_eq_norm,dist_eq_norm]
      congr 2
      abel

private theorem hit_five {K : Set (EuclideanSpace ℝ (Fin 4))} (hK : IsCompact K)
    (hnt : K.Nontrivial)
    (high : ∀ c, ∃ x ∈ K, (627/1000 : ℝ)*diam K < dist x c) :
    ∃ (c : Fin 5 → EuclideanSpace ℝ (Fin 4)) (r : ℝ), 0 < r ∧ 2*r < diam K ∧
      ∀ x ∈ K, ∀ y ∈ K, dist x y = diam K →
        ∃ i, x ∈ ball (c i) r ∨ y ∈ ball (c i) r := by
  classical
  let D := diam K
  have hD : 0 < D := diam_pos hnt hK.isBounded
  obtain ⟨c, hc⟩ := exists_compact_centered_normalization hK.isBounded hD
  let f (x : EuclideanSpace ℝ (Fin 4)) := D⁻¹ • x - c
  let S := f '' K
  have hset : (fun x => x-c) '' ((diam K)⁻¹ • closure K) = S := by
    rw [hK.isClosed.closure_eq, ← Set.image_smul, Set.image_image]
  dsimp only at hc
  rw [hset] at hc
  obtain ⟨hs, hd, hmin⟩ := hc
  have hne : S.Nonempty := hnt.nonempty.image f
  have within (x) (hx : x ∈ S) (y) (hy : y ∈ S) : dist x y ≤ 1 :=
    (dist_le_diam_of_mem hs.isBounded hx hy).trans_eq hd
  let R := radiusAt S 0
  have hR : (627 / 1000 : ℝ) < R := by
    obtain ⟨x, hx, hfar⟩ := high (D • (c+0))
    rw [change_center D hD] at hfar
    have hsmall := dist_le_radiusAt hs hne (show f x ∈ S from ⟨x,hx,rfl⟩) 0
    change 627 / 1000 * D < D * dist (f x) 0 at hfar
    exact (lt_of_mul_lt_mul_left (by simpa [mul_comm] using hfar) hD.le).trans_le hsmall
  have hRhi : R^2 ≤ 2/5 := minimum_center_jung_bound hs hne hd.le hmin
  have hRlo : 1957/5000 ≤ R^2 := by nlinarith [sq_nonneg (R-627/1000)]
  obtain ⟨n, hn, hn5, p, w, hp, _, hwpos, hw, hbary⟩ := exists_positive_contact_simplex hs hne hmin
  have hj := contact_jung_bound hn p w R (fun i => (hp i).2) (fun i => (hwpos i).le)
    hw hbary (fun i j => within _ (hp i).1 _ (hp j).1)
  have hn_eq : n = 5 := by
    by_contra hn'
    have nt : (n : ℝ) ≤ 4 := by exact_mod_cast (show n ≤ 4 by omega)
    have np : 0 < (n : ℝ) := by exact_mod_cast hn
    have hz := (le_div_iff₀ (by positivity : 0 < 2*(n : ℝ))).mp hj
    nlinarith [mul_pos np (show 0 < R^2-3/8 by linarith)]
  subst n
  refine ⟨fun i => D • (c + alpha • p i), D*rho, mul_pos hD (by norm_num [rho]), ?_, ?_⟩
  · change 2*(D*rho) < D
    dsimp [rho]
    linarith
  · intro x hx y hy hxy
    by_contra! nohit
    have miss (v : EuclideanSpace ℝ (Fin 4))
        (hv : ∀ i, v ∉ ball (D • (c + alpha • p i)) (D*rho)) : Missed p (f v) := by
      intro i
      have h := hv i
      rw [mem_ball, change_center D hD] at h
      exact le_of_not_gt (fun hh => h (mul_lt_mul_of_pos_left hh hD))
    have fx : f x ∈ S := ⟨x,hx,rfl⟩
    have fy : f y ∈ S := ⟨y,hy,rfl⟩
    have mass (z) (hz : z ∈ S) : ‖z‖^2 ≤ R^2 := by
      exact pow_le_pow_left₀ (norm_nonneg z)
        (by simpa [R] using dist_le_radiusAt hs hne hz 0) 2
    apply missed_pair_ne_one w p (R^2) (fun i => (hwpos i).le) hw hbary
      (fun i => by rw [(hp i).2]) hRlo hRhi (fun i j => within _ (hp i).1 _ (hp j).1)
      (f x) (f y) (mass _ fx) (mass _ fy) (fun i => within _ fx _ (hp i).1)
      (fun i => within _ fy _ (hp i).1) (miss x (fun i => (nohit i).1)) (miss y (fun i => (nohit i).2))
    dsimp only [f]
    rw [dist_sub_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hD), hxy]
    exact inv_mul_cancel₀ hD.ne'


theorem OMA.solution : OMA.R_Borsuk_borsuk_conjecture_four_eight_parts_R1.H2 := by
  intro K hK hnt high
  exact hit_five hK hnt high
