import FormalConjectures.ErdosProblems.«633»

/-!
# Existence of a Triangle Simili-Cuttable Only for `n ∉ {0, 2, 3, 5}`

We prove `Erdos633.exists_isSimiliCuttable_iff_ne_zero_two_three_five`: there exists a triangle
`T` in `ℝ²` such that `IsSimiliCuttable n T ↔ n ≠ 0 ∧ n ≠ 2 ∧ n ≠ 3 ∧ n ≠ 5` (Soifer 2009).

1. **Positive direction (`n ∉ {0, 2, 3, 5}`)**: Every triangle `T` is simili-cuttable into `1`,
   into `2 * m` (`m ≥ 2`) via barycentric homotheties, and into `n + 3` from `n ≥ 1` by
   subdividing one tile into `4` similar sub-triangles.
2. **Negative direction (`n ∈ {2, 3, 5}`)**: Choose `T` whose interior angles `A, B, C` are
   `ℤ`-linearly independent. For any simili-cutting `Ts : Fin n → Triangle ℝ ℝ²` of `T`,
   integrating the indicator of `p + r • (cos θ, sin θ)` around small circles centered at each
   point `p ∈ ℝ²` yields the local angular sum identity `∑ i, localAngle (Ts i) p = localAngle T p`.
   At the three corners of `T`, this yields an invertible `3 × 3` nonnegative integer matrix
   relating the common tile angles `(θ₀, θ₁, θ₂)` to `(A, B, C)`, forcing `(θ₀, θ₁, θ₂)` to be
   `ℤ`-linearly independent, every non-corner tile vertex to have degree `3` (for `n ≤ 5`), every
   corner of `T` to be covered by a unique tile, and the number of non-corner vertices to be `n - 1`.
   - `n = 2`: `1` non-corner vertex requires `3` tiles, impossible.
   - `n = 3`: `2` non-corner vertices both lie in all `3` tiles, forcing two tiles onto the same
     side of the shared edge and producing overlapping interiors.
   - `n = 5`: the `3` corner tiles are distinct and place their non-corner vertices on the open
     edges of `T`; the remaining `2` tiles share an edge `[p₁, p₂]` among the `4` non-corner
     vertices, and degree accounting forces both `p₁` and `p₂` onto the same open edge of `T`,
     putting both remaining tiles on the inward side of that edge with overlapping interiors.
-/

-- Problem: Erdős Problem 633 — exists isSimiliCuttable iff ne zero two three five
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/633.lean:116 (declaration Erdos633.exists_isSimiliCuttable_iff_ne_zero_two_three_five)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace Erdos633ExistsSimiliCuttableProof

open Affine MeasureTheory
open scoped EuclideanGeometry Similar NNReal Real Classical

/- Part 1: Positive direction (`n ∉ {0, 2, 3, 5}`) -/

private def vec3 (x y z : ℝ) : Fin 3 → ℝ
  | 0 => x
  | 1 => y
  | 2 => z

private lemma affineCombination_eq_imp (T : Triangle ℝ ℝ²) {w₁ w₂ : Fin 3 → ℝ}
    (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ i = 1)
    (h : Finset.univ.affineCombination ℝ T.points w₁ =
      Finset.univ.affineCombination ℝ T.points w₂) : w₁ = w₂ := by
  have hind := T.independent.indicator_eq_of_affineCombination_eq
    Finset.univ Finset.univ w₁ w₂ hw₁ hw₂ h
  simpa using hind

private noncomputable def homothetyMap (s : ℝ) (c : ℝ²) : ℝ² →ᵃ[ℝ] ℝ² where
  toFun x := s • x + c
  linear := s • LinearMap.id
  map_vadd' p v := by
    change s • (v + p) + c = s • v + (s • p + c)
    rw [smul_add, add_assoc]

private lemma homothetyMap_injective {s : ℝ} (hs : s ≠ 0) (c : ℝ²) :
    Function.Injective (homothetyMap s c) := by
  intro x y h
  change s • x + c = s • y + c at h
  exact smul_right_injective ℝ² hs (add_right_cancel h)

private noncomputable def subTri (T : Triangle ℝ ℝ²) (s : ℝ) (hs : s ≠ 0)
    (a : Fin 3 → ℝ) : Triangle ℝ ℝ² :=
  T.map (homothetyMap s (∑ i : Fin 3, a i • T.points i)) (homothetyMap_injective hs _)

private lemma subTri_similar (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s ≠ 0) (a : Fin 3 → ℝ) :
    (subTri T s hs a).points ∼ T.points := by
  refine ⟨⟨|s|, abs_nonneg s⟩, ?_, fun i j => ?_⟩
  · intro h
    have h0 : |s| = 0 := congrArg NNReal.toReal h
    exact hs (abs_eq_zero.mp h0)
  · simp only [subTri, Simplex.map_points, Function.comp_apply, homothetyMap, AffineMap.coe_mk]
    rw [edist_dist, edist_dist]
    have hd : dist (s • T.points i + ∑ k : Fin 3, a k • T.points k)
        (s • T.points j + ∑ k : Fin 3, a k • T.points k) =
        |s| * dist (T.points i) (T.points j) := by
      rw [dist_add_right, dist_smul₀, Real.norm_eq_abs]
    rw [hd, ENNReal.ofReal_mul (abs_nonneg s), ENNReal.ofReal_eq_coe_nnreal (abs_nonneg s)]
    rfl

private lemma subTri_affineCombination (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s ≠ 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {u : Fin 3 → ℝ} (hu : ∑ i, u i = 1) :
    Finset.univ.affineCombination ℝ (subTri T s hs a).points u =
      Finset.univ.affineCombination ℝ T.points (fun i => a i + s * u i) := by
  have hw : ∑ i : Fin 3, (a i + s * u i) = 1 := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha, hu]
    ring
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hu,
    Finset.affineCombination_eq_linear_combination _ _ _ hw]
  simp only [subTri, Simplex.map_points, Function.comp_apply, homothetyMap, AffineMap.coe_mk,
    smul_add, add_smul, Finset.sum_add_distrib]
  have hsmul : ∑ i : Fin 3, u i • ∑ k : Fin 3, a k • T.points k =
      (∑ i : Fin 3, u i) • ∑ k : Fin 3, a k • T.points k :=
    Finset.sum_smul.symm
  rw [hsmul, hu, one_smul, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_comm]

private lemma mem_subTri_setInterior_iff (I : Set ℝ) (T : Triangle ℝ ℝ²)
    {s : ℝ} (hs : s ≠ 0) {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s hs a).setInterior I ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, (w i - a i) / s ∈ I) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  constructor
  · rintro ⟨u, hu, huI, rfl⟩
    refine ⟨fun i => a i + s * u i, ?_, ?_, (subTri_affineCombination T hs ha hu).symm⟩
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha, hu]
      ring
    · intro i
      have hdiv : (a i + s * u i - a i) / s = u i := by
        field_simp [hs]
        ring
      rw [hdiv]
      exact huI i
  · rintro ⟨w, hw, hwI, rfl⟩
    let u : Fin 3 → ℝ := fun i => (w i - a i) / s
    have hu : ∑ i : Fin 3, u i = 1 := by
      simp only [u, ← Finset.sum_div, Finset.sum_sub_distrib, hw, ha]
      field_simp [hs]
      ring
    refine ⟨u, hu, hwI, ?_⟩
    rw [subTri_affineCombination T hs ha hu]
    congr 1
    funext i
    simp only [u]
    field_simp [hs]
    ring

private lemma mem_subTri_closedInterior_pos (T : Triangle ℝ ℝ²) {s : ℝ} (hs : 0 < s)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_gt hs) a).closedInterior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, a i ≤ w i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_gt hs) a).setInterior (Set.Icc 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Icc 0 1) T (ne_of_gt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  constructor
  · intro h i
    have h0 : 0 ≤ (w i - a i) / s := (h i).1
    have h1 : 0 ≤ w i - a i := (div_nonneg_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (w 0 - a 0) + (w 1 - a 1) + (w 2 - a 2) = s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 ≤ w 0 - a 0 := sub_nonneg.mpr (h 0)
    have h1 : 0 ≤ w 1 - a 1 := sub_nonneg.mpr (h 1)
    have h2 : 0 ≤ w 2 - a 2 := sub_nonneg.mpr (h 2)
    have hle : w i - a i ≤ s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    exact ⟨div_nonneg (sub_nonneg.mpr (h i)) (le_of_lt hs), (div_le_one hs).mpr hle⟩

private lemma mem_subTri_interior_pos (T : Triangle ℝ ℝ²) {s : ℝ} (hs : 0 < s)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_gt hs) a).interior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, a i < w i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_gt hs) a).setInterior (Set.Ioo 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Ioo 0 1) T (ne_of_gt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  constructor
  · intro h i
    have h0 : 0 < (w i - a i) / s := (h i).1
    have h1 : 0 < w i - a i := (div_pos_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (w 0 - a 0) + (w 1 - a 1) + (w 2 - a 2) = s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 < w 0 - a 0 := sub_pos.mpr (h 0)
    have h1 : 0 < w 1 - a 1 := sub_pos.mpr (h 1)
    have h2 : 0 < w 2 - a 2 := sub_pos.mpr (h 2)
    have hlt : w i - a i < s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    exact ⟨div_pos (sub_pos.mpr (h i)) hs, (div_lt_one hs).mpr hlt⟩

private lemma mem_subTri_closedInterior_neg (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s < 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_lt hs) a).closedInterior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, w i ≤ a i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_lt hs) a).setInterior (Set.Icc 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Icc 0 1) T (ne_of_lt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  have ht : 0 < -s := neg_pos.mpr hs
  constructor
  · intro h i
    have h0 : 0 ≤ (a i - w i) / (-s) := by
      have : (a i - w i) / (-s) = (w i - a i) / s := by field_simp [ne_of_lt hs]; ring
      rw [this]
      exact (h i).1
    have h1 : 0 ≤ a i - w i := (div_nonneg_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (a 0 - w 0) + (a 1 - w 1) + (a 2 - w 2) = -s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 ≤ a 0 - w 0 := sub_nonneg.mpr (h 0)
    have h1 : 0 ≤ a 1 - w 1 := sub_nonneg.mpr (h 1)
    have h2 : 0 ≤ a 2 - w 2 := sub_nonneg.mpr (h 2)
    have hle : a i - w i ≤ -s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    have heq : (w i - a i) / s = (a i - w i) / (-s) := by field_simp [ne_of_lt hs]; ring
    rw [heq]
    exact ⟨div_nonneg (sub_nonneg.mpr (h i)) (le_of_lt ht), (div_le_one ht).mpr hle⟩

private lemma mem_subTri_interior_neg (T : Triangle ℝ ℝ²) {s : ℝ} (hs : s < 0)
    {a : Fin 3 → ℝ} (ha : ∑ i, a i = 1 - s) {x : ℝ²} :
    x ∈ (subTri T s (ne_of_lt hs) a).interior ↔
      ∃ w : Fin 3 → ℝ, (∑ i, w i = 1) ∧
        (∀ i, w i < a i) ∧
        Finset.univ.affineCombination ℝ T.points w = x := by
  change x ∈ (subTri T s (ne_of_lt hs) a).setInterior (Set.Ioo 0 1) ↔ _
  rw [mem_subTri_setInterior_iff (Set.Ioo 0 1) T (ne_of_lt hs) ha]
  refine exists_congr fun w => and_congr_right fun hw => and_congr_left fun _ => ?_
  have ht : 0 < -s := neg_pos.mpr hs
  constructor
  · intro h i
    have h0 : 0 < (a i - w i) / (-s) := by
      have : (a i - w i) / (-s) = (w i - a i) / s := by field_simp [ne_of_lt hs]; ring
      rw [this]
      exact (h i).1
    have h1 : 0 < a i - w i := (div_pos_iff.mp h0).elim (fun h' => h'.1) (fun h' => by linarith)
    linarith
  · intro h i
    have hsum : (a 0 - w 0) + (a 1 - w 1) + (a 2 - w 2) = -s := by
      rw [Fin.sum_univ_three] at hw ha
      linarith
    have h0 : 0 < a 0 - w 0 := sub_pos.mpr (h 0)
    have h1 : 0 < a 1 - w 1 := sub_pos.mpr (h 1)
    have h2 : 0 < a 2 - w 2 := sub_pos.mpr (h 2)
    have hlt : a i - w i < -s := match i with
      | 0 => by linarith
      | 1 => by linarith
      | 2 => by linarith
    have heq : (w i - a i) / s = (a i - w i) / (-s) := by field_simp [ne_of_lt hs]; ring
    rw [heq]
    exact ⟨div_pos (sub_pos.mpr (h i)) ht, (div_lt_one ht).mpr hlt⟩

private lemma mem_closedInterior_of_nonneg (T : Triangle ℝ ℝ²) {w : Fin 3 → ℝ}
    (hw : ∑ i, w i = 1) (hnn : ∀ i, 0 ≤ w i) :
    Finset.univ.affineCombination ℝ T.points w ∈ T.closedInterior := by
  rw [T.affineCombination_mem_closedInterior_iff hw]
  intro i
  rw [Fin.sum_univ_three] at hw
  have h0 := hnn 0
  have h1 := hnn 1
  have h2 := hnn 2
  refine ⟨hnn i, ?_⟩
  match i with
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith

private lemma mem_interior_of_pos (T : Triangle ℝ ℝ²) {w : Fin 3 → ℝ}
    (hw : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) :
    Finset.univ.affineCombination ℝ T.points w ∈ T.interior := by
  rw [T.affineCombination_mem_interior_iff hw]
  intro i
  rw [Fin.sum_univ_three] at hw
  have h0 := hpos 0
  have h1 := hpos 1
  have h2 := hpos 2
  refine ⟨hpos i, ?_⟩
  match i with
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith

private def StrongSimiliCuttable (n : ℕ) (T : Triangle ℝ ℝ²) : Prop :=
  ∃ Ts : Fin n → Triangle ℝ ℝ²,
    (∀ i, (Ts i).points ∼ T.points) ∧
    (∀ i, (Ts i).interior ⊆ T.interior) ∧
    Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior) ∧
    ⋃ i, (Ts i).closedInterior = T.closedInterior

private lemma StrongSimiliCuttable.toIsSimiliCuttable {n : ℕ} {T : Triangle ℝ ℝ²}
    (h : StrongSimiliCuttable n T) : Erdos633.IsSimiliCuttable n T := by
  rcases h with ⟨Ts, hsim, -, hdisj, hunion⟩
  exact ⟨Ts, fun i j => (hsim i).trans (hsim j).symm, hdisj, hunion⟩

private lemma strongSimiliCuttable_one (T : Triangle ℝ ℝ²) : StrongSimiliCuttable 1 T := by
  refine ⟨fun _ => T, fun _ => Similar.refl _, fun _ => Set.Subset.rfl, ?_, ?_⟩
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  · ext x
    simp

private lemma strongSimiliCuttable_two_mul (m : ℕ) (hm : 2 ≤ m) (T : Triangle ℝ ℝ²) :
    StrongSimiliCuttable (2 * m) T := by
  let mr : ℝ := (m : ℝ)
  have hmr_pos : 0 < mr := by
    dsimp only [mr]
    exact_mod_cast (by omega : 0 < m)
  have hmr_ge2 : (2 : ℝ) ≤ mr := by
    dsimp only [mr]
    exact_mod_cast hm
  have hs_big_pos : 0 < (mr - 1) / mr := div_pos (by linarith) hmr_pos
  have hs_up_pos : 0 < 1 / mr := div_pos one_pos hmr_pos
  have hs_inv_neg : -1 / mr < 0 := div_neg_of_neg_of_pos (by norm_num) hmr_pos
  let aBig : Fin 3 → ℝ := vec3 (1 / mr) 0 0
  have haBig : ∑ i : Fin 3, aBig i = 1 - (mr - 1) / mr := by
    rw [Fin.sum_univ_three]
    change 1 / mr + 0 + 0 = 1 - (mr - 1) / mr
    field_simp [ne_of_gt hmr_pos]
    ring
  let aUp (j : Fin m) : Fin 3 → ℝ := vec3 0 ((j.1 : ℝ) / mr) ((mr - 1 - (j.1 : ℝ)) / mr)
  have haUp (j : Fin m) : ∑ i : Fin 3, aUp j i = 1 - 1 / mr := by
    rw [Fin.sum_univ_three]
    change 0 + (j.1 : ℝ) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - 1 / mr
    field_simp [ne_of_gt hmr_pos]
    ring
  let aInv (j : Fin (m - 1)) : Fin 3 → ℝ :=
    vec3 (1 / mr) (((j.1 : ℝ) + 1) / mr) ((mr - 1 - (j.1 : ℝ)) / mr)
  have haInv (j : Fin (m - 1)) : ∑ i : Fin 3, aInv j i = 1 - (-1 / mr) := by
    rw [Fin.sum_univ_three]
    change 1 / mr + ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (-1 / mr)
    field_simp [ne_of_gt hmr_pos]
    ring
  let idx := Unit ⊕ Fin m ⊕ Fin (m - 1)
  let tile : idx → Triangle ℝ ℝ²
    | Sum.inl () => subTri T ((mr - 1) / mr) (ne_of_gt hs_big_pos) aBig
    | Sum.inr (Sum.inl j) => subTri T (1 / mr) (ne_of_gt hs_up_pos) (aUp j)
    | Sum.inr (Sum.inr j) => subTri T (-1 / mr) (ne_of_lt hs_inv_neg) (aInv j)
  have hcard : Fintype.card idx = 2 * m := by
    dsimp only [idx]
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_fin]
    omega
  let e : Fin (2 * m) ≃ idx := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => tile (e i), ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with ⟨⟩ | j | j
    · exact subTri_similar T (ne_of_gt hs_big_pos) aBig
    · exact subTri_similar T (ne_of_gt hs_up_pos) (aUp j)
    · exact subTri_similar T (ne_of_lt hs_inv_neg) (aInv j)
  · intro i x hx
    dsimp only at hx
    generalize e i = p at hx
    rcases p with ⟨⟩ | j | j
    · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      refine mem_interior_of_pos T hw fun k => ?_
      have hk := hlt k
      match k with
      | 0 =>
        change 1 / mr < w 0 at hk
        linarith [div_pos one_pos hmr_pos]
      | 1 => exact hk
      | 2 => exact hk
    · rw [mem_subTri_interior_pos T hs_up_pos (haUp j)] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      have hj_le : (j.1 : ℝ) ≤ mr - 1 := by
        have h1 : j.1 + 1 ≤ m := j.2
        have h2 : (j.1 : ℝ) + 1 ≤ mr := by dsimp only [mr]; exact_mod_cast h1
        linarith
      refine mem_interior_of_pos T hw fun k => ?_
      have hk := hlt k
      match k with
      | 0 => exact hk
      | 1 =>
        change (j.1 : ℝ) / mr < w 1 at hk
        have hnn : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
        linarith
      | 2 =>
        change (mr - 1 - (j.1 : ℝ)) / mr < w 2 at hk
        have hnn : (0 : ℝ) ≤ (mr - 1 - (j.1 : ℝ)) / mr :=
          div_nonneg (by linarith) (le_of_lt hmr_pos)
        linarith
    · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j)] at hx
      rcases hx with ⟨w, hw, hlt, rfl⟩
      have hj_le : (j.1 : ℝ) + 2 ≤ mr := by
        have h1 : j.1 + 2 ≤ m := by omega
        dsimp only [mr]
        exact_mod_cast h1
      rw [Fin.sum_univ_three] at hw
      have h0 : w 0 < 1 / mr := hlt 0
      have h1 : w 1 < ((j.1 : ℝ) + 1) / mr := hlt 1
      have h2 : w 2 < (mr - 1 - (j.1 : ℝ)) / mr := hlt 2
      have hsum12 : ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hsum02 : 1 / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (j.1 : ℝ) / mr := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hsum01 : 1 / mr + ((j.1 : ℝ) + 1) / mr = 1 - (mr - 2 - (j.1 : ℝ)) / mr := by
        field_simp [ne_of_gt hmr_pos]; ring
      have hnn1 : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
      have hnn2 : (0 : ℝ) ≤ (mr - 2 - (j.1 : ℝ)) / mr :=
        div_nonneg (by linarith) (le_of_lt hmr_pos)
      refine mem_interior_of_pos T (by rw [Fin.sum_univ_three]; exact hw) fun k => ?_
      match k with
      | 0 => linarith
      | 1 => linarith
      | 2 => linarith
  · intro i₁ i₂ hne
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    have he_ne : e i₁ ≠ e i₂ := fun h => hne (e.injective h)
    have hdisj_idx : ∀ p₁ p₂ : idx, p₁ ≠ p₂ →
        x ∈ (tile p₁).interior → x ∈ (tile p₂).interior → False := by
      intro p₁ p₂ hp hx1 hx2
      rcases p₁ with ⟨⟩ | j₁ | j₁ <;> rcases p₂ with ⟨⟩ | j₂ | j₂
      · exact hp rfl
      · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hb0 : 1 / mr < w₁ 0 := h1 0
        have hu1 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have hu2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        have hsum : 1 / mr + (j₂.1 : ℝ) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        linarith
      · rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hb0 : 1 / mr < w₁ 0 := h1 0
        have hi0 : w₁ 0 < 1 / mr := h2 0
        linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hb0 : 1 / mr < w₁ 0 := h2 0
        have hu1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have hu2 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have hsum : 1 / mr + (j₁.1 : ℝ) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hjne : j₁.1 ≠ j₂.1 := fun h => hp (by rw [Fin.ext h])
        have h0_1 : 0 < w₁ 0 := h1 0
        have h1_1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have h2_1 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have h1_2 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have h2_2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        rcases lt_or_gt_of_ne hjne with hlt | hgt
        · have hle : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hlt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : ((j₁.1 : ℝ) + 1) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
        · have hle : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : ((j₂.1 : ℝ) + 1) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
      · rw [mem_subTri_interior_pos T hs_up_pos (haUp j₁)] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hu1 : (j₁.1 : ℝ) / mr < w₁ 1 := h1 1
        have hu2 : (mr - 1 - (j₁.1 : ℝ)) / mr < w₁ 2 := h1 2
        have hi1 : w₁ 1 < ((j₂.1 : ℝ) + 1) / mr := h2 1
        have hi2 : w₁ 2 < (mr - 1 - (j₂.1 : ℝ)) / mr := h2 2
        rcases le_or_gt j₁.1 j₂.1 with hle | hgt
        · have hle' : (j₁.1 : ℝ) ≤ (j₂.1 : ℝ) := by exact_mod_cast hle
          have hdiv : (mr - 1 - (j₂.1 : ℝ)) / mr ≤ (mr - 1 - (j₁.1 : ℝ)) / mr :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hmr_pos)
          linarith
        · have hle' : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle' (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_big_pos haBig] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hi0 : w₁ 0 < 1 / mr := h1 0
        have hb0 : 1 / mr < w₁ 0 := h2 0
        linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_pos T hs_up_pos (haUp j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        have hi1 : w₁ 1 < ((j₁.1 : ℝ) + 1) / mr := h1 1
        have hi2 : w₁ 2 < (mr - 1 - (j₁.1 : ℝ)) / mr := h1 2
        have hu1 : (j₂.1 : ℝ) / mr < w₁ 1 := h2 1
        have hu2 : (mr - 1 - (j₂.1 : ℝ)) / mr < w₁ 2 := h2 2
        rcases le_or_gt j₂.1 j₁.1 with hle | hgt
        · have hle' : (j₂.1 : ℝ) ≤ (j₁.1 : ℝ) := by exact_mod_cast hle
          have hdiv : (mr - 1 - (j₁.1 : ℝ)) / mr ≤ (mr - 1 - (j₂.1 : ℝ)) / mr :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hmr_pos)
          linarith
        · have hle' : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle' (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₁)] at hx1
        rw [mem_subTri_interior_neg T hs_inv_neg (haInv j₂)] at hx2
        rcases hx1 with ⟨w₁, hw₁, h1, rfl⟩
        rcases hx2 with ⟨w₂, hw₂, h2, hweq⟩
        have hww : w₁ = w₂ := affineCombination_eq_imp T hw₁ hw₂ hweq.symm
        subst hww
        rw [Fin.sum_univ_three] at hw₁
        have hjne : j₁.1 ≠ j₂.1 := fun h => hp (by rw [Fin.ext h])
        have h0_1 : w₁ 0 < 1 / mr := h1 0
        have h1_1 : w₁ 1 < ((j₁.1 : ℝ) + 1) / mr := h1 1
        have h2_1 : w₁ 2 < (mr - 1 - (j₁.1 : ℝ)) / mr := h1 2
        have h1_2 : w₁ 1 < ((j₂.1 : ℝ) + 1) / mr := h2 1
        have h2_2 : w₁ 2 < (mr - 1 - (j₂.1 : ℝ)) / mr := h2 2
        rcases lt_or_gt_of_ne hjne with hlt | hgt
        · have hle : (j₁.1 : ℝ) + 1 ≤ (j₂.1 : ℝ) := by exact_mod_cast hlt
          have hdiv : ((j₁.1 : ℝ) + 1) / mr ≤ (j₂.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : 1 / mr + (j₂.1 : ℝ) / mr + (mr - 1 - (j₂.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
        · have hle : (j₂.1 : ℝ) + 1 ≤ (j₁.1 : ℝ) := by exact_mod_cast hgt
          have hdiv : ((j₂.1 : ℝ) + 1) / mr ≤ (j₁.1 : ℝ) / mr :=
            div_le_div_of_nonneg_right hle (le_of_lt hmr_pos)
          have hsum : 1 / mr + (j₁.1 : ℝ) / mr + (mr - 1 - (j₁.1 : ℝ)) / mr = 1 := by
            field_simp [ne_of_gt hmr_pos]; ring
          linarith
    exact hdisj_idx (e i₁) (e i₂) he_ne hx₁ hx₂
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      generalize e i = p at hx
      rcases p with ⟨⟩ | j | j
      · rw [mem_subTri_closedInterior_pos T hs_big_pos haBig] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        refine mem_closedInterior_of_nonneg T hw fun k => ?_
        have hk := hle k
        match k with
        | 0 =>
          change 1 / mr ≤ w 0 at hk
          linarith [div_pos one_pos hmr_pos]
        | 1 => exact hk
        | 2 => exact hk
      · rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp j)] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        have hj_le : (j.1 : ℝ) ≤ mr - 1 := by
          have h1 : j.1 + 1 ≤ m := j.2
          have h2 : (j.1 : ℝ) + 1 ≤ mr := by dsimp only [mr]; exact_mod_cast h1
          linarith
        refine mem_closedInterior_of_nonneg T hw fun k => ?_
        have hk := hle k
        match k with
        | 0 => exact hk
        | 1 =>
          change (j.1 : ℝ) / mr ≤ w 1 at hk
          have hnn : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
          linarith
        | 2 =>
          change (mr - 1 - (j.1 : ℝ)) / mr ≤ w 2 at hk
          have hnn : (0 : ℝ) ≤ (mr - 1 - (j.1 : ℝ)) / mr :=
            div_nonneg (by linarith) (le_of_lt hmr_pos)
          linarith
      · rw [mem_subTri_closedInterior_neg T hs_inv_neg (haInv j)] at hx
        rcases hx with ⟨w, hw, hle, rfl⟩
        have hj_le : (j.1 : ℝ) + 2 ≤ mr := by
          have h1 : j.1 + 2 ≤ m := by omega
          dsimp only [mr]
          exact_mod_cast h1
        rw [Fin.sum_univ_three] at hw
        have h0 : w 0 ≤ 1 / mr := hle 0
        have h1 : w 1 ≤ ((j.1 : ℝ) + 1) / mr := hle 1
        have h2 : w 2 ≤ (mr - 1 - (j.1 : ℝ)) / mr := hle 2
        have hsum12 : ((j.1 : ℝ) + 1) / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hsum02 : 1 / mr + (mr - 1 - (j.1 : ℝ)) / mr = 1 - (j.1 : ℝ) / mr := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hsum01 : 1 / mr + ((j.1 : ℝ) + 1) / mr = 1 - (mr - 2 - (j.1 : ℝ)) / mr := by
          field_simp [ne_of_gt hmr_pos]; ring
        have hnn1 : (0 : ℝ) ≤ (j.1 : ℝ) / mr := div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr_pos)
        have hnn2 : (0 : ℝ) ≤ (mr - 2 - (j.1 : ℝ)) / mr :=
          div_nonneg (by linarith) (le_of_lt hmr_pos)
        refine mem_closedInterior_of_nonneg T (by rw [Fin.sum_univ_three]; exact hw) fun k => ?_
        match k with
        | 0 => linarith
        | 1 => linarith
        | 2 => linarith
    · rintro ⟨w, hw, hwI, rfl⟩
      have hw0 : 0 ≤ w 0 := (hwI 0).1
      have hw1 : 0 ≤ w 1 := (hwI 1).1
      have hw2 : 0 ≤ w 2 := (hwI 2).1
      have hw1_le : w 1 ≤ 1 := (hwI 1).2
      have hcover : ∃ p : idx, Finset.univ.affineCombination ℝ T.points w ∈ (tile p).closedInterior := by
        by_cases hbig : 1 / mr ≤ w 0
        · refine ⟨Sum.inl (), ?_⟩
          rw [mem_subTri_closedInterior_pos T hs_big_pos haBig]
          refine ⟨w, hw, fun k => ?_, rfl⟩
          match k with
          | 0 => exact hbig
          | 1 => exact hw1
          | 2 => exact hw2
        · push Not at hbig
          by_cases hw1_eq : w 1 = 1
          · let jlast : Fin m := ⟨m - 1, by omega⟩
            refine ⟨Sum.inr (Sum.inl jlast), ?_⟩
            rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp jlast)]
            have hjlast : (jlast.1 : ℝ) = mr - 1 := by
              dsimp only [jlast, mr]
              rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
            refine ⟨w, hw, fun k => ?_, rfl⟩
            match k with
            | 0 => exact hw0
            | 1 =>
              change (jlast.1 : ℝ) / mr ≤ w 1
              rw [hjlast, hw1_eq]
              exact (div_le_one hmr_pos).mpr (by linarith)
            | 2 =>
              change (mr - 1 - (jlast.1 : ℝ)) / mr ≤ w 2
              rw [hjlast]
              have hzero : (mr - 1 - (mr - 1)) / mr = 0 := by ring
              rw [hzero]
              exact hw2
          · have hw1_lt : w 1 < 1 := lt_of_le_of_ne hw1_le hw1_eq
            let jnat : ℕ := Nat.floor (mr * w 1)
            have hjnat_lt : jnat < m := by
              have hlt : mr * w 1 < mr := by nlinarith
              have hlt' : mr * w 1 < (m : ℝ) := hlt
              exact (Nat.floor_lt (mul_nonneg (le_of_lt hmr_pos) hw1)).mpr hlt'
            have hjnat_le : (jnat : ℝ) ≤ mr * w 1 :=
              Nat.floor_le (mul_nonneg (le_of_lt hmr_pos) hw1)
            have hjnat_gt : mr * w 1 < (jnat : ℝ) + 1 := Nat.lt_floor_add_one (mr * w 1)
            have hw1_lo : (jnat : ℝ) / mr ≤ w 1 := (div_le_iff₀ hmr_pos).mpr (by linarith)
            have hw1_hi : w 1 ≤ ((jnat : ℝ) + 1) / mr := (le_div_iff₀ hmr_pos).mpr (by linarith)
            by_cases hup : (mr - 1 - (jnat : ℝ)) / mr ≤ w 2
            · refine ⟨Sum.inr (Sum.inl ⟨jnat, hjnat_lt⟩), ?_⟩
              rw [mem_subTri_closedInterior_pos T hs_up_pos (haUp ⟨jnat, hjnat_lt⟩)]
              refine ⟨w, hw, fun k => ?_, rfl⟩
              match k with
              | 0 => exact hw0
              | 1 => exact hw1_lo
              | 2 => exact hup
            · push Not at hup
              have hjnat_lt' : jnat < m - 1 := by
                by_contra hge
                have hjeq : jnat = m - 1 := by omega
                have hjr : (jnat : ℝ) = mr - 1 := by
                  rw [hjeq, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
                rw [hjr] at hup
                have hzero : (mr - 1 - (mr - 1)) / mr = 0 := by ring
                linarith
              refine ⟨Sum.inr (Sum.inr ⟨jnat, hjnat_lt'⟩), ?_⟩
              rw [mem_subTri_closedInterior_neg T hs_inv_neg (haInv ⟨jnat, hjnat_lt'⟩)]
              refine ⟨w, hw, fun k => ?_, rfl⟩
              match k with
              | 0 => exact le_of_lt hbig
              | 1 => exact hw1_hi
              | 2 => exact le_of_lt hup
      rcases hcover with ⟨p, hp⟩
      exact ⟨e.symm p, by simpa using hp⟩

private lemma strongSimiliCuttable_add_three {n : ℕ} (hn : 1 ≤ n) {T : Triangle ℝ ℝ²}
    (h : StrongSimiliCuttable n T) : StrongSimiliCuttable (n + 3) T := by
  rcases h with ⟨Ts, hsim, hint, hdisj, hunion⟩
  let i0 : Fin n := ⟨0, by omega⟩
  obtain ⟨Us, hUsim, hUint, hUdisj, hUunion⟩ := strongSimiliCuttable_two_mul 2 (le_refl 2) (Ts i0)
  let idx := Fin 4 ⊕ Fin (n - 1)
  let tile : idx → Triangle ℝ ℝ²
    | Sum.inl k => Us k
    | Sum.inr j => Ts ⟨j.1 + 1, by omega⟩
  have hcard : Fintype.card idx = n + 3 := by
    dsimp only [idx]
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    omega
  let e : Fin (n + 3) ≃ idx := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => tile (e i), ?_, ?_, ?_, ?_⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with k | j
    · exact (hUsim k).trans (hsim i0)
    · exact hsim ⟨j.1 + 1, by omega⟩
  · intro i
    dsimp only
    generalize e i = p
    rcases p with k | j
    · exact (hUint k).trans (hint i0)
    · exact hint ⟨j.1 + 1, by omega⟩
  · intro i₁ i₂ hne
    dsimp only
    have he_ne : e i₁ ≠ e i₂ := fun h => hne (e.injective h)
    generalize e i₁ = p₁ at he_ne ⊢
    generalize e i₂ = p₂ at he_ne ⊢
    rcases p₁ with k₁ | j₁ <;> rcases p₂ with k₂ | j₂
    · have hk : k₁ ≠ k₂ := fun h => he_ne (by rw [h])
      exact hUdisj hk
    · have hne' : i0 ≠ ⟨j₂.1 + 1, by omega⟩ := by
        intro heq
        have : (0 : ℕ) = j₂.1 + 1 := congrArg Fin.val heq
        omega
      exact (hdisj hne').mono_left (hUint k₁)
    · have hne' : (⟨j₁.1 + 1, by omega⟩ : Fin n) ≠ i0 := by
        intro heq
        have : j₁.1 + 1 = 0 := congrArg Fin.val heq
        omega
      exact (hdisj hne').mono_right (hUint k₂)
    · have hj : (⟨j₁.1 + 1, by omega⟩ : Fin n) ≠ ⟨j₂.1 + 1, by omega⟩ := by
        intro heq
        have hval : j₁.1 = j₂.1 := by
          have : j₁.1 + 1 = j₂.1 + 1 := congrArg Fin.val heq
          omega
        exact he_ne (by rw [Fin.ext hval])
      exact hdisj hj
  · rw [← hunion]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      generalize e i = p at hx
      rcases p with k | j
      · refine ⟨i0, ?_⟩
        rw [← hUunion]
        exact Set.mem_iUnion.mpr ⟨k, hx⟩
      · exact ⟨⟨j.1 + 1, by omega⟩, hx⟩
    · rintro ⟨j, hx⟩
      by_cases hj : j.1 = 0
      · have hjeq : j = i0 := Fin.ext hj
        rw [hjeq, ← hUunion] at hx
        rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
        exact ⟨e.symm (Sum.inl k), by simpa [tile] using hk⟩
      · let j' : Fin (n - 1) := ⟨j.1 - 1, by omega⟩
        have hjeq : (⟨j'.1 + 1, by omega⟩ : Fin n) = j := Fin.ext (by dsimp [j']; omega)
        refine ⟨e.symm (Sum.inr j'), ?_⟩
        simpa [tile, hjeq] using hx

private lemma isSimiliCuttable_of_ne (T : Triangle ℝ ℝ²) {n : ℕ}
    (hn₀ : n ≠ 0) (hn₂ : n ≠ 2) (hn₃ : n ≠ 3) (hn₅ : n ≠ 5) :
    Erdos633.IsSimiliCuttable n T := by
  by_cases hn1 : n = 1
  · subst hn1
    exact (strongSimiliCuttable_one T).toIsSimiliCuttable
  · by_cases heven : n % 2 = 0
    · have hm : 2 ≤ n / 2 := by omega
      have heq : 2 * (n / 2) = n := by omega
      rw [← heq]
      exact (strongSimiliCuttable_two_mul (n / 2) hm T).toIsSimiliCuttable
    · have hge7 : 7 ≤ n := by omega
      have hm : 2 ≤ (n - 3) / 2 := by omega
      have heq1 : 2 * ((n - 3) / 2) = n - 3 := by omega
      have heq2 : (n - 3) + 3 = n := by omega
      have hbase : StrongSimiliCuttable (n - 3) T := by
        rw [← heq1]
        exact strongSimiliCuttable_two_mul ((n - 3) / 2) hm T
      rw [← heq2]
      exact (strongSimiliCuttable_add_three (by omega) hbase).toIsSimiliCuttable

/- Part 2: 2D Vector Geometry, Cross Product, and Barycentric Coordinates -/

private noncomputable def mk2 (x y : ℝ) : ℝ² := WithLp.toLp 2 ![x, y]

@[simp] private lemma mk2_zero (x y : ℝ) : mk2 x y 0 = x := rfl
@[simp] private lemma mk2_one (x y : ℝ) : mk2 x y 1 = y := rfl

private lemma ext2 {u v : ℝ²} (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  ext i
  fin_cases i <;> assumption

private lemma inner2 (u v : ℝ²) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  simp [mul_comm]

private lemma norm_sq2 (u : ℝ²) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp

private def cross (u v : ℝ²) : ℝ := u 0 * v 1 - u 1 * v 0

private lemma cross_cramer (u v w : ℝ²) :
    cross u v • w = cross w v • u + cross u w • v := by
  apply ext2 <;> (simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring)

private lemma cross_ne_zero_of_triangle (Δ : Triangle ℝ ℝ²) :
    cross (Δ.points 1 - Δ.points 0) (Δ.points 2 - Δ.points 0) ≠ 0 := by
  intro hzero
  have hind := (affineIndependent_iff_linearIndependent_vsub ℝ Δ.points (0 : Fin 3)).mp Δ.independent
  have h10 : Δ.points 1 - Δ.points 0 ≠ 0 :=
    sub_ne_zero.mpr (Δ.independent.injective.ne (by decide : (1 : Fin 3) ≠ 0))
  have hcoord : (Δ.points 1 - Δ.points 0) 0 ≠ 0 ∨ (Δ.points 1 - Δ.points 0) 1 ≠ 0 := by
    by_contra h
    push Not at h
    exact h10 (ext2 h.1 h.2)
  have hex : ∃ t : ℝ, Δ.points 2 - Δ.points 0 = t • (Δ.points 1 - Δ.points 0) := by
    rcases hcoord with h0 | h1
    · refine ⟨(Δ.points 2 - Δ.points 0) 0 / (Δ.points 1 - Δ.points 0) 0, ext2 ?_ ?_⟩
      · simp only [PiLp.smul_apply, smul_eq_mul]
        field_simp [h0]
      · simp only [PiLp.smul_apply, smul_eq_mul]
        simp only [cross] at hzero
        field_simp [h0]
        linarith
    · refine ⟨(Δ.points 2 - Δ.points 0) 1 / (Δ.points 1 - Δ.points 0) 1, ext2 ?_ ?_⟩
      · simp only [PiLp.smul_apply, smul_eq_mul]
        simp only [cross] at hzero
        field_simp [h1]
        linarith
      · simp only [PiLp.smul_apply, smul_eq_mul]
        field_simp [h1]
  rcases hex with ⟨t, ht⟩
  let f : {x : Fin 3 // x ≠ 0} → ℝ := fun x =>
    if x.1 = 1 then t else -1
  have hlin : ∑ x : {x : Fin 3 // x ≠ 0}, f x • (Δ.points x.1 -ᵥ Δ.points 0) = 0 := by
    have huniv : (Finset.univ : Finset {x : Fin 3 // x ≠ 0}) =
        {⟨1, by decide⟩, ⟨2, by decide⟩} := by
      ext ⟨x, hx⟩
      fin_cases x <;> simp at hx ⊢
    rw [huniv, Finset.sum_pair (by decide)]
    simp only [f, ↓reduceIte, (by decide : (2 : Fin 3) ≠ 1), vsub_eq_sub, neg_one_smul]
    rw [ht, add_neg_cancel]
  have hf := Fintype.linearIndependent_iff.mp hind f hlin ⟨2, by decide⟩
  simp only [f, (by decide : (2 : Fin 3) ≠ 1), ↓reduceIte] at hf
  norm_num at hf

private noncomputable def bary (Δ : Triangle ℝ ℝ²) (x : ℝ²) : Fin 3 → ℝ
  | 0 => cross (Δ.points 1 - x) (Δ.points 2 - x) /
      cross (Δ.points 1 - Δ.points 0) (Δ.points 2 - Δ.points 0)
  | 1 => cross (x - Δ.points 0) (Δ.points 2 - Δ.points 0) /
      cross (Δ.points 1 - Δ.points 0) (Δ.points 2 - Δ.points 0)
  | 2 => cross (Δ.points 1 - Δ.points 0) (x - Δ.points 0) /
      cross (Δ.points 1 - Δ.points 0) (Δ.points 2 - Δ.points 0)

private lemma bary_sum (Δ : Triangle ℝ ℝ²) (x : ℝ²) : ∑ k : Fin 3, bary Δ x k = 1 := by
  have hD := cross_ne_zero_of_triangle Δ
  rw [Fin.sum_univ_three]
  simp only [bary, cross, PiLp.sub_apply] at hD ⊢
  field_simp [hD]
  ring

private lemma bary_affineCombination (Δ : Triangle ℝ ℝ²) (x : ℝ²) :
    Finset.univ.affineCombination ℝ Δ.points (bary Δ x) = x := by
  have hD := cross_ne_zero_of_triangle Δ
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (bary_sum Δ x), Fin.sum_univ_three]
  simp only [cross, PiLp.sub_apply] at hD
  apply ext2 <;>
    (simp only [bary, cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul];
      field_simp [hD]; ring)

private lemma bary_unique (Δ : Triangle ℝ ℝ²) {w : Fin 3 → ℝ} (hw : ∑ k, w k = 1)
    {x : ℝ²} (hx : Finset.univ.affineCombination ℝ Δ.points w = x) : w = bary Δ x :=
  affineCombination_eq_imp Δ hw (bary_sum Δ x) (hx.trans (bary_affineCombination Δ x).symm)

private lemma mem_closedInterior_iff_bary (Δ : Triangle ℝ ℝ²) (x : ℝ²) :
    x ∈ Δ.closedInterior ↔ ∀ k : Fin 3, 0 ≤ bary Δ x k := by
  constructor
  · rintro ⟨w, hw, hwI, rfl⟩
    rw [← bary_unique Δ hw rfl]
    exact fun k => (hwI k).1
  · intro hnn
    rw [← bary_affineCombination Δ x]
    exact mem_closedInterior_of_nonneg Δ (bary_sum Δ x) hnn

private lemma mem_interior_iff_bary (Δ : Triangle ℝ ℝ²) (x : ℝ²) :
    x ∈ Δ.interior ↔ ∀ k : Fin 3, 0 < bary Δ x k := by
  constructor
  · rintro ⟨w, hw, hwI, rfl⟩
    rw [← bary_unique Δ hw rfl]
    exact fun k => (hwI k).1
  · intro hpos
    rw [← bary_affineCombination Δ x]
    exact mem_interior_of_pos Δ (bary_sum Δ x) hpos

private lemma fin3_cases (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  omega

private lemma fin3_sum_perm (f : Fin 3 → ℝ) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f a + f b + f c = f 0 + f 1 + f 2 := by
  rcases fin3_cases a with rfl | rfl | rfl <;>
  rcases fin3_cases b with rfl | rfl | rfl <;>
  rcases fin3_cases c with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | exact absurd rfl hac | exact absurd rfl hbc | ring

private lemma bary_point (Δ : Triangle ℝ ℝ²) (k j : Fin 3) :
    bary Δ (Δ.points k) j = if j = k then 1 else 0 := by
  let w : Fin 3 → ℝ := fun i => if i = k then 1 else 0
  have hw : ∑ i : Fin 3, w i = 1 := by simp [w]
  have hcomb : Finset.univ.affineCombination ℝ Δ.points w = Δ.points k := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
    simp [w]
  exact congrFun (bary_unique Δ hw hcomb).symm j

private lemma fin3_bary_eq_point (T : Triangle ℝ ℝ²) {y : ℝ²} {c : Fin 3}
    (h1 : bary T y c = 1) (hnn : ∀ k : Fin 3, 0 ≤ bary T y k) : y = T.points c := by
  have hsum := bary_sum T y
  rw [Fin.sum_univ_three] at hsum
  have h0 : ∀ j : Fin 3, j ≠ c → bary T y j = 0 := by
    intro j hj
    rcases fin3_cases c with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
      first | exact absurd rfl hj | linarith [hnn 0, hnn 1, hnn 2]
  rw [← bary_affineCombination T y,
    Finset.affineCombination_eq_linear_combination _ _ _ (bary_sum T y), Fin.sum_univ_three]
  rcases fin3_cases c with rfl | rfl | rfl
  · rw [h1, h0 1 (by decide), h0 2 (by decide)]; simp
  · rw [h1, h0 0 (by decide), h0 2 (by decide)]; simp
  · rw [h1, h0 0 (by decide), h0 1 (by decide)]; simp

private lemma fin3_vec_decomp (T : Triangle ℝ ℝ²) {j a b : Fin 3}
    (hja : j ≠ a) (hjb : j ≠ b) (hab : a ≠ b) (y : ℝ²) :
    y - T.points j =
      bary T y a • (T.points a - T.points j) + bary T y b • (T.points b - T.points j) := by
  have hsum := bary_sum T y
  have hcomb := bary_affineCombination T y
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum, Fin.sum_univ_three] at hcomb
  rw [Fin.sum_univ_three] at hsum
  conv_lhs => rw [← hcomb]
  have h0eq : bary T y 0 = 1 - bary T y 1 - bary T y 2 := by linarith
  rcases fin3_cases j with rfl | rfl | rfl <;>
  rcases fin3_cases a with rfl | rfl | rfl <;>
  rcases fin3_cases b with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hja
    | exact absurd rfl hjb
    | exact absurd rfl hab
    | (apply ext2 <;> (simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, h0eq]; ring))

private lemma fin3_affine_decomp {V : Type*} [AddCommGroup V] [Module ℝ V] (p : Fin 3 → V)
    {k₀ k₁ k₂ : Fin 3} (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂)
    (w : Fin 3 → ℝ) (hw : ∑ k : Fin 3, w k = 1) :
    ∑ k : Fin 3, w k • p k = (1 - w k₁ - w k₂) • p k₀ + w k₁ • p k₁ + w k₂ • p k₂ := by
  rw [Fin.sum_univ_three] at hw ⊢
  have hk0 : w k₀ = 1 - w k₁ - w k₂ := by
    have hp := fin3_sum_perm w h01 h02 h12
    linarith
  rcases fin3_cases k₀ with rfl | rfl | rfl <;>
  rcases fin3_cases k₁ with rfl | rfl | rfl <;>
  rcases fin3_cases k₂ with rfl | rfl | rfl <;>
    first
    | exact absurd rfl h01
    | exact absurd rfl h02
    | exact absurd rfl h12
    | (rw [hk0]; try abel)

private lemma fin3_img_eq {α : Type*} [DecidableEq α] (f : Fin 3 → α) {k₀ k₁ k₂ : Fin 3}
    (h01 : k₀ ≠ k₁) (h02 : k₀ ≠ k₂) (h12 : k₁ ≠ k₂) :
    Finset.univ.image f = {f k₀, f k₁, f k₂} := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨k, rfl⟩
    have hcases : k = k₀ ∨ k = k₁ ∨ k = k₂ := by
      rcases fin3_cases k₀ with rfl | rfl | rfl <;>
      rcases fin3_cases k₁ with rfl | rfl | rfl <;>
      rcases fin3_cases k₂ with rfl | rfl | rfl <;>
      rcases fin3_cases k with rfl | rfl | rfl <;>
        simp at h01 h02 h12 ⊢
    rcases hcases with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨k₀, rfl⟩
    · exact ⟨k₁, rfl⟩
    · exact ⟨k₂, rfl⟩

private lemma fin3_fun_eq {f g : Fin 3 → ℝ} {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : f a = g a) (hb : f b = g b) (hc : f c = g c) : f = g := by
  ext k
  have hcases : k = a ∨ k = b ∨ k = c := by
    rcases fin3_cases a with rfl | rfl | rfl <;>
    rcases fin3_cases b with rfl | rfl | rfl <;>
    rcases fin3_cases c with rfl | rfl | rfl <;>
    rcases fin3_cases k with rfl | rfl | rfl <;>
      simp at hab hac hbc ⊢
  rcases hcases with rfl | rfl | rfl <;> assumption

private lemma card_filter_pair {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (P : α → Prop) [DecidablePred P] :
    (({a, b} : Finset α).filter P).card = (if P a then 1 else 0) + (if P b then 1 else 0) := by
  by_cases ha : P a <;> by_cases hb : P b <;>
    simp [Finset.filter_insert, Finset.filter_singleton, ha, hb, hab]

private lemma card_filter_triple {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (P : α → Prop) [DecidablePred P] :
    (({a, b, c} : Finset α).filter P).card =
      (if P a then 1 else 0) + (if P b then 1 else 0) + (if P c then 1 else 0) := by
  by_cases ha : P a <;> by_cases hb : P b <;> by_cases hc : P c <;>
    simp [Finset.filter_insert, Finset.filter_singleton, ha, hb, hc, hab, hac, hbc]

private lemma div_pos_iff_neg {a b : ℝ} (hb : b < 0) : 0 < a / b ↔ a < 0 := by
  constructor
  · intro h
    rw [div_pos_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · exact h1
  · intro ha
    exact div_pos_of_neg_of_neg ha hb

private lemma fin3_cross_ne_zero (Δ : Triangle ℝ ℝ²) {a b c : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    cross (Δ.points b - Δ.points a) (Δ.points c - Δ.points a) ≠ 0 := by
  have hD := cross_ne_zero_of_triangle Δ
  intro hcz
  apply hD
  rcases fin3_cases a with rfl | rfl | rfl <;>
  rcases fin3_cases b with rfl | rfl | rfl <;>
  rcases fin3_cases c with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | exact absurd rfl hac
    | exact absurd rfl hbc
    | (simp only [cross, PiLp.sub_apply] at hcz ⊢; first | linear_combination hcz | linear_combination -hcz)

private def edgeVec (Δ : Triangle ℝ ℝ²) : Fin 3 → ℝ²
  | 0 => Δ.points 2 - Δ.points 1
  | 1 => Δ.points 0 - Δ.points 2
  | 2 => Δ.points 1 - Δ.points 0

private lemma edgeVec_ne_zero (Δ : Triangle ℝ ℝ²) (k : Fin 3) : edgeVec Δ k ≠ 0 := by
  fin_cases k <;>
    exact sub_ne_zero.mpr (Δ.independent.injective.ne (by decide))

private noncomputable def baryDir (Δ : Triangle ℝ ℝ²) (u : ℝ²) (k : Fin 3) : ℝ :=
  cross (edgeVec Δ k) u / cross (Δ.points 1 - Δ.points 0) (Δ.points 2 - Δ.points 0)

private lemma bary_add_smul (Δ : Triangle ℝ ℝ²) (p u : ℝ²) (r : ℝ) (k : Fin 3) :
    bary Δ (p + r • u) k = bary Δ p k + r * baryDir Δ u k := by
  have hD := cross_ne_zero_of_triangle Δ
  simp only [cross, PiLp.sub_apply] at hD
  fin_cases k <;>
    (simp only [bary, baryDir, edgeVec, cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul]; field_simp [hD]; ring)

private noncomputable def triAngle (Δ : Triangle ℝ ℝ²) : Fin 3 → ℝ
  | 0 => ∠ (Δ.points 1) (Δ.points 0) (Δ.points 2)
  | 1 => ∠ (Δ.points 2) (Δ.points 1) (Δ.points 0)
  | 2 => ∠ (Δ.points 0) (Δ.points 2) (Δ.points 1)

private lemma triAngle_sum (Δ : Triangle ℝ ℝ²) :
    triAngle Δ 0 + triAngle Δ 1 + triAngle Δ 2 = Real.pi := by
  have hne : Δ.points 1 ≠ Δ.points 0 := Δ.independent.injective.ne (by decide)
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (Δ.points 2) hne
  simp only [triAngle]
  rw [EuclideanGeometry.angle_comm (Δ.points 1) (Δ.points 0) (Δ.points 2),
    EuclideanGeometry.angle_comm (Δ.points 0) (Δ.points 2) (Δ.points 1),
    EuclideanGeometry.angle_comm (Δ.points 2) (Δ.points 1) (Δ.points 0)]
  linarith

private lemma triAngle_pos (Δ : Triangle ℝ ℝ²) (k : Fin 3) : 0 < triAngle Δ k := by
  have hnotcol : ∀ a b c : Fin 3, a ≠ b → b ≠ c → a ≠ c →
      0 < ∠ (Δ.points a) (Δ.points b) (Δ.points c) := by
    intro a b c hab hbc hac
    have hnn : 0 ≤ ∠ (Δ.points a) (Δ.points b) (Δ.points c) := EuclideanGeometry.angle_nonneg _ _ _
    refine lt_of_le_of_ne hnn (Ne.symm ?_)
    intro h0
    have hcol : Collinear ℝ ({Δ.points a, Δ.points b, Δ.points c} : Set ℝ²) := by
      rw [EuclideanGeometry.collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi]
      exact Or.inr (Or.inr (Or.inl h0))
    have hset : ({Δ.points a, Δ.points b, Δ.points c} : Set ℝ²) = Set.range Δ.points := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨a, rfl⟩
        · exact ⟨b, rfl⟩
        · exact ⟨c, rfl⟩
      · rintro ⟨i, rfl⟩
        fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> simp at hab hbc hac ⊢
    rw [hset] at hcol
    have hnot : ¬ Collinear ℝ (Set.range Δ.points) := by
      rw [collinear_iff_of_mem (Set.mem_range_self (0 : Fin 3))]
      intro ⟨v, hv⟩
      have h1 : ∃ r₁ : ℝ, Δ.points 1 = r₁ • v +ᵥ Δ.points 0 := hv (Δ.points 1) (Set.mem_range_self 1)
      have h2 : ∃ r₂ : ℝ, Δ.points 2 = r₂ • v +ᵥ Δ.points 0 := hv (Δ.points 2) (Set.mem_range_self 2)
      rcases h1 with ⟨r₁, hr₁⟩
      rcases h2 with ⟨r₂, hr₂⟩
      have hsub1 : Δ.points 1 - Δ.points 0 = r₁ • v := by
        rw [hr₁, vadd_eq_add, add_sub_cancel_right]
      have hsub2 : Δ.points 2 - Δ.points 0 = r₂ • v := by
        rw [hr₂, vadd_eq_add, add_sub_cancel_right]
      have hcz : cross (Δ.points 1 - Δ.points 0) (Δ.points 2 - Δ.points 0) = 0 := by
        rw [hsub1, hsub2]
        simp only [cross, PiLp.smul_apply, smul_eq_mul]
        ring
      exact cross_ne_zero_of_triangle Δ hcz
    exact hnot hcol
  fin_cases k
  · exact hnotcol 1 0 2 (by decide) (by decide) (by decide)
  · exact hnotcol 2 1 0 (by decide) (by decide) (by decide)
  · exact hnotcol 0 2 1 (by decide) (by decide) (by decide)

private lemma triAngle_lt_pi (Δ : Triangle ℝ ℝ²) (k : Fin 3) : triAngle Δ k < Real.pi := by
  have hsum := triAngle_sum Δ
  have h0 := triAngle_pos Δ 0
  have h1 := triAngle_pos Δ 1
  have h2 := triAngle_pos Δ 2
  match k with
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith

/- Part 3: Constructing a Triangle with `ℤ`-Linearly Independent Angles -/

private lemma exists_angle_indep_triangle :
    ∃ T : Triangle ℝ ℝ²,
      ∀ r s t : ℤ,
        (r : ℝ) * triAngle T 0 + (s : ℝ) * triAngle T 1 + (t : ℝ) * triAngle T 2 = 0 →
        r = 0 ∧ s = 0 ∧ t = 0 := by
  have hIoo_uncount : ¬ (Set.Ioo (0 : ℝ) (Real.pi / 3)).Countable := by
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real (by positivity : (0 : ℝ) < Real.pi / 3)]
    exact not_le_of_gt Cardinal.aleph0_lt_continuum
  let badA : Set ℝ := Set.range (fun q : ℚ => (q : ℝ) * Real.pi)
  have hbadA_count : badA.Countable := Set.countable_range _
  have hdiffA : (Set.Ioo (0 : ℝ) (Real.pi / 3) \ badA).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
    exact hIoo_uncount (hbadA_count.mono hemp)
  rcases hdiffA with ⟨A, ⟨hA0, hAhi⟩, hAnbad⟩
  let badB : Set ℝ := Set.range (fun q : ℚ × ℚ => (q.1 : ℝ) * A + (q.2 : ℝ) * Real.pi)
  have hbadB_count : badB.Countable := Set.countable_range _
  have hdiffB : (Set.Ioo (0 : ℝ) (Real.pi / 3) \ badB).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hemp
    exact hIoo_uncount (hbadB_count.mono hemp)
  rcases hdiffB with ⟨B, ⟨hB0, hBhi⟩, hBnbad⟩
  have hAB_pos : 0 < A + B := by linarith
  have hAB_lt : A + B < Real.pi := by linarith [Real.pi_pos]
  have hsinA : 0 < Real.sin A := Real.sin_pos_of_pos_of_lt_pi hA0 (by linarith [Real.pi_pos])
  have hsinB : 0 < Real.sin B := Real.sin_pos_of_pos_of_lt_pi hB0 (by linarith [Real.pi_pos])
  have hsinAB : 0 < Real.sin (A + B) := Real.sin_pos_of_pos_of_lt_pi hAB_pos hAB_lt
  let s : ℝ := Real.sin B / Real.sin (A + B)
  have hs_pos : 0 < s := div_pos hsinB hsinAB
  let P0 : ℝ² := mk2 0 0
  let P1 : ℝ² := mk2 1 0
  let P2 : ℝ² := mk2 (s * Real.cos A) (s * Real.sin A)
  have hpts_ind : AffineIndependent ℝ ![P0, P1, P2] := by
    rw [affineIndependent_iff_linearIndependent_vsub ℝ ![P0, P1, P2] (0 : Fin 3)]
    rw [Fintype.linearIndependent_iff]
    intro f hf
    have huniv : (Finset.univ : Finset {x : Fin 3 // x ≠ 0}) =
        {⟨1, by decide⟩, ⟨2, by decide⟩} := by
      ext ⟨x, hx⟩
      fin_cases x <;> simp at hx ⊢
    rw [huniv, Finset.sum_pair (by decide)] at hf
    have hc0 := congrArg (fun v : ℝ² => v 0) hf
    have hc1 := congrArg (fun v : ℝ² => v 1) hf
    change f ⟨1, by decide⟩ * (1 - 0) + f ⟨2, by decide⟩ * (s * Real.cos A - 0) = 0 at hc0
    change f ⟨1, by decide⟩ * (0 - 0) + f ⟨2, by decide⟩ * (s * Real.sin A - 0) = 0 at hc1
    have h2 : f ⟨2, by decide⟩ = 0 := by
      have hss : s * Real.sin A ≠ 0 := ne_of_gt (mul_pos hs_pos hsinA)
      have h1' : f ⟨2, by decide⟩ * (s * Real.sin A) = 0 := by linarith
      exact (mul_eq_zero.mp h1').resolve_right hss
    have h1 : f ⟨1, by decide⟩ = 0 := by
      rw [h2] at hc0
      linarith
    intro ⟨x, hx⟩
    fin_cases x
    · exact absurd rfl hx
    · exact h1
    · exact h2
  let T : Triangle ℝ ℝ² := ⟨![P0, P1, P2], hpts_ind⟩
  have hang0 : triAngle T 0 = A := by
    change InnerProductGeometry.angle (P1 - P0) (P2 - P0) = A
    apply Real.injOn_cos ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
      ⟨le_of_lt hA0, by linarith [Real.pi_pos]⟩
    rw [InnerProductGeometry.cos_angle, inner2]
    have hnorm1 : ‖P1 - P0‖ = 1 := by
      have hsq : ‖P1 - P0‖ ^ 2 = 1 := by
        rw [norm_sq2]; simp [P0, P1]
      nlinarith [norm_nonneg (P1 - P0)]
    have hnorm2 : ‖P2 - P0‖ = s := by
      have hsq : ‖P2 - P0‖ ^ 2 = s ^ 2 := by
        rw [norm_sq2]
        simp only [P0, P2, PiLp.sub_apply, mk2_zero, mk2_one, sub_zero]
        have hcs := Real.sin_sq_add_cos_sq A
        nlinarith
      nlinarith [norm_nonneg (P2 - P0)]
    rw [hnorm1, hnorm2]
    simp only [P0, P1, P2, PiLp.sub_apply, mk2_zero, mk2_one, sub_zero, one_mul, zero_mul, add_zero]
    field_simp [ne_of_gt hs_pos]
  have hang1 : triAngle T 1 = B := by
    change InnerProductGeometry.angle (P2 - P1) (P0 - P1) = B
    apply Real.injOn_cos ⟨InnerProductGeometry.angle_nonneg _ _, InnerProductGeometry.angle_le_pi _ _⟩
      ⟨le_of_lt hB0, by linarith [Real.pi_pos]⟩
    rw [InnerProductGeometry.cos_angle, inner2]
    let t : ℝ := Real.sin A / Real.sin (A + B)
    have ht_pos : 0 < t := div_pos hsinA hsinAB
    have hx21 : (P2 - P1) 0 = -(t * Real.cos B) := by
      have hne : Real.sin (A + B) ≠ 0 := ne_of_gt hsinAB
      change s * Real.cos A - 1 = -(t * Real.cos B)
      dsimp only [s, t]
      field_simp [hne]
      rw [Real.sin_add]
      ring
    have hy21 : (P2 - P1) 1 = t * Real.sin B := by
      simp only [P1, P2, PiLp.sub_apply, mk2_one, sub_zero, s, t]
      ring
    have hnorm1 : ‖P0 - P1‖ = 1 := by
      have hsq : ‖P0 - P1‖ ^ 2 = 1 := by
        rw [norm_sq2]; simp [P0, P1]
      nlinarith [norm_nonneg (P0 - P1)]
    have hnorm2 : ‖P2 - P1‖ = t := by
      have hsq : ‖P2 - P1‖ ^ 2 = t ^ 2 := by
        rw [norm_sq2, hx21, hy21]
        have hcs := Real.sin_sq_add_cos_sq B
        nlinarith
      nlinarith [norm_nonneg (P2 - P1)]
    rw [hnorm1, hnorm2, hx21, hy21]
    simp only [P0, P1, PiLp.sub_apply, mk2_zero, mk2_one, zero_sub, sub_self, mul_zero, add_zero]
    field_simp [ne_of_gt ht_pos]
  have hang2 : triAngle T 2 = Real.pi - A - B := by
    have hsum := triAngle_sum T
    linarith
  refine ⟨T, fun r s' t' hlin => ?_⟩
  rw [hang0, hang1, hang2] at hlin
  have h1 : ((r - t' : ℤ) : ℝ) * A + ((s' - t' : ℤ) : ℝ) * B + (t' : ℝ) * Real.pi = 0 := by
    push_cast
    linarith
  have hst : s' - t' = 0 := by
    by_contra hne
    have hneR : ((s' - t' : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hne
    apply hBnbad
    refine ⟨(-((r - t' : ℤ) : ℚ) / ((s' - t' : ℤ) : ℚ), -((t' : ℤ) : ℚ) / ((s' - t' : ℤ) : ℚ)), ?_⟩
    push_cast at h1 hneR ⊢
    field_simp [hneR]
    linarith
  have hst' : s' = t' := sub_eq_zero.mp hst
  subst hst'
  simp only [sub_self, Int.cast_zero, zero_mul, add_zero] at h1
  have hrt : r - s' = 0 := by
    by_contra hne
    have hneR : ((r - s' : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hne
    apply hAnbad
    refine ⟨-((s' : ℤ) : ℚ) / ((r - s' : ℤ) : ℚ), ?_⟩
    push_cast at h1 hneR ⊢
    field_simp [hneR]
    linarith
  have hrt' : r = s' := sub_eq_zero.mp hrt
  subst hrt'
  simp only [sub_self, Int.cast_zero, zero_mul, zero_add] at h1
  have hr0 : (r : ℝ) = 0 := (mul_eq_zero.mp h1).resolve_right (ne_of_gt Real.pi_pos)
  have hr0' : r = 0 := Int.cast_eq_zero.mp hr0
  exact ⟨hr0', hr0', hr0'⟩

/- Part 4: Local Angular Measure and Sum Identity -/

private noncomputable def unitVec (θ : ℝ) : ℝ² := mk2 (Real.cos θ) (Real.sin θ)

private lemma polar_rep {v : ℝ²} (hv : v ≠ 0) :
    ∃ φ : ℝ, v 0 = ‖v‖ * Real.cos φ ∧ v 1 = ‖v‖ * Real.sin φ := by
  let z : ℂ := ⟨v 0, v 1⟩
  have hnorm : ‖z‖ = ‖v‖ := by
    have hsq1 : ‖z‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      dsimp [z]
      ring
    have hsq2 : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := norm_sq2 v
    nlinarith [norm_nonneg z, norm_nonneg v]
  have hz : z ≠ 0 := by
    intro h
    apply hv
    rw [← norm_eq_zero, ← hnorm, h, norm_zero]
  have hzn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨z.arg, ?_, ?_⟩
  · have hc := Complex.cos_arg hz
    change Real.cos z.arg = v 0 / ‖z‖ at hc
    rw [← hnorm, hc]
    field_simp [hzn]
  · have hs := Complex.sin_arg z
    change Real.sin z.arg = v 1 / ‖z‖ at hs
    rw [← hnorm, hs]
    field_simp [hzn]

private lemma cross_unitVec_eq_sin {v : ℝ²} {φ : ℝ}
    (h0 : v 0 = ‖v‖ * Real.cos φ) (h1 : v 1 = ‖v‖ * Real.sin φ) (θ : ℝ) :
    cross v (unitVec θ) = ‖v‖ * Real.sin (θ - φ) := by
  simp only [cross, unitVec, mk2_zero, mk2_one, h0, h1, Real.sin_sub]
  ring

private lemma volume_Ico_periodic {P : ℝ → Prop}
    (hP : ∀ θ, P (θ + 2 * Real.pi) ↔ P θ)
    (hmeas : MeasurableSet {θ : ℝ | P θ}) (a : ℝ) :
    volume {θ ∈ Set.Ico 0 (2 * Real.pi) | P θ} =
      volume {θ ∈ Set.Ico a (a + 2 * Real.pi) | P θ} := by
  have hPz : ∀ k : ℤ, ∀ θ, P (θ + (k : ℝ) * (2 * Real.pi)) ↔ P θ := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · intro θ; simp
    · intro n ih θ
      push_cast
      simp only [Int.cast_natCast] at ih
      have : θ + ((n : ℝ) + 1) * (2 * Real.pi) = (θ + (n : ℝ) * (2 * Real.pi)) + 2 * Real.pi := by
        ring
      rw [this, hP, ih]
    · intro n ih θ
      push_cast
      have : θ + (-(n : ℝ) - 1) * (2 * Real.pi) + 2 * Real.pi =
          θ + (-(n : ℝ)) * (2 * Real.pi) := by ring
      rw [← hP, this]
      simpa using ih θ
  have h2pi : 0 < 2 * Real.pi := by positivity
  let k : ℤ := ⌊a / (2 * Real.pi)⌋
  let b : ℝ := a - (k : ℝ) * (2 * Real.pi)
  have hb0 : 0 ≤ b := by
    dsimp [b, k]
    have hle : (⌊a / (2 * Real.pi)⌋ : ℝ) ≤ a / (2 * Real.pi) := Int.floor_le _
    have := (le_div_iff₀ h2pi).mp hle
    linarith
  have hb1 : b < 2 * Real.pi := by
    dsimp [b, k]
    have hlt : a / (2 * Real.pi) < (⌊a / (2 * Real.pi)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have := (div_lt_iff₀ h2pi).mp hlt
    linarith
  have hshift1 : volume {θ ∈ Set.Ico a (a + 2 * Real.pi) | P θ} =
      volume {θ ∈ Set.Ico b (b + 2 * Real.pi) | P θ} := by
    have hpre : (fun θ : ℝ => ((k : ℝ) * (2 * Real.pi)) + θ) ⁻¹'
        {θ ∈ Set.Ico a (a + 2 * Real.pi) | P θ} =
        {θ ∈ Set.Ico b (b + 2 * Real.pi) | P θ} := by
      ext θ
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩
        refine ⟨⟨by dsimp [b]; linarith, by dsimp [b]; linarith⟩, ?_⟩
        rw [add_comm] at hp
        exact (hPz k θ).mp hp
      · rintro ⟨⟨h1, h2⟩, hp⟩
        refine ⟨⟨by dsimp [b] at h1; linarith, by dsimp [b] at h2; linarith⟩, ?_⟩
        rw [add_comm]
        exact (hPz k θ).mpr hp
    rw [← hpre, MeasureTheory.measure_preimage_add]
  rw [hshift1]
  have hsplit1 : {θ ∈ Set.Ico 0 (2 * Real.pi) | P θ} =
      {θ ∈ Set.Ico 0 b | P θ} ∪ {θ ∈ Set.Ico b (2 * Real.pi) | P θ} := by
    ext θ
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h0, h1⟩, hp⟩
      rcases lt_or_ge θ b with hlt | hge
      · exact Or.inl ⟨⟨h0, hlt⟩, hp⟩
      · exact Or.inr ⟨⟨hge, h1⟩, hp⟩
    · rintro (⟨⟨h0, h1⟩, hp⟩ | ⟨⟨h0, h1⟩, hp⟩)
      · exact ⟨⟨h0, lt_trans h1 hb1⟩, hp⟩
      · exact ⟨⟨le_trans hb0 h0, h1⟩, hp⟩
  have hsplit2 : {θ ∈ Set.Ico b (b + 2 * Real.pi) | P θ} =
      {θ ∈ Set.Ico b (2 * Real.pi) | P θ} ∪ {θ ∈ Set.Ico (2 * Real.pi) (b + 2 * Real.pi) | P θ} := by
    ext θ
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h0, h1⟩, hp⟩
      rcases lt_or_ge θ (2 * Real.pi) with hlt | hge
      · exact Or.inl ⟨⟨h0, hlt⟩, hp⟩
      · exact Or.inr ⟨⟨hge, h1⟩, hp⟩
    · rintro (⟨⟨h0, h1⟩, hp⟩ | ⟨⟨h0, h1⟩, hp⟩)
      · exact ⟨⟨h0, by linarith⟩, hp⟩
      · exact ⟨⟨by linarith, h1⟩, hp⟩
  have hdisj1 : Disjoint {θ ∈ Set.Ico 0 b | P θ} {θ ∈ Set.Ico b (2 * Real.pi) | P θ} := by
    rw [Set.disjoint_left]
    intro θ h1 h2
    linarith [h1.1.2, h2.1.1]
  have hdisj2 : Disjoint {θ ∈ Set.Ico b (2 * Real.pi) | P θ}
      {θ ∈ Set.Ico (2 * Real.pi) (b + 2 * Real.pi) | P θ} := by
    rw [Set.disjoint_left]
    intro θ h1 h2
    linarith [h1.1.2, h2.1.1]
  have hm1 : MeasurableSet {θ ∈ Set.Ico b (2 * Real.pi) | P θ} :=
    measurableSet_Ico.inter hmeas
  have hm2 : MeasurableSet {θ ∈ Set.Ico (2 * Real.pi) (b + 2 * Real.pi) | P θ} :=
    measurableSet_Ico.inter hmeas
  have hshift2 : volume {θ ∈ Set.Ico (2 * Real.pi) (b + 2 * Real.pi) | P θ} =
      volume {θ ∈ Set.Ico 0 b | P θ} := by
    have hpre : (fun θ : ℝ => (2 * Real.pi) + θ) ⁻¹'
        {θ ∈ Set.Ico (2 * Real.pi) (b + 2 * Real.pi) | P θ} =
        {θ ∈ Set.Ico 0 b | P θ} := by
      ext θ
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, hp⟩
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        rw [add_comm] at hp
        exact (hP θ).mp hp
      · rintro ⟨⟨h1, h2⟩, hp⟩
        refine ⟨⟨by linarith, by linarith⟩, ?_⟩
        rw [add_comm]
        exact (hP θ).mpr hp
    rw [← hpre, MeasureTheory.measure_preimage_add]
  rw [hsplit1, hsplit2, measure_union hdisj1 hm1, measure_union hdisj2 hm2, hshift2, add_comm]

private lemma volume_sin_zero (φ : ℝ) :
    volume {θ ∈ Set.Ico 0 (2 * Real.pi) | Real.sin (θ - φ) = 0} = 0 := by
  have hsub : {θ ∈ Set.Ico 0 (2 * Real.pi) | Real.sin (θ - φ) = 0} ⊆
      Set.range (fun k : ℤ => φ + (k : ℝ) * Real.pi) := by
    intro θ hθ
    rcases Real.sin_eq_zero_iff.mp hθ.2 with ⟨k, hk⟩
    exact ⟨k, by linarith⟩
  exact ((Set.countable_range _).mono hsub).measure_zero volume

private lemma volume_sin_pos (φ : ℝ) :
    volume {θ ∈ Set.Ico 0 (2 * Real.pi) | 0 < Real.sin (θ - φ)} = ENNReal.ofReal Real.pi := by
  have hper : ∀ θ, (0 < Real.sin (θ + 2 * Real.pi - φ)) ↔ (0 < Real.sin (θ - φ)) := by
    intro θ
    have : θ + 2 * Real.pi - φ = (θ - φ) + 2 * Real.pi := by ring
    rw [this, Real.sin_add_two_pi]
  have hmeas : MeasurableSet {θ : ℝ | 0 < Real.sin (θ - φ)} :=
    (isOpen_lt continuous_const (Real.continuous_sin.comp (continuous_id.sub continuous_const))).measurableSet
  rw [volume_Ico_periodic hper hmeas φ]
  have heq : {θ ∈ Set.Ico φ (φ + 2 * Real.pi) | 0 < Real.sin (θ - φ)} =
      Set.Ioo φ (φ + Real.pi) := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_Ico, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hpos⟩
      refine ⟨?_, ?_⟩
      · refine lt_of_le_of_ne hlo ?_
        rintro rfl
        simp at hpos
      · by_contra hge
        push Not at hge
        rcases eq_or_lt_of_le hge with rfl | hgt
        · have : φ + Real.pi - φ = Real.pi := by ring
          rw [this, Real.sin_pi] at hpos
          exact lt_irrefl 0 hpos
        · have hsub : θ - φ = (θ - φ - Real.pi) + Real.pi := by ring
          rw [hsub, Real.sin_add_pi] at hpos
          have hsin := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < θ - φ - Real.pi)
            (by linarith : θ - φ - Real.pi < Real.pi)
          linarith
    · rintro ⟨hlo, hhi⟩
      refine ⟨⟨le_of_lt hlo, by linarith [Real.pi_pos]⟩, ?_⟩
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [heq, Real.volume_Ioo, add_sub_cancel_left]

private lemma volume_wedge {e₁ e₂ : ℝ²} (hpos : 0 < cross e₁ e₂) :
    volume {θ ∈ Set.Ico 0 (2 * Real.pi) |
      0 < cross e₁ (unitVec θ) ∧ 0 < cross (unitVec θ) e₂} =
      ENNReal.ofReal (InnerProductGeometry.angle e₁ e₂) := by
  have he1 : e₁ ≠ 0 := by
    intro h; rw [h] at hpos; simp [cross] at hpos
  have he2 : e₂ ≠ 0 := by
    intro h; rw [h] at hpos; simp [cross] at hpos
  have hn1 : 0 < ‖e₁‖ := norm_pos_iff.mpr he1
  have hn2 : 0 < ‖e₂‖ := norm_pos_iff.mpr he2
  obtain ⟨φ₁, h10, h11⟩ := polar_rep he1
  obtain ⟨φ₂, h20, h21⟩ := polar_rep he2
  let α : ℝ := InnerProductGeometry.angle e₁ e₂
  have hα_nn : 0 ≤ α := InnerProductGeometry.angle_nonneg e₁ e₂
  have hα_le : α ≤ Real.pi := InnerProductGeometry.angle_le_pi e₁ e₂
  have hcos : Real.cos α = Real.cos (φ₂ - φ₁) := by
    dsimp [α]
    rw [InnerProductGeometry.cos_angle, inner2, h10, h11, h20, h21, Real.cos_sub]
    field_simp [ne_of_gt hn1, ne_of_gt hn2]
  have hsin_pos : 0 < Real.sin (φ₂ - φ₁) := by
    have hcr : cross e₁ e₂ = ‖e₁‖ * ‖e₂‖ * Real.sin (φ₂ - φ₁) := by
      simp only [cross, h10, h11, h20, h21, Real.sin_sub]
      ring
    nlinarith [mul_pos hn1 hn2]
  have hsin_eq : Real.sin α = Real.sin (φ₂ - φ₁) := by
    have hsq1 := Real.sin_sq_add_cos_sq α
    have hsq2 := Real.sin_sq_add_cos_sq (φ₂ - φ₁)
    have hnn := Real.sin_nonneg_of_nonneg_of_le_pi hα_nn hα_le
    rw [hcos] at hsq1
    nlinarith
  have hα_pos : 0 < α := by
    refine lt_of_le_of_ne hα_nn ?_
    intro h
    rw [← h, Real.sin_zero] at hsin_eq
    linarith
  have hα_lt : α < Real.pi := by
    refine lt_of_le_of_ne hα_le ?_
    intro h
    rw [h, Real.sin_pi] at hsin_eq
    linarith
  have h20' : e₂ 0 = ‖e₂‖ * Real.cos (φ₁ + α) := by
    rw [h20]
    congr 1
    rw [Real.cos_add, hcos, hsin_eq, ← Real.cos_add]
    ring_nf
  have h21' : e₂ 1 = ‖e₂‖ * Real.sin (φ₁ + α) := by
    rw [h21]
    congr 1
    rw [Real.sin_add, hcos, hsin_eq, ← Real.sin_add]
    ring_nf
  have hset : {θ ∈ Set.Ico 0 (2 * Real.pi) |
      0 < cross e₁ (unitVec θ) ∧ 0 < cross (unitVec θ) e₂} =
      {θ ∈ Set.Ico 0 (2 * Real.pi) |
        0 < Real.sin (θ - φ₁) ∧ 0 < Real.sin (φ₁ + α - θ)} := by
    ext θ
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun _ => and_congr ?_ ?_
    · rw [cross_unitVec_eq_sin h10 h11]
      exact mul_pos_iff_of_pos_left hn1
    · have hcr2 : cross (unitVec θ) e₂ = ‖e₂‖ * Real.sin (φ₁ + α - θ) := by
        have hswap : cross (unitVec θ) e₂ = -cross e₂ (unitVec θ) := by simp [cross]; ring
        rw [hswap, cross_unitVec_eq_sin h20' h21']
        have : φ₁ + α - θ = -(θ - (φ₁ + α)) := by ring
        rw [this, Real.sin_neg]
        ring
      rw [hcr2]
      exact mul_pos_iff_of_pos_left hn2
  rw [hset]
  have hper : ∀ θ,
      (0 < Real.sin (θ + 2 * Real.pi - φ₁) ∧ 0 < Real.sin (φ₁ + α - (θ + 2 * Real.pi))) ↔
      (0 < Real.sin (θ - φ₁) ∧ 0 < Real.sin (φ₁ + α - θ)) := by
    intro θ
    have h1 : θ + 2 * Real.pi - φ₁ = (θ - φ₁) + 2 * Real.pi := by ring
    have h2 : φ₁ + α - (θ + 2 * Real.pi) = (φ₁ + α - θ) - 2 * Real.pi := by ring
    rw [h1, h2, Real.sin_add_two_pi, Real.sin_sub_two_pi]
  have hmeas : MeasurableSet {θ : ℝ | 0 < Real.sin (θ - φ₁) ∧ 0 < Real.sin (φ₁ + α - θ)} :=
    ((isOpen_lt continuous_const (Real.continuous_sin.comp (continuous_id.sub continuous_const))).inter
      (isOpen_lt continuous_const (Real.continuous_sin.comp (continuous_const.sub continuous_id)))).measurableSet
  rw [volume_Ico_periodic hper hmeas φ₁]
  have heq : {θ ∈ Set.Ico φ₁ (φ₁ + 2 * Real.pi) |
      0 < Real.sin (θ - φ₁) ∧ 0 < Real.sin (φ₁ + α - θ)} = Set.Ioo φ₁ (φ₁ + α) := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_Ico, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hs1, hs2⟩
      have hgt : φ₁ < θ := by
        refine lt_of_le_of_ne hlo ?_
        rintro rfl
        simp at hs1
      have hltpi : θ < φ₁ + Real.pi := by
        by_contra hge
        push Not at hge
        rcases eq_or_lt_of_le hge with rfl | hgt'
        · have : φ₁ + Real.pi - φ₁ = Real.pi := by ring
          rw [this, Real.sin_pi] at hs1
          exact lt_irrefl 0 hs1
        · have hsub : θ - φ₁ = (θ - φ₁ - Real.pi) + Real.pi := by ring
          rw [hsub, Real.sin_add_pi] at hs1
          have hsp := Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < θ - φ₁ - Real.pi)
            (by linarith : θ - φ₁ - Real.pi < Real.pi)
          linarith
      refine ⟨hgt, ?_⟩
      by_contra hge
      push Not at hge
      rcases eq_or_lt_of_le hge with rfl | hgt'
      · have : φ₁ + α - (φ₁ + α) = 0 := by ring
        rw [this, Real.sin_zero] at hs2
        exact lt_irrefl 0 hs2
      · have hsn := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith : φ₁ + α - θ < 0)
          (by linarith : -Real.pi < φ₁ + α - θ)
        linarith
    · rintro ⟨hlo, hhi⟩
      refine ⟨⟨le_of_lt hlo, by linarith [Real.pi_pos]⟩, ?_, ?_⟩
      · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      · exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [heq, Real.volume_Ioo, add_sub_cancel_left]

private noncomputable def localAngle (Δ : Triangle ℝ ℝ²) (p : ℝ²) : ℝ :=
  if p ∉ Δ.closedInterior then 0
  else if p ∈ Δ.interior then 2 * Real.pi
  else if p = Δ.points 0 then triAngle Δ 0
  else if p = Δ.points 1 then triAngle Δ 1
  else if p = Δ.points 2 then triAngle Δ 2
  else Real.pi

private lemma localAngle_nonneg (Δ : Triangle ℝ ℝ²) (p : ℝ²) : 0 ≤ localAngle Δ p := by
  unfold localAngle
  split_ifs <;>
    first
    | exact le_refl 0
    | positivity
    | exact le_of_lt (triAngle_pos Δ _)

private def closedArc (Δ : Triangle ℝ ℝ²) (p : ℝ²) (r : ℝ) : Set ℝ :=
  {θ ∈ Set.Ico 0 (2 * Real.pi) | p + r • unitVec θ ∈ Δ.closedInterior}

private def openArc (Δ : Triangle ℝ ℝ²) (p : ℝ²) (r : ℝ) : Set ℝ :=
  {θ ∈ Set.Ico 0 (2 * Real.pi) | p + r • unitVec θ ∈ Δ.interior}

private lemma exists_radius_arc (Δ : Triangle ℝ ℝ²) (p : ℝ²) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
      closedArc Δ p r =ᵐ[volume] openArc Δ p r ∧
      MeasurableSet (openArc Δ p r) ∧
      volume (openArc Δ p r) = ENNReal.ofReal (localAngle Δ p) := by
  have hD := cross_ne_zero_of_triangle Δ
  let D : ℝ := cross (Δ.points 1 - Δ.points 0) (Δ.points 2 - Δ.points 0)
  let M : ℝ := 1 +
    ((|edgeVec Δ 0 0| + |edgeVec Δ 0 1|) + (|edgeVec Δ 1 0| + |edgeVec Δ 1 1|) +
      (|edgeVec Δ 2 0| + |edgeVec Δ 2 1|)) / |D|
  have hM_pos : 0 < M := by
    have hDabs : 0 < |D| := abs_pos.mpr hD
    have hnum : 0 ≤ (|edgeVec Δ 0 0| + |edgeVec Δ 0 1|) + (|edgeVec Δ 1 0| + |edgeVec Δ 1 1|) +
        (|edgeVec Δ 2 0| + |edgeVec Δ 2 1|) := by positivity
    have := div_nonneg hnum (le_of_lt hDabs)
    linarith
  have hbaryDir_bound : ∀ (k : Fin 3) (θ : ℝ), |baryDir Δ (unitVec θ) k| ≤ M := by
    intro k θ
    have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have hsin : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hcr : |cross (edgeVec Δ k) (unitVec θ)| ≤ |edgeVec Δ k 0| + |edgeVec Δ k 1| := by
      simp only [cross, unitVec, mk2_zero, mk2_one]
      calc |edgeVec Δ k 0 * Real.sin θ - edgeVec Δ k 1 * Real.cos θ|
          ≤ |edgeVec Δ k 0 * Real.sin θ| + |edgeVec Δ k 1 * Real.cos θ| := abs_sub _ _
        _ = |edgeVec Δ k 0| * |Real.sin θ| + |edgeVec Δ k 1| * |Real.cos θ| := by
            rw [abs_mul, abs_mul]
        _ ≤ |edgeVec Δ k 0| * 1 + |edgeVec Δ k 1| * 1 := by
            gcongr
        _ = |edgeVec Δ k 0| + |edgeVec Δ k 1| := by ring
    have hdiv : |baryDir Δ (unitVec θ) k| ≤ (|edgeVec Δ k 0| + |edgeVec Δ k 1|) / |D| := by
      dsimp only [baryDir, D]
      rw [abs_div]
      exact div_le_div_of_nonneg_right hcr (abs_nonneg D)
    have hle : (|edgeVec Δ k 0| + |edgeVec Δ k 1|) / |D| ≤ M := by
      dsimp only [M]
      have hDabs : 0 < |D| := abs_pos.mpr hD
      have hsub : |edgeVec Δ k 0| + |edgeVec Δ k 1| ≤
          (|edgeVec Δ 0 0| + |edgeVec Δ 0 1|) + (|edgeVec Δ 1 0| + |edgeVec Δ 1 1|) +
          (|edgeVec Δ 2 0| + |edgeVec Δ 2 1|) := by
        match k with
        | 0 => linarith [abs_nonneg (edgeVec Δ 0 0), abs_nonneg (edgeVec Δ 0 1),
            abs_nonneg (edgeVec Δ 1 0), abs_nonneg (edgeVec Δ 1 1),
            abs_nonneg (edgeVec Δ 2 0), abs_nonneg (edgeVec Δ 2 1)]
        | 1 => linarith [abs_nonneg (edgeVec Δ 0 0), abs_nonneg (edgeVec Δ 0 1),
            abs_nonneg (edgeVec Δ 1 0), abs_nonneg (edgeVec Δ 1 1),
            abs_nonneg (edgeVec Δ 2 0), abs_nonneg (edgeVec Δ 2 1)]
        | 2 => linarith [abs_nonneg (edgeVec Δ 0 0), abs_nonneg (edgeVec Δ 0 1),
            abs_nonneg (edgeVec Δ 1 0), abs_nonneg (edgeVec Δ 1 1),
            abs_nonneg (edgeVec Δ 2 0), abs_nonneg (edgeVec Δ 2 1)]
      have := div_le_div_of_nonneg_right hsub (le_of_lt hDabs)
      linarith
    exact le_trans hdiv hle
  have hae_diff : ∀ r > 0, closedArc Δ p r =ᵐ[volume] openArc Δ p r := by
    intro r hr
    have hsub_open : openArc Δ p r ⊆ closedArc Δ p r := fun θ hθ =>
      ⟨hθ.1, Δ.interior_subset_closedInterior hθ.2⟩
    have hdiff_zero : volume (closedArc Δ p r \ openArc Δ p r) = 0 := by
      have hsub : closedArc Δ p r \ openArc Δ p r ⊆
          ⋃ k : Fin 3, {θ ∈ Set.Ico 0 (2 * Real.pi) | bary Δ p k + r * baryDir Δ (unitVec θ) k = 0} := by
        intro θ ⟨hc, ho⟩
        simp only [closedArc, openArc, Set.mem_ofPred_eq, mem_closedInterior_iff_bary,
          mem_interior_iff_bary] at hc ho
        have hnotall : ¬ ∀ k : Fin 3, 0 < bary Δ (p + r • unitVec θ) k := fun h => ho ⟨hc.1, h⟩
        push Not at hnotall
        rcases hnotall with ⟨k, hk⟩
        refine Set.mem_iUnion.mpr ⟨k, hc.1, ?_⟩
        have hnn := hc.2 k
        rw [bary_add_smul] at hnn hk
        linarith
      refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
      obtain ⟨φ, hφ0, hφ1⟩ := polar_rep (edgeVec_ne_zero Δ k)
      have hnorm_pos : 0 < ‖edgeVec Δ k‖ := norm_pos_iff.mpr (edgeVec_ne_zero Δ k)
      have hval_ne : r * (‖edgeVec Δ k‖ / D) ≠ 0 :=
        mul_ne_zero (ne_of_gt hr) (div_ne_zero (ne_of_gt hnorm_pos) hD)
      let c : ℝ := -(bary Δ p k) / (r * (‖edgeVec Δ k‖ / D))
      have hsubk : {θ ∈ Set.Ico 0 (2 * Real.pi) | bary Δ p k + r * baryDir Δ (unitVec θ) k = 0} ⊆
          {θ : ℝ | Real.sin (θ - φ) = c} := by
        intro θ hθ
        have heq := hθ.2
        dsimp only [baryDir, D] at heq
        rw [cross_unitVec_eq_sin hφ0 hφ1] at heq
        change Real.sin (θ - φ) = c
        dsimp only [c]
        have heq' : r * (‖edgeVec Δ k‖ / D) * Real.sin (θ - φ) = -bary Δ p k := by
          have : r * (‖edgeVec Δ k‖ * Real.sin (θ - φ) / D) =
              r * (‖edgeVec Δ k‖ / D) * Real.sin (θ - φ) := by ring
          linarith
        exact (eq_div_iff hval_ne).mpr (by linarith)
      have hcount : ({θ : ℝ | Real.sin (θ - φ) = c}).Countable := by
        have hsin_pre : {θ : ℝ | Real.sin (θ - φ) = c} ⊆
            (Set.range (fun m : ℤ => φ + Real.arcsin c + (m : ℝ) * (2 * Real.pi))) ∪
            (Set.range (fun m : ℤ => φ + Real.pi - Real.arcsin c + (m : ℝ) * (2 * Real.pi))) := by
          intro θ hθ
          have hc1 : |c| ≤ 1 := by
            rw [← hθ]
            exact Real.abs_sin_le_one _
          have hsin_eq : Real.sin (Real.arcsin c) = Real.sin (θ - φ) := by
            rw [hθ, Real.sin_arcsin (neg_le_of_abs_le hc1) (le_of_abs_le hc1)]
          rw [Real.sin_eq_sin_iff] at hsin_eq
          rcases hsin_eq with ⟨m, hm | hm⟩
          · left; exact ⟨m, by linear_combination -hm⟩
          · right; exact ⟨m, by linear_combination -hm⟩
        exact ((Set.countable_range _).union (Set.countable_range _)).mono hsin_pre
      exact (hcount.mono hsubk).measure_zero volume
    exact MeasureTheory.ae_eq_set.mpr ⟨hdiff_zero, by
      rw [Set.sdiff_eq_empty.mpr hsub_open, measure_empty]⟩
  have hmeas_open : ∀ r : ℝ, MeasurableSet (openArc Δ p r) := by
    intro r
    have heq : openArc Δ p r = Set.Ico 0 (2 * Real.pi) ∩
        ⋂ k : Fin 3, {θ : ℝ | 0 < bary Δ p k + r * baryDir Δ (unitVec θ) k} := by
      ext θ
      simp only [openArc, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
        mem_interior_iff_bary, bary_add_smul]
    rw [heq]
    refine measurableSet_Ico.inter (MeasurableSet.iInter fun k => ?_)
    have hcont : Continuous (fun θ : ℝ => bary Δ p k + r * baryDir Δ (unitVec θ) k) := by
      dsimp only [baryDir, cross, unitVec, mk2_zero, mk2_one]
      fun_prop
    exact (isOpen_lt continuous_const hcont).measurableSet
  by_cases hnot : p ∉ Δ.closedInterior
  · have hnot' := hnot
    rw [mem_closedInterior_iff_bary] at hnot'
    push Not at hnot'
    rcases hnot' with ⟨k, hk⟩
    refine ⟨(-bary Δ p k) / M, div_pos (neg_pos.mpr hk) hM_pos, fun r hr hlt => ?_⟩
    refine ⟨hae_diff r hr, hmeas_open r, ?_⟩
    have hemp : openArc Δ p r = ∅ := by
      ext θ
      simp only [openArc, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
        mem_interior_iff_bary]
      intro _ hall
      have hpos := hall k
      rw [bary_add_smul] at hpos
      have hbd := hbaryDir_bound k θ
      have hmul : r * baryDir Δ (unitVec θ) k ≤ r * M :=
        mul_le_mul_of_nonneg_left (le_of_abs_le hbd) (le_of_lt hr)
      have hrM : r * M < -bary Δ p k := (lt_div_iff₀ hM_pos).mp hlt
      linarith
    rw [hemp, measure_empty]
    simp [localAngle, hnot]
  · push Not at hnot
    by_cases hint : p ∈ Δ.interior
    · rw [mem_interior_iff_bary] at hint
      let m := min (bary Δ p 0) (min (bary Δ p 1) (bary Δ p 2))
      have hm_pos : 0 < m := lt_min (hint 0) (lt_min (hint 1) (hint 2))
      refine ⟨m / M, div_pos hm_pos hM_pos, fun r hr hlt => ?_⟩
      refine ⟨hae_diff r hr, hmeas_open r, ?_⟩
      have hfull : openArc Δ p r = Set.Ico 0 (2 * Real.pi) := by
        ext θ
        simp only [openArc, Set.mem_ofPred_eq, and_iff_left_iff_imp, mem_interior_iff_bary]
        intro _ k
        rw [bary_add_smul]
        have hkm : m ≤ bary Δ p k := by
          fin_cases k
          · exact min_le_left _ _
          · exact le_trans (min_le_right _ _) (min_le_left _ _)
          · exact le_trans (min_le_right _ _) (min_le_right _ _)
        have hbd := hbaryDir_bound k θ
        have hmul : -(r * M) ≤ r * baryDir Δ (unitVec θ) k := by
          have := neg_le_of_abs_le hbd
          nlinarith
        have hrM : r * M < m := (lt_div_iff₀ hM_pos).mp hlt
        linarith
      rw [hfull, Real.volume_Ico, sub_zero]
      have hint' : p ∈ Δ.interior := (mem_interior_iff_bary Δ p).mpr hint
      simp [localAngle, hnot, hint']
    · have hnn : ∀ k : Fin 3, 0 ≤ bary Δ p k := (mem_closedInterior_iff_bary Δ p).mp hnot
      have hsum1 := bary_sum Δ p
      rw [Fin.sum_univ_three] at hsum1
      have hpt_iff : ∀ k : Fin 3, p = Δ.points k ↔ bary Δ p k = 1 := by
        intro k
        constructor
        · rintro rfl; simp [bary_point]
        · intro h1
          have h0 : ∀ j : Fin 3, j ≠ k → bary Δ p j = 0 := by
            intro j hj
            match k, j with
            | 0, 0 => exact absurd rfl hj
            | 0, 1 => linarith [hnn 0, hnn 1, hnn 2]
            | 0, 2 => linarith [hnn 0, hnn 1, hnn 2]
            | 1, 0 => linarith [hnn 0, hnn 1, hnn 2]
            | 1, 1 => exact absurd rfl hj
            | 1, 2 => linarith [hnn 0, hnn 1, hnn 2]
            | 2, 0 => linarith [hnn 0, hnn 1, hnn 2]
            | 2, 1 => linarith [hnn 0, hnn 1, hnn 2]
            | 2, 2 => exact absurd rfl hj
          rw [← bary_affineCombination Δ p,
            Finset.affineCombination_eq_linear_combination _ _ _ (bary_sum Δ p), Fin.sum_univ_three]
          match k with
          | 0 => rw [h1, h0 1 (by decide), h0 2 (by decide)]; simp
          | 1 => rw [h1, h0 0 (by decide), h0 2 (by decide)]; simp
          | 2 => rw [h1, h0 0 (by decide), h0 1 (by decide)]; simp
      have hvertex_case : ∀ (k₀ k₁ k₂ : Fin 3),
          k₀ ≠ k₁ → k₁ ≠ k₂ → k₀ ≠ k₂ → p = Δ.points k₀ →
          ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ →
            closedArc Δ p r =ᵐ[volume] openArc Δ p r ∧
            MeasurableSet (openArc Δ p r) ∧
            volume (openArc Δ p r) = ENNReal.ofReal (triAngle Δ k₀) := by
        intro k₀ k₁ k₂ h01 h12 h02 hp
        refine ⟨1 / M, div_pos one_pos hM_pos, fun r hr hlt => ?_⟩
        refine ⟨hae_diff r hr, hmeas_open r, ?_⟩
        have hb0 : bary Δ p k₀ = 1 := (hpt_iff k₀).mp hp
        have hb1 : bary Δ p k₁ = 0 := by rw [hp, bary_point]; simp [h01.symm]
        have hb2 : bary Δ p k₂ = 0 := by rw [hp, bary_point]; simp [h02.symm]
        have hopen_eq : openArc Δ p r =
            {θ ∈ Set.Ico 0 (2 * Real.pi) |
              0 < baryDir Δ (unitVec θ) k₁ ∧ 0 < baryDir Δ (unitVec θ) k₂} := by
          ext θ
          simp only [openArc, Set.mem_ofPred_eq, mem_interior_iff_bary, bary_add_smul]
          refine and_congr_right fun _ => ?_
          constructor
          · intro hall
            have h1 := hall k₁
            have h2 := hall k₂
            rw [hb1, zero_add] at h1
            rw [hb2, zero_add] at h2
            exact ⟨(mul_pos_iff_of_pos_left hr).mp h1, (mul_pos_iff_of_pos_left hr).mp h2⟩
          · rintro ⟨h1, h2⟩ k
            have hcases : k = k₀ ∨ k = k₁ ∨ k = k₂ := by
              fin_cases k₀ <;> fin_cases k₁ <;> fin_cases k₂ <;> fin_cases k <;>
                simp at h01 h12 h02 ⊢
            rcases hcases with rfl | rfl | rfl
            · rw [hb0]
              have hbd := hbaryDir_bound k θ
              have hrM : r * M < 1 := (lt_div_iff₀ hM_pos).mp hlt
              have hneg := neg_le_of_abs_le hbd
              have hmul : -(r * M) ≤ r * baryDir Δ (unitVec θ) k := by nlinarith
              linarith
            · rw [hb1, zero_add]; exact mul_pos hr h1
            · rw [hb2, zero_add]; exact mul_pos hr h2
        rw [hopen_eq]
        have hwedge_all : ∀ (u₁ u₂ : ℝ²),
            (cross u₁ u₂ = D ∧
              (∀ θ, (0 < baryDir Δ (unitVec θ) k₁ ∧ 0 < baryDir Δ (unitVec θ) k₂) ↔
                (0 < cross u₁ (unitVec θ) / D ∧ 0 < cross (unitVec θ) u₂ / D))) →
            InnerProductGeometry.angle u₁ u₂ = triAngle Δ k₀ →
            volume {θ ∈ Set.Ico 0 (2 * Real.pi) |
              0 < baryDir Δ (unitVec θ) k₁ ∧ 0 < baryDir Δ (unitVec θ) k₂} =
              ENNReal.ofReal (triAngle Δ k₀) := by
          intro u₁ u₂ ⟨hcrD, hiff⟩ hang
          rcases lt_or_gt_of_ne hD with hDneg | hDpos
          · have hcr_pos : 0 < cross u₂ u₁ := by
              have : cross u₂ u₁ = -cross u₁ u₂ := by simp [cross]; ring
              linarith
            have hset' : {θ ∈ Set.Ico 0 (2 * Real.pi) |
                0 < baryDir Δ (unitVec θ) k₁ ∧ 0 < baryDir Δ (unitVec θ) k₂} =
                {θ ∈ Set.Ico 0 (2 * Real.pi) |
                  0 < cross u₂ (unitVec θ) ∧ 0 < cross (unitVec θ) u₁} := by
              ext θ
              simp only [Set.mem_ofPred_eq]
              refine and_congr_right fun _ => ?_
              rw [hiff]
              have h1 : 0 < cross u₁ (unitVec θ) / D ↔ 0 < cross (unitVec θ) u₁ := by
                rw [div_pos_iff_neg hDneg]
                have : cross (unitVec θ) u₁ = -cross u₁ (unitVec θ) := by simp [cross]; ring
                constructor <;> intro h <;> linarith
              have h2 : 0 < cross (unitVec θ) u₂ / D ↔ 0 < cross u₂ (unitVec θ) := by
                rw [div_pos_iff_neg hDneg]
                have : cross u₂ (unitVec θ) = -cross (unitVec θ) u₂ := by simp [cross]; ring
                constructor <;> intro h <;> linarith
              rw [h1, h2, and_comm]
            rw [hset', volume_wedge hcr_pos, InnerProductGeometry.angle_comm, hang]
          · have hcr_pos : 0 < cross u₁ u₂ := hcrD.symm ▸ hDpos
            have hset' : {θ ∈ Set.Ico 0 (2 * Real.pi) |
                0 < baryDir Δ (unitVec θ) k₁ ∧ 0 < baryDir Δ (unitVec θ) k₂} =
                {θ ∈ Set.Ico 0 (2 * Real.pi) |
                  0 < cross u₁ (unitVec θ) ∧ 0 < cross (unitVec θ) u₂} := by
              ext θ
              simp only [Set.mem_ofPred_eq]
              refine and_congr_right fun _ => ?_
              rw [hiff, div_pos_iff_of_pos_right hDpos, div_pos_iff_of_pos_right hDpos]
            rw [hset', volume_wedge hcr_pos, hang]
        fin_cases k₀
        · refine hwedge_all (Δ.points 1 - Δ.points 0) (Δ.points 2 - Δ.points 0) ⟨rfl, fun θ => ?_⟩ rfl
          fin_cases k₁ <;> fin_cases k₂ <;> simp at h01 h12 h02 ⊢
          · rw [and_comm]
            refine and_congr ?_ ?_
            · rfl
            · have : cross (edgeVec Δ 1) (unitVec θ) = cross (unitVec θ) (Δ.points 2 - Δ.points 0) := by
                simp [edgeVec, cross]; ring
              dsimp [baryDir, D]; rw [this]
          · refine and_congr ?_ ?_
            · rfl
            · have : cross (edgeVec Δ 1) (unitVec θ) = cross (unitVec θ) (Δ.points 2 - Δ.points 0) := by
                simp [edgeVec, cross]; ring
              dsimp [baryDir, D]; rw [this]
        · refine hwedge_all (Δ.points 2 - Δ.points 1) (Δ.points 0 - Δ.points 1) ⟨?_, fun θ => ?_⟩ rfl
          · simp only [D, cross, PiLp.sub_apply]; ring
          · fin_cases k₁ <;> fin_cases k₂ <;> simp at h01 h12 h02 ⊢
            · refine and_congr ?_ ?_
              · rfl
              · have : cross (edgeVec Δ 2) (unitVec θ) = cross (unitVec θ) (Δ.points 0 - Δ.points 1) := by
                  simp [edgeVec, cross]; ring
                dsimp [baryDir, D]; rw [this]
            · rw [and_comm]
              refine and_congr ?_ ?_
              · rfl
              · have : cross (edgeVec Δ 2) (unitVec θ) = cross (unitVec θ) (Δ.points 0 - Δ.points 1) := by
                  simp [edgeVec, cross]; ring
                dsimp [baryDir, D]; rw [this]
        · refine hwedge_all (Δ.points 0 - Δ.points 2) (Δ.points 1 - Δ.points 2) ⟨?_, fun θ => ?_⟩ rfl
          · simp only [D, cross, PiLp.sub_apply]; ring
          · fin_cases k₁ <;> fin_cases k₂ <;> simp at h01 h12 h02 ⊢
            · rw [and_comm]
              refine and_congr ?_ ?_
              · rfl
              · have : cross (edgeVec Δ 0) (unitVec θ) = cross (unitVec θ) (Δ.points 1 - Δ.points 2) := by
                  simp [edgeVec, cross]; ring
                dsimp [baryDir, D]; rw [this]
            · refine and_congr ?_ ?_
              · rfl
              · have : cross (edgeVec Δ 0) (unitVec θ) = cross (unitVec θ) (Δ.points 1 - Δ.points 2) := by
                  simp [edgeVec, cross]; ring
                dsimp [baryDir, D]; rw [this]
      by_cases hp0 : p = Δ.points 0
      · obtain ⟨r₀, hr₀, h⟩ := hvertex_case 0 1 2 (by decide) (by decide) (by decide) hp0
        have hloc : localAngle Δ p = triAngle Δ 0 := by
          unfold localAngle; rw [if_neg (not_not.mpr hnot), if_neg hint, if_pos hp0]
        refine ⟨r₀, hr₀, fun r hr hlt => ?_⟩
        rw [hloc]; exact h r hr hlt
      · by_cases hp1 : p = Δ.points 1
        · obtain ⟨r₀, hr₀, h⟩ := hvertex_case 1 2 0 (by decide) (by decide) (by decide) hp1
          have hloc : localAngle Δ p = triAngle Δ 1 := by
            unfold localAngle; rw [if_neg (not_not.mpr hnot), if_neg hint, if_neg hp0, if_pos hp1]
          refine ⟨r₀, hr₀, fun r hr hlt => ?_⟩
          rw [hloc]; exact h r hr hlt
        · by_cases hp2 : p = Δ.points 2
          · obtain ⟨r₀, hr₀, h⟩ := hvertex_case 2 0 1 (by decide) (by decide) (by decide) hp2
            have hloc : localAngle Δ p = triAngle Δ 2 := by
              unfold localAngle
              rw [if_neg (not_not.mpr hnot), if_neg hint, if_neg hp0, if_neg hp1, if_pos hp2]
            refine ⟨r₀, hr₀, fun r hr hlt => ?_⟩
            rw [hloc]; exact h r hr hlt
          · have hlt1 : ∀ k : Fin 3, bary Δ p k < 1 := by
              intro k
              have hle : bary Δ p k ≤ 1 := by
                match k with
                | 0 => linarith [hnn 0, hnn 1, hnn 2]
                | 1 => linarith [hnn 0, hnn 1, hnn 2]
                | 2 => linarith [hnn 0, hnn 1, hnn 2]
              refine lt_of_le_of_ne hle fun h1 => ?_
              have hp := (hpt_iff k).mpr h1
              match k with
              | 0 => exact hp0 hp
              | 1 => exact hp1 hp
              | 2 => exact hp2 hp
            have hex0 : ∃ k₀ : Fin 3, bary Δ p k₀ = 0 := by
              by_contra hall
              push Not at hall
              apply hint
              rw [mem_interior_iff_bary]
              exact fun k => lt_of_le_of_ne (hnn k) (Ne.symm (hall k))
            rcases hex0 with ⟨k₀, hk₀⟩
            have hother_pos : ∀ k : Fin 3, k ≠ k₀ → 0 < bary Δ p k := by
              intro k hk
              refine lt_of_le_of_ne (hnn k) ?_
              intro h0
              have hthird : ∃ k' : Fin 3, k' ≠ k₀ ∧ k' ≠ k := by
                rcases fin3_cases k₀ with rfl | rfl | rfl <;> rcases fin3_cases k with rfl | rfl | rfl
                · exact absurd rfl hk
                · exact ⟨2, by decide, by decide⟩
                · exact ⟨1, by decide, by decide⟩
                · exact ⟨2, by decide, by decide⟩
                · exact absurd rfl hk
                · exact ⟨0, by decide, by decide⟩
                · exact ⟨1, by decide, by decide⟩
                · exact ⟨0, by decide, by decide⟩
                · exact absurd rfl hk
              rcases hthird with ⟨k', hk'0, hk'k⟩
              have hperm := fin3_sum_perm (bary Δ p) hk.symm hk'0.symm hk'k.symm
              have h1 : bary Δ p k' = 1 := by linarith
              exact absurd h1 (ne_of_lt (hlt1 k'))
            have hother_min : ∃ m > 0, ∀ k : Fin 3, k ≠ k₀ → m ≤ bary Δ p k := by
              fin_cases k₀
              · refine ⟨min (bary Δ p 1) (bary Δ p 2),
                  lt_min (hother_pos 1 (by decide)) (hother_pos 2 (by decide)), fun k hk => ?_⟩
                fin_cases k
                · exact absurd rfl hk
                · exact min_le_left _ _
                · exact min_le_right _ _
              · refine ⟨min (bary Δ p 0) (bary Δ p 2),
                  lt_min (hother_pos 0 (by decide)) (hother_pos 2 (by decide)), fun k hk => ?_⟩
                fin_cases k
                · exact min_le_left _ _
                · exact absurd rfl hk
                · exact min_le_right _ _
              · refine ⟨min (bary Δ p 0) (bary Δ p 1),
                  lt_min (hother_pos 0 (by decide)) (hother_pos 1 (by decide)), fun k hk => ?_⟩
                fin_cases k
                · exact min_le_left _ _
                · exact min_le_right _ _
                · exact absurd rfl hk
            rcases hother_min with ⟨m, hm_pos, hm_le⟩
            refine ⟨m / M, div_pos hm_pos hM_pos, fun r hr hlt => ?_⟩
            refine ⟨hae_diff r hr, hmeas_open r, ?_⟩
            have hopen_eq : openArc Δ p r =
                {θ ∈ Set.Ico 0 (2 * Real.pi) | 0 < baryDir Δ (unitVec θ) k₀} := by
              ext θ
              simp only [openArc, Set.mem_ofPred_eq, mem_interior_iff_bary, bary_add_smul]
              refine and_congr_right fun _ => ?_
              constructor
              · intro hall
                have h0 := hall k₀
                rw [hk₀, zero_add] at h0
                exact (mul_pos_iff_of_pos_left hr).mp h0
              · intro hpos k
                by_cases hk : k = k₀
                · subst hk; rw [hk₀, zero_add]; exact mul_pos hr hpos
                · have hbd := hbaryDir_bound k θ
                  have hrM : r * M < m := (lt_div_iff₀ hM_pos).mp hlt
                  have hkm := hm_le k hk
                  have := neg_le_of_abs_le hbd
                  nlinarith
            rw [hopen_eq]
            have hlocal : localAngle Δ p = Real.pi := by
              simp [localAngle, hnot, hint, hp0, hp1, hp2]
            rw [hlocal]
            let w : ℝ² := if 0 < D then edgeVec Δ k₀ else -(edgeVec Δ k₀)
            have hw_ne : w ≠ 0 := by
              dsimp [w]
              split_ifs
              · exact edgeVec_ne_zero Δ k₀
              · exact neg_ne_zero.mpr (edgeVec_ne_zero Δ k₀)
            have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne
            obtain ⟨φ, hφ0, hφ1⟩ := polar_rep hw_ne
            have hset' : {θ ∈ Set.Ico 0 (2 * Real.pi) | 0 < baryDir Δ (unitVec θ) k₀} =
                {θ ∈ Set.Ico 0 (2 * Real.pi) | 0 < Real.sin (θ - φ)} := by
              ext θ
              simp only [Set.mem_ofPred_eq]
              refine and_congr_right fun _ => ?_
              dsimp only [baryDir, D]
              rcases lt_or_gt_of_ne hD with hDneg | hDpos
              · rw [div_pos_iff_neg hDneg]
                have hcr : cross (edgeVec Δ k₀) (unitVec θ) = -(‖w‖ * Real.sin (θ - φ)) := by
                  have hw' : w = -(edgeVec Δ k₀) := if_neg (not_lt.mpr (le_of_lt hDneg))
                  have hswap : cross (edgeVec Δ k₀) (unitVec θ) = -cross w (unitVec θ) := by
                    rw [hw']; simp [cross]; ring
                  rw [hswap, cross_unitVec_eq_sin hφ0 hφ1]
                rw [hcr, neg_lt_zero]
                exact mul_pos_iff_of_pos_left hwn
              · rw [div_pos_iff_of_pos_right hDpos]
                have hw' : w = edgeVec Δ k₀ := if_pos hDpos
                rw [← hw', cross_unitVec_eq_sin hφ0 hφ1]
                exact mul_pos_iff_of_pos_left hwn
            rw [hset', volume_sin_pos φ]

private lemma sum_localAngle_eq {n : ℕ} {T : Triangle ℝ ℝ²} {Ts : Fin n → Triangle ℝ ℝ²}
    (hdisj : Pairwise (fun i j => Disjoint (Ts i).interior (Ts j).interior))
    (hunion : ⋃ i, (Ts i).closedInterior = T.closedInterior) (p : ℝ²) :
    ∑ i : Fin n, localAngle (Ts i) p = localAngle T p := by
  obtain ⟨rT, hrT_pos, hrT⟩ := exists_radius_arc T p
  have hTi : ∀ i : Fin n, ∃ r > 0, ∀ r', 0 < r' → r' < r →
      closedArc (Ts i) p r' =ᵐ[volume] openArc (Ts i) p r' ∧
      MeasurableSet (openArc (Ts i) p r') ∧
      volume (openArc (Ts i) p r') = ENNReal.ofReal (localAngle (Ts i) p) :=
    fun i => exists_radius_arc (Ts i) p
  choose rI hrI_pos hrI using hTi
  let rmin : ℝ := (insert rT (Finset.univ.image rI)).inf' (Finset.insert_nonempty rT _) id
  have hrmin_pos : 0 < rmin := by
    rw [Finset.lt_inf'_iff]
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, id_eq] at hx ⊢
    rcases hx with rfl | ⟨i, rfl⟩
    · exact hrT_pos
    · exact hrI_pos i
  let r : ℝ := rmin / 2
  have hr_pos : 0 < r := half_pos hrmin_pos
  have hr_lt_T : r < rT := by
    have hle : rmin ≤ rT := Finset.inf'_le id (Finset.mem_insert_self rT _)
    dsimp only [r]
    linarith
  have hr_lt_I : ∀ i : Fin n, r < rI i := by
    intro i
    have hle : rmin ≤ rI i := Finset.inf'_le id
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem rI (Finset.mem_univ i)))
    dsimp only [r]
    linarith
  obtain ⟨haeT, -, hvolT⟩ := hrT r hr_pos hr_lt_T
  have haeI : ∀ i : Fin n, closedArc (Ts i) p r =ᵐ[volume] openArc (Ts i) p r :=
    fun i => (hrI i r hr_pos (hr_lt_I i)).1
  have hmeasI : ∀ i : Fin n, MeasurableSet (openArc (Ts i) p r) :=
    fun i => (hrI i r hr_pos (hr_lt_I i)).2.1
  have hvolI : ∀ i : Fin n, volume (openArc (Ts i) p r) = ENNReal.ofReal (localAngle (Ts i) p) :=
    fun i => (hrI i r hr_pos (hr_lt_I i)).2.2
  have hunion_arc : (⋃ i ∈ (Finset.univ : Finset (Fin n)), closedArc (Ts i) p r) =
      closedArc T p r := by
    ext θ
    simp only [closedArc, Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨i, hθ, hx⟩
      refine ⟨hθ, ?_⟩
      rw [← hunion]
      exact Set.mem_iUnion.mpr ⟨i, hx⟩
    · rintro ⟨hθ, hx⟩
      rw [← hunion] at hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact ⟨i, hθ, hi⟩
  have hae_union : (⋃ i ∈ (Finset.univ : Finset (Fin n)), closedArc (Ts i) p r) =ᵐ[volume]
      (⋃ i ∈ (Finset.univ : Finset (Fin n)), openArc (Ts i) p r) := by
    have hsub1 : ∀ i, closedArc (Ts i) p r =ᵐ[volume] openArc (Ts i) p r := haeI
    exact Filter.EventuallyEq.countable_bUnion (Finset.countable_toSet Finset.univ) fun i _ => hsub1 i
  have hdisj_arc : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (fun i => openArc (Ts i) p r) := by
    intro i _ j _ hij
    rw [Function.onFun, Set.disjoint_left]
    intro θ hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.2 hj.2
  have hvol_eq : ∑ i : Fin n, volume (openArc (Ts i) p r) = volume (openArc T p r) := by
    rw [← MeasureTheory.measure_biUnion_finset hdisj_arc (fun i _ => hmeasI i),
      ← MeasureTheory.measure_congr hae_union, hunion_arc, MeasureTheory.measure_congr haeT]
  simp_rw [hvolI] at hvol_eq
  rw [hvolT, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => localAngle_nonneg (Ts i) p)] at hvol_eq
  exact (ENNReal.ofReal_eq_ofReal_iff
    (Finset.sum_nonneg fun i _ => localAngle_nonneg (Ts i) p)
    (localAngle_nonneg T p)).mp hvol_eq

/- Part 5: Shared-Edge Overlap, Corner-Tile Geometry, and Combinatorial Contradictions -/

private lemma interior_eq_of_same_vertices {Δ₁ Δ₂ : Triangle ℝ ℝ²}
    (h : Finset.univ.image Δ₁.points = Finset.univ.image Δ₂.points) :
    Δ₁.interior = Δ₂.interior := by
  have hbij : ∃ e : Fin 3 ≃ Fin 3, ∀ k, Δ₂.points k = Δ₁.points (e k) := by
    have hex : ∀ k : Fin 3, ∃ j : Fin 3, Δ₂.points k = Δ₁.points j := by
      intro k
      have hk : Δ₂.points k ∈ Finset.univ.image Δ₁.points := by
        rw [h]; exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
      rcases Finset.mem_image.mp hk with ⟨j, _, hj⟩
      exact ⟨j, hj.symm⟩
    choose f hf using hex
    have hinj : Function.Injective f := by
      intro k₁ k₂ hfk
      apply Δ₂.independent.injective
      rw [hf k₁, hf k₂, hfk]
    exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), hf⟩
  rcases hbij with ⟨e, he⟩
  ext x
  constructor
  · rintro ⟨w, hw, hwI, rfl⟩
    refine ⟨fun k => w (e k), ?_, fun k => hwI (e k), ?_⟩
    · exact Equiv.sum_comp e w ▸ hw
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ (Equiv.sum_comp e w ▸ hw),
        Finset.affineCombination_eq_linear_combination _ _ _ hw]
      simp_rw [he]
      exact Equiv.sum_comp e (fun j => w j • Δ₁.points j)
  · rintro ⟨w, hw, hwI, rfl⟩
    refine ⟨fun j => w (e.symm j), ?_, fun j => hwI (e.symm j), ?_⟩
    · exact Equiv.sum_comp e.symm w ▸ hw
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ (Equiv.sum_comp e.symm w ▸ hw),
        Finset.affineCombination_eq_linear_combination _ _ _ hw]
      have hcomp : ∑ j : Fin 3, w (e.symm j) • Δ₁.points j =
          ∑ k : Fin 3, w k • Δ₁.points (e k) := by
        refine Fintype.sum_equiv e.symm _ _ fun j => ?_
        simp
      rw [hcomp]
      simp_rw [he]

private lemma interior_nonempty (Δ : Triangle ℝ ℝ²) : Δ.interior.Nonempty := by
  refine ⟨Finset.univ.affineCombination ℝ Δ.points (fun _ => (1 / 3 : ℝ)), ?_⟩
  refine mem_interior_of_pos Δ ?_ fun _ => by norm_num
  rw [Fin.sum_univ_three]
  norm_num

private lemma mem_interior_of_three_vertices {Δ : Triangle ℝ ℝ²} {p q r : ℝ²}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : p ∈ Set.range Δ.points) (hq : q ∈ Set.range Δ.points) (hr : r ∈ Set.range Δ.points)
    {w₀ w₁ w₂ : ℝ} (hw : w₀ + w₁ + w₂ = 1) (h0 : 0 < w₀) (h1 : 0 < w₁) (h2 : 0 < w₂) :
    w₀ • p + w₁ • q + w₂ • r ∈ Δ.interior := by
  rcases hp with ⟨kp, hkp⟩
  rcases hq with ⟨kq, hkq⟩
  rcases hr with ⟨kr, hkr⟩
  have hne01 : kp ≠ kq := fun h => hpq (by rw [← hkp, ← hkq, h])
  have hne02 : kp ≠ kr := fun h => hpr (by rw [← hkp, ← hkr, h])
  have hne12 : kq ≠ kr := fun h => hqr (by rw [← hkq, ← hkr, h])
  let w : Fin 3 → ℝ := fun k =>
    if k = kp then w₀ else if k = kq then w₁ else w₂
  have hsum : ∑ k : Fin 3, w k = 1 := by
    rw [Fin.sum_univ_three]
    fin_cases kp <;> fin_cases kq <;> fin_cases kr <;>
      simp [w] at hne01 hne02 hne12 ⊢ <;> linarith
  have hpos : ∀ k : Fin 3, 0 < w k := by
    intro k
    dsimp [w]
    split_ifs <;> assumption
  have hcomb : Finset.univ.affineCombination ℝ Δ.points w = w₀ • p + w₁ • q + w₂ • r := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum, Fin.sum_univ_three]
    rw [← hkp, ← hkq, ← hkr]
    fin_cases kp <;> fin_cases kq <;> fin_cases kr <;>
      simp [w] at hne01 hne02 hne12 ⊢ <;> abel
  rw [← hcomb]
  exact mem_interior_of_pos Δ hsum hpos

private lemma not_disjoint_of_shared_edge_same_side {Δ₁ Δ₂ : Triangle ℝ ℝ²}
    {p q r₁ r₂ : ℝ²}
    (hp1 : p ∈ Set.range Δ₁.points) (hq1 : q ∈ Set.range Δ₁.points) (hr1 : r₁ ∈ Set.range Δ₁.points)
    (hp2 : p ∈ Set.range Δ₂.points) (hq2 : q ∈ Set.range Δ₂.points) (hr2 : r₂ ∈ Set.range Δ₂.points)
    (hside : 0 < cross (q - p) (r₁ - p) * cross (q - p) (r₂ - p)) :
    ¬ Disjoint Δ₁.interior Δ₂.interior := by
  have hD1 : cross (q - p) (r₁ - p) ≠ 0 := fun h => by rw [h, zero_mul] at hside; exact lt_irrefl 0 hside
  have hD2 : cross (q - p) (r₂ - p) ≠ 0 := fun h => by rw [h, mul_zero] at hside; exact lt_irrefl 0 hside
  have hpq : p ≠ q := by
    rintro rfl; simp [cross] at hD1
  have hpr1 : p ≠ r₁ := by
    rintro rfl; simp [cross] at hD1
  have hqr1 : q ≠ r₁ := by
    rintro rfl; apply hD1; simp [cross]; ring
  have hpr2 : p ≠ r₂ := by
    rintro rfl; simp [cross] at hD2
  have hqr2 : q ≠ r₂ := by
    rintro rfl; apply hD2; simp [cross]; ring
  let D₁ := cross (q - p) (r₁ - p)
  let D₂ := cross (q - p) (r₂ - p)
  let A := cross (r₁ - p) (r₂ - p)
  let γ : ℝ := D₁ / D₂
  let μ : ℝ := A / D₂
  have hγ_pos : 0 < γ := by
    dsimp [γ, D₁, D₂]
    exact div_pos_iff.mpr (mul_pos_iff.mp hside)
  have hr1_eq : r₁ - p = μ • (q - p) + γ • (r₂ - p) := by
    have hcr := cross_cramer (q - p) (r₂ - p) (r₁ - p)
    have hsm : D₂⁻¹ • (D₂ • (r₁ - p)) = D₂⁻¹ • (A • (q - p) + D₁ • (r₂ - p)) :=
      congrArg (fun v => D₂⁻¹ • v) hcr
    rw [smul_smul, inv_mul_cancel₀ hD2, one_smul, smul_add, smul_smul, smul_smul] at hsm
    simpa [μ, γ, div_eq_inv_mul] using hsm
  let t : ℝ := 1 / (4 * (1 + |μ| + γ))
  have hden_pos : 0 < 4 * (1 + |μ| + γ) := by linarith [abs_nonneg μ]
  have ht_pos : 0 < t := div_pos one_pos hden_pos
  have ht_mul : t * (1 + |μ| + γ) = 1 / 4 := by
    dsimp [t]
    field_simp [ne_of_gt hden_pos]
  have ht_lt_half : t < 1 / 2 := by
    have : 4 ≤ 4 * (1 + |μ| + γ) := by linarith [abs_nonneg μ]
    have hle : t ≤ 1 / 4 := by
      dsimp [t]
      exact one_div_le_one_div_of_le (by norm_num) this
    linarith
  let x : ℝ² := (1 / 2 - t / 2) • p + (1 / 2 - t / 2) • q + t • r₁
  have hx1 : x ∈ Δ₁.interior :=
    mem_interior_of_three_vertices hpq hpr1 hqr1 hp1 hq1 hr1 (by ring) (by linarith) (by linarith) ht_pos
  have hx_eq2 : x = (1 / 2 - t * (μ - 1 / 2 + γ)) • p + (1 / 2 + t * (μ - 1 / 2)) • q + (t * γ) • r₂ := by
    have h1 : x = p + (1 / 2 - t / 2) • (q - p) + t • (r₁ - p) := by
      apply ext2 <;> (simp only [x, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring)
    rw [h1, hr1_eq]
    apply ext2 <;> (simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring)
  have hw0_pos : 0 < 1 / 2 - t * (μ - 1 / 2 + γ) := by
    have h1 : μ - 1 / 2 + γ ≤ 1 + |μ| + γ := by linarith [le_abs_self μ]
    have h2 : t * (μ - 1 / 2 + γ) ≤ t * (1 + |μ| + γ) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt ht_pos)
    linarith
  have hw1_pos : 0 < 1 / 2 + t * (μ - 1 / 2) := by
    have h1 : -(1 + |μ| + γ) ≤ μ - 1 / 2 := by linarith [neg_abs_le μ]
    have h2 : -(t * (1 + |μ| + γ)) ≤ t * (μ - 1 / 2) := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt ht_pos)
      linarith
    linarith
  have hx2 : x ∈ Δ₂.interior := by
    rw [hx_eq2]
    exact mem_interior_of_three_vertices hpq hpr2 hqr2 hp2 hq2 hr2 (by ring)
      hw0_pos hw1_pos (mul_pos ht_pos hγ_pos)
  intro hdisj
  exact Set.disjoint_left.mp hdisj hx1 hx2

private lemma sub_triangle_interior_subset {T Δ : Triangle ℝ ℝ²}
    (hsub : Δ.closedInterior ⊆ T.closedInterior) : Δ.interior ⊆ T.interior := by
  intro x hx
  rw [mem_interior_iff_bary] at hx ⊢
  intro k
  have hnn : 0 ≤ bary T x k := (mem_closedInterior_iff_bary T x).mp
    (hsub (Δ.interior_subset_closedInterior ((mem_interior_iff_bary Δ x).mpr hx))) k
  refine lt_of_le_of_ne hnn ?_
  intro h0
  have hD := cross_ne_zero_of_triangle T
  let u : ℝ² := mk2 (-(edgeVec T k 1)) (edgeVec T k 0)
  have hcr : cross (edgeVec T k) u = edgeVec T k 0 ^ 2 + edgeVec T k 1 ^ 2 := by
    simp only [cross, u, mk2_zero, mk2_one]; ring
  have hcr_pos : 0 < cross (edgeVec T k) u := by
    have hne := edgeVec_ne_zero T k
    have hsq : 0 < ‖edgeVec T k‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
    rw [norm_sq2] at hsq
    linarith
  let dir : ℝ² := if 0 < cross (T.points 1 - T.points 0) (T.points 2 - T.points 0) then -u else u
  have hdir_neg : baryDir T dir k < 0 := by
    dsimp only [baryDir, dir]
    rcases lt_or_gt_of_ne hD with hDn | hDp
    · rw [if_neg (not_lt.mpr (le_of_lt hDn))]
      exact div_neg_of_pos_of_neg hcr_pos hDn
    · rw [if_pos hDp]
      have hcrn : cross (edgeVec T k) (-u) = -cross (edgeVec T k) u := by simp [cross]; ring
      rw [hcrn]
      exact div_neg_of_neg_of_pos (neg_lt_zero.mpr hcr_pos) hDp
  let m := min (bary Δ x 0) (min (bary Δ x 1) (bary Δ x 2))
  have hm_pos : 0 < m := lt_min (hx 0) (lt_min (hx 1) (hx 2))
  let B := 1 + |baryDir Δ dir 0| + |baryDir Δ dir 1| + |baryDir Δ dir 2|
  have hB_pos : 0 < B := by positivity
  let ε : ℝ := m / (2 * B)
  have hε_pos : 0 < ε := div_pos hm_pos (by positivity)
  have hxε_in : x + ε • dir ∈ Δ.closedInterior := by
    rw [mem_closedInterior_iff_bary]
    intro j
    rw [bary_add_smul]
    have hjm : m ≤ bary Δ x j := by
      fin_cases j
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (min_le_left _ _)
      · exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hjB : |baryDir Δ dir j| ≤ B := by
      fin_cases j <;> dsimp [B] <;>
        linarith [abs_nonneg (baryDir Δ dir 0), abs_nonneg (baryDir Δ dir 1),
          abs_nonneg (baryDir Δ dir 2)]
    have hneg : -B ≤ baryDir Δ dir j := neg_le_of_abs_le hjB
    have hmul : -(ε * B) ≤ ε * baryDir Δ dir j := by nlinarith
    have hεB : ε * B = m / 2 := by dsimp [ε]; field_simp [ne_of_gt hB_pos]
    linarith
  have hxε_T := (mem_closedInterior_iff_bary T (x + ε • dir)).mp (hsub hxε_in) k
  rw [bary_add_smul, ← h0, zero_add] at hxε_T
  linarith [mul_neg_of_pos_of_neg hε_pos hdir_neg]

private lemma corner_tile_edges {n : ℕ} {T : Triangle ℝ ℝ²} {Ts : Fin n → Triangle ℝ ℝ²}
    (hunion : ⋃ i, (Ts i).closedInterior = T.closedInterior)
    {j a b : Fin 3} (hja : j ≠ a) (hjb : j ≠ b) (hab : a ≠ b)
    {i₀ : Fin n} (hi₀ : ∀ i : Fin n, i ≠ i₀ → T.points j ∉ (Ts i).closedInterior)
    (hvj : T.points j ∈ Set.range (Ts i₀).points) :
    ∃ p q : ℝ²,
      p ∈ Set.range (Ts i₀).points ∧ q ∈ Set.range (Ts i₀).points ∧
      bary T p b = 0 ∧ 0 < bary T p a ∧
      bary T q a = 0 ∧ 0 < bary T q b ∧
      Finset.univ.image (Ts i₀).points = {T.points j, p, q} := by
  have hball : ∃ ρ > 0, ∀ i : Fin n, i ≠ i₀ →
      Disjoint (Metric.ball (T.points j) ρ) (Ts i).closedInterior := by
    have hopen : ∀ i : Fin n, i ≠ i₀ → ∃ ρ > 0,
        Disjoint (Metric.ball (T.points j) ρ) (Ts i).closedInterior := by
      intro i hi
      have hmem : T.points j ∈ ((Ts i).closedInterior)ᶜ := hi₀ i hi
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp (Ts i).isClosed_closedInterior.isOpen_compl _ hmem
      exact ⟨ρ, hρ, Set.disjoint_left.mpr fun x hx => hsub hx⟩
    let ρf : Fin n → ℝ := fun i =>
      if h : i ≠ i₀ then Classical.choose (hopen i h) else 1
    have hρf_pos : ∀ i : Fin n, 0 < ρf i := by
      intro i
      dsimp [ρf]
      by_cases h : i ≠ i₀
      · rw [dif_pos h]; exact (Classical.choose_spec (hopen i h)).1
      · rw [dif_neg h]; exact one_pos
    let ρ : ℝ := (insert 1 (Finset.univ.image ρf)).inf' (Finset.insert_nonempty 1 _) id
    have hρ_pos : 0 < ρ := by
      rw [Finset.lt_inf'_iff]
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, id_eq] at hx ⊢
      rcases hx with rfl | ⟨i, rfl⟩
      · exact one_pos
      · exact hρf_pos i
    refine ⟨ρ, hρ_pos, fun i hi => ?_⟩
    have hle : ρ ≤ ρf i := Finset.inf'_le id
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem ρf (Finset.mem_univ i)))
    have hspec := (Classical.choose_spec (hopen i hi)).2
    have hρeq : ρf i = Classical.choose (hopen i hi) := dif_pos hi
    rw [hρeq] at hle
    exact hspec.mono_left (Metric.ball_subset_ball hle)
  rcases hball with ⟨ρ, hρ_pos, hρ_disj⟩
  have hlocal : ∀ x ∈ T.closedInterior, x ∈ Metric.ball (T.points j) ρ →
      x ∈ (Ts i₀).closedInterior := by
    intro x hxT hxB
    rw [← hunion] at hxT
    rcases Set.mem_iUnion.mp hxT with ⟨i, hi⟩
    by_cases heq : i = i₀
    · rwa [← heq]
    · exact False.elim (Set.disjoint_left.mp (hρ_disj i heq) hxB hi)
  let t : ℝ := min (1 / 2) (ρ / (2 * (1 + ‖T.points a - T.points j‖ + ‖T.points b - T.points j‖)))
  have ht_pos : 0 < t := lt_min (by norm_num) (div_pos hρ_pos (by positivity))
  have ht_lt1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  let xa : ℝ² := T.points j + t • (T.points a - T.points j)
  let xb : ℝ² := T.points j + t • (T.points b - T.points j)
  have hxa_T : xa ∈ T.closedInterior := by
    let w : Fin 3 → ℝ := fun k => if k = j then 1 - t else if k = a then t else 0
    have hw : ∑ k : Fin 3, w k = 1 := by
      rw [Fin.sum_univ_three, ← fin3_sum_perm w hja hjb hab]
      simp [w, hja.symm, hjb.symm, hab.symm]
    have hcomb : Finset.univ.affineCombination ℝ T.points w = xa := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw,
        fin3_affine_decomp T.points hja hjb hab w hw]
      simp only [w, hja.symm, hjb.symm, hab.symm, ↓reduceIte, xa]
      apply ext2 <;> (simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring)
    rw [← hcomb]
    refine mem_closedInterior_of_nonneg T hw fun k => ?_
    dsimp [w]; split_ifs <;> linarith
  have hxb_T : xb ∈ T.closedInterior := by
    let w : Fin 3 → ℝ := fun k => if k = j then 1 - t else if k = b then t else 0
    have hw : ∑ k : Fin 3, w k = 1 := by
      rw [Fin.sum_univ_three, ← fin3_sum_perm w hja hjb hab]
      simp [w, hja.symm, hjb.symm, hab]
    have hcomb : Finset.univ.affineCombination ℝ T.points w = xb := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw,
        fin3_affine_decomp T.points hja hjb hab w hw]
      simp only [w, hja.symm, hjb.symm, hab, ↓reduceIte, xb]
      apply ext2 <;> (simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring)
    rw [← hcomb]
    refine mem_closedInterior_of_nonneg T hw fun k => ?_
    dsimp [w]; split_ifs <;> linarith
  have hxa_B : xa ∈ Metric.ball (T.points j) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : xa - T.points j = t • (T.points a - T.points j) := by simp [xa]
    rw [hsub, norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos)]
    have hle : t ≤ ρ / (2 * (1 + ‖T.points a - T.points j‖ + ‖T.points b - T.points j‖)) :=
      min_le_right _ _
    have hden : 0 < 1 + ‖T.points a - T.points j‖ + ‖T.points b - T.points j‖ := by positivity
    have h1 : t * ‖T.points a - T.points j‖ ≤
        (ρ / (2 * (1 + ‖T.points a - T.points j‖ + ‖T.points b - T.points j‖))) *
        ‖T.points a - T.points j‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    have h2 : (ρ / (2 * (1 + ‖T.points a - T.points j‖ + ‖T.points b - T.points j‖))) *
        ‖T.points a - T.points j‖ < ρ / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      nlinarith [norm_nonneg (T.points b - T.points j)]
    linarith
  have hxb_B : xb ∈ Metric.ball (T.points j) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : xb - T.points j = t • (T.points b - T.points j) := by simp [xb]
    rw [hsub, norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos)]
    have hle : t ≤ ρ / (2 * (1 + ‖T.points a - T.points j‖ + ‖T.points b - T.points j‖)) :=
      min_le_right _ _
    have hden : 0 < 1 + ‖T.points a - T.points j‖ + ‖T.points b - T.points j‖ := by positivity
    have h1 : t * ‖T.points b - T.points j‖ ≤
        (ρ / (2 * (1 + ‖T.points a - T.points j‖ + ‖T.points b - T.points j‖))) *
        ‖T.points b - T.points j‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    have h2 : (ρ / (2 * (1 + ‖T.points a - T.points j‖ + ‖T.points b - T.points j‖))) *
        ‖T.points b - T.points j‖ < ρ / 2 := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)]
      nlinarith [norm_nonneg (T.points a - T.points j)]
    linarith
  have hxa_in : xa ∈ (Ts i₀).closedInterior := hlocal xa hxa_T hxa_B
  have hxb_in : xb ∈ (Ts i₀).closedInterior := hlocal xb hxb_T hxb_B
  rcases hvj with ⟨k₀, hk₀⟩
  have hex_other : ∃ k₁ k₂ : Fin 3, k₀ ≠ k₁ ∧ k₀ ≠ k₂ ∧ k₁ ≠ k₂ := by
    fin_cases k₀
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  rcases hex_other with ⟨k₁, k₂, h01, h02, h12⟩
  let u₁ := (Ts i₀).points k₁
  let u₂ := (Ts i₀).points k₂
  have hpts_img : Finset.univ.image (Ts i₀).points = {T.points j, u₁, u₂} := by
    rw [fin3_img_eq (Ts i₀).points h01 h02 h12, hk₀]
  have hu1_T : u₁ ∈ T.closedInterior := by
    rw [← hunion]; exact Set.mem_iUnion.mpr ⟨i₀, (Ts i₀).point_mem_closedInterior k₁⟩
  have hu2_T : u₂ ∈ T.closedInterior := by
    rw [← hunion]; exact Set.mem_iUnion.mpr ⟨i₀, (Ts i₀).point_mem_closedInterior k₂⟩
  have hc1a : 0 ≤ bary T u₁ a := (mem_closedInterior_iff_bary T u₁).mp hu1_T a
  have hc1b : 0 ≤ bary T u₁ b := (mem_closedInterior_iff_bary T u₁).mp hu1_T b
  have hc2a : 0 ≤ bary T u₂ a := (mem_closedInterior_iff_bary T u₂).mp hu2_T a
  have hc2b : 0 ≤ bary T u₂ b := (mem_closedInterior_iff_bary T u₂).mp hu2_T b
  have hbary_vec : ∀ y : ℝ², y - T.points j =
      bary T y a • (T.points a - T.points j) + bary T y b • (T.points b - T.points j) :=
    fin3_vec_decomp T hja hjb hab
  have hbary_lin : ∀ (α β : ℝ) (x : ℝ²),
      x = (1 - α - β) • T.points j + α • u₁ + β • u₂ →
      bary T x a = α * bary T u₁ a + β * bary T u₂ a ∧
      bary T x b = α * bary T u₁ b + β * bary T u₂ b := by
    intro α β x hx
    let w : Fin 3 → ℝ := fun k =>
      if k = j then (1 - α - β) + α * bary T u₁ j + β * bary T u₂ j
      else if k = a then α * bary T u₁ a + β * bary T u₂ a
      else α * bary T u₁ b + β * bary T u₂ b
    have hwsum : ∑ k : Fin 3, w k = 1 := by
      have h1 := bary_sum T u₁
      have h2 := bary_sum T u₂
      rw [Fin.sum_univ_three] at h1 h2 ⊢
      have hp1 := fin3_sum_perm (bary T u₁) hja hjb hab
      have hp2 := fin3_sum_perm (bary T u₂) hja hjb hab
      have hpw := fin3_sum_perm w hja hjb hab
      have hwj : w j = (1 - α - β) + α * bary T u₁ j + β * bary T u₂ j := by simp [w]
      have hwa : w a = α * bary T u₁ a + β * bary T u₂ a := by simp [w, hja.symm]
      have hwb : w b = α * bary T u₁ b + β * bary T u₂ b := by simp [w, hjb.symm, hab.symm]
      rw [← hpw, hwj, hwa, hwb]
      linear_combination α * (hp1 + h1) + β * (hp2 + h2)
    have hwcomb : Finset.univ.affineCombination ℝ T.points w = x := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hwsum, hx]
      have h1 := bary_affineCombination T u₁
      have h2 := bary_affineCombination T u₂
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (bary_sum T u₁)] at h1
      rw [Finset.affineCombination_eq_linear_combination _ _ _ (bary_sum T u₂)] at h2
      have hd_w := fin3_affine_decomp T.points hja hjb hab w hwsum
      have hd_1 := fin3_affine_decomp T.points hja hjb hab (bary T u₁) (bary_sum T u₁)
      have hd_2 := fin3_affine_decomp T.points hja hjb hab (bary T u₂) (bary_sum T u₂)
      rw [hd_1] at h1
      rw [hd_2] at h2
      rw [hd_w, ← h1, ← h2]
      have hwa : w a = α * bary T u₁ a + β * bary T u₂ a := by simp [w, hja.symm]
      have hwb : w b = α * bary T u₁ b + β * bary T u₂ b := by simp [w, hjb.symm, hab.symm]
      rw [hwa, hwb]
      apply ext2 <;> (simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring)
    have hweq := bary_unique T hwsum hwcomb
    refine ⟨?_, ?_⟩
    · rw [← hweq]; dsimp [w]; simp [hja.symm]
    · rw [← hweq]; dsimp [w]; simp [hjb.symm, hab.symm]
  have hxa_bary : bary T xa a = t ∧ bary T xa b = 0 := by
    let w : Fin 3 → ℝ := fun k => if k = j then 1 - t else if k = a then t else 0
    have hw : ∑ k : Fin 3, w k = 1 := by
      rw [Fin.sum_univ_three, ← fin3_sum_perm w hja hjb hab]
      simp [w, hja.symm, hjb.symm, hab.symm]
    have hcomb : Finset.univ.affineCombination ℝ T.points w = xa := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw,
        fin3_affine_decomp T.points hja hjb hab w hw]
      simp only [w, hja.symm, hjb.symm, hab.symm, ↓reduceIte, xa]
      apply ext2 <;> (simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring)
    have hweq := bary_unique T hw hcomb
    rw [← hweq]; simp [w, hja.symm, hjb.symm, hab.symm]
  have hxb_bary : bary T xb a = 0 ∧ bary T xb b = t := by
    let w : Fin 3 → ℝ := fun k => if k = j then 1 - t else if k = b then t else 0
    have hw : ∑ k : Fin 3, w k = 1 := by
      rw [Fin.sum_univ_three, ← fin3_sum_perm w hja hjb hab]
      simp [w, hja.symm, hjb.symm, hab]
    have hcomb : Finset.univ.affineCombination ℝ T.points w = xb := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw,
        fin3_affine_decomp T.points hja hjb hab w hw]
      simp only [w, hja.symm, hjb.symm, hab, ↓reduceIte, xb]
      apply ext2 <;> (simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring)
    have hweq := bary_unique T hw hcomb
    rw [← hweq]; simp [w, hja.symm, hjb.symm, hab]
  have hmem_decomp : ∀ x ∈ (Ts i₀).closedInterior,
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ x = (1 - α - β) • T.points j + α • u₁ + β • u₂ := by
    intro x hx
    rcases hx with ⟨w, hw, hwI, rfl⟩
    refine ⟨w k₁, w k₂, (hwI k₁).1, (hwI k₂).1, ?_⟩
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw,
      fin3_affine_decomp (Ts i₀).points h01 h02 h12 w hw, hk₀]
  obtain ⟨α₁, β₁, hα₁, hβ₁, hxa_eq⟩ := hmem_decomp xa hxa_in
  obtain ⟨α₂, β₂, hα₂, hβ₂, hxb_eq⟩ := hmem_decomp xb hxb_in
  have h1 := hbary_lin α₁ β₁ xa hxa_eq
  have h2 := hbary_lin α₂ β₂ xb hxb_eq
  rw [hxa_bary.1, hxa_bary.2] at h1
  rw [hxb_bary.1, hxb_bary.2] at h2
  have hb_zero : bary T u₁ b = 0 ∨ bary T u₂ b = 0 := by
    by_contra h
    push Not at h
    have hb1p : 0 < bary T u₁ b := lt_of_le_of_ne hc1b (Ne.symm h.1)
    have hb2p : 0 < bary T u₂ b := lt_of_le_of_ne hc2b (Ne.symm h.2)
    have hα0 : α₁ = 0 := by nlinarith
    have hβ0 : β₁ = 0 := by nlinarith
    rw [hα0, hβ0, zero_mul, zero_mul, add_zero] at h1
    linarith
  have ha_zero : bary T u₁ a = 0 ∨ bary T u₂ a = 0 := by
    by_contra h
    push Not at h
    have ha1p : 0 < bary T u₁ a := lt_of_le_of_ne hc1a (Ne.symm h.1)
    have ha2p : 0 < bary T u₂ a := lt_of_le_of_ne hc2a (Ne.symm h.2)
    have hα0 : α₂ = 0 := by nlinarith
    have hβ0 : β₂ = 0 := by nlinarith
    rw [hα0, hβ0, zero_mul, zero_mul, add_zero] at h2
    linarith
  have hu1_nz : ¬ (bary T u₁ a = 0 ∧ bary T u₁ b = 0) := by
    rintro ⟨ha0, hb0⟩
    have hu1_eq : u₁ = T.points j := by
      have hvec := hbary_vec u₁
      rw [ha0, hb0, zero_smul, zero_smul, add_zero] at hvec
      exact sub_eq_zero.mp hvec
    rw [← hk₀] at hu1_eq
    exact h01.symm ((Ts i₀).independent.injective hu1_eq)
  have hu2_nz : ¬ (bary T u₂ a = 0 ∧ bary T u₂ b = 0) := by
    rintro ⟨ha0, hb0⟩
    have hu2_eq : u₂ = T.points j := by
      have hvec := hbary_vec u₂
      rw [ha0, hb0, zero_smul, zero_smul, add_zero] at hvec
      exact sub_eq_zero.mp hvec
    rw [← hk₀] at hu2_eq
    exact h02.symm ((Ts i₀).independent.injective hu2_eq)
  rcases hb_zero with hb1 | hb2
  · have ha1 : 0 < bary T u₁ a := lt_of_le_of_ne hc1a fun h => hu1_nz ⟨h.symm, hb1⟩
    have ha2 : bary T u₂ a = 0 := ha_zero.resolve_left (ne_of_gt ha1)
    have hb2' : 0 < bary T u₂ b := lt_of_le_of_ne hc2b fun h => hu2_nz ⟨ha2, h.symm⟩
    exact ⟨u₁, u₂, ⟨k₁, rfl⟩, ⟨k₂, rfl⟩, hb1, ha1, ha2, hb2', hpts_img⟩
  · have ha2 : 0 < bary T u₂ a := lt_of_le_of_ne hc2a fun h => hu2_nz ⟨h.symm, hb2⟩
    have ha1 : bary T u₁ a = 0 := ha_zero.resolve_right (ne_of_gt ha2)
    have hb1' : 0 < bary T u₁ b := lt_of_le_of_ne hc1b fun h => hu1_nz ⟨ha1, h.symm⟩
    refine ⟨u₂, u₁, ⟨k₂, rfl⟩, ⟨k₁, rfl⟩, hb2, ha2, ha1, hb1', ?_⟩
    rw [hpts_img]
    ext y
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

private lemma not_isSimiliCuttable_two_three_five {T : Triangle ℝ ℝ²}
    (hind : ∀ r s t : ℤ,
      (r : ℝ) * triAngle T 0 + (s : ℝ) * triAngle T 1 + (t : ℝ) * triAngle T 2 = 0 →
      r = 0 ∧ s = 0 ∧ t = 0)
    {n : ℕ} (hn : n = 2 ∨ n = 3 ∨ n = 5) :
    ¬ Erdos633.IsSimiliCuttable n T := by
  rintro ⟨Ts, hsim, hdisj, hunion⟩
  have hn_pos : 0 < n := by omega
  let iZero : Fin n := ⟨0, hn_pos⟩
  let θ : Fin 3 → ℝ := triAngle (Ts iZero)
  have hθ_eq : ∀ (i : Fin n) (k : Fin 3), triAngle (Ts i) k = θ k := by
    intro i k
    have hs := hsim i iZero
    have hpts_i : (Ts i).points = ![(Ts i).points 0, (Ts i).points 1, (Ts i).points 2] := by
      ext m; fin_cases m <;> rfl
    have hpts_0 : (Ts iZero).points =
        ![(Ts iZero).points 0, (Ts iZero).points 1, (Ts iZero).points 2] := by
      ext m; fin_cases m <;> rfl
    rw [hpts_i, hpts_0] at hs
    obtain ⟨ha1, ha2, ha0⟩ := hs.angle_eq_all
    fin_cases k
    · dsimp [triAngle, θ]
      rw [EuclideanGeometry.angle_comm ((Ts i).points 1),
        EuclideanGeometry.angle_comm ((Ts iZero).points 1)]
      exact ha0
    · dsimp [triAngle, θ]
      rw [EuclideanGeometry.angle_comm ((Ts i).points 2),
        EuclideanGeometry.angle_comm ((Ts iZero).points 2)]
      exact ha1
    · dsimp [triAngle, θ]
      rw [EuclideanGeometry.angle_comm ((Ts i).points 0),
        EuclideanGeometry.angle_comm ((Ts iZero).points 0)]
      exact ha2
  have hθ_pos : ∀ k : Fin 3, 0 < θ k := fun k => triAngle_pos (Ts iZero) k
  have hθ_sum : θ 0 + θ 1 + θ 2 = Real.pi := triAngle_sum (Ts iZero)
  let vCount (p : ℝ²) (k : Fin 3) : ℕ := (Finset.univ.filter fun i : Fin n => (Ts i).points k = p).card
  let eCount (p : ℝ²) : ℕ :=
    (Finset.univ.filter fun i : Fin n =>
      p ∈ (Ts i).closedInterior ∧ p ∉ (Ts i).interior ∧ ∀ k : Fin 3, (Ts i).points k ≠ p).card
  let iCount (p : ℝ²) : ℕ := (Finset.univ.filter fun i : Fin n => p ∈ (Ts i).interior).card
  have hlocal_decomp : ∀ p : ℝ²,
      (∑ k : Fin 3, (vCount p k : ℝ) * θ k) + (eCount p : ℝ) * Real.pi +
        2 * (iCount p : ℝ) * Real.pi = localAngle T p := by
    intro p
    rw [← sum_localAngle_eq hdisj hunion p]
    have hterm : ∀ i : Fin n,
        localAngle (Ts i) p =
          (∑ k : Fin 3, if (Ts i).points k = p then θ k else 0) +
          (if p ∈ (Ts i).closedInterior ∧ p ∉ (Ts i).interior ∧ ∀ k : Fin 3, (Ts i).points k ≠ p
            then Real.pi else 0) +
          (if p ∈ (Ts i).interior then 2 * Real.pi else 0) := by
      intro i
      have hinj := (Ts i).independent.injective
      have h01 : (Ts i).points 0 ≠ (Ts i).points 1 := hinj.ne (by decide)
      have h02 : (Ts i).points 0 ≠ (Ts i).points 2 := hinj.ne (by decide)
      have h12 : (Ts i).points 1 ≠ (Ts i).points 2 := hinj.ne (by decide)
      have hpt_not_int : ∀ k : Fin 3, (Ts i).points k ∉ (Ts i).interior := by
        intro k hk
        rw [mem_interior_iff_bary] at hk
        have hother : ∃ j : Fin 3, j ≠ k := by
          fin_cases k
          · exact ⟨1, by decide⟩
          · exact ⟨0, by decide⟩
          · exact ⟨0, by decide⟩
        rcases hother with ⟨j, hj⟩
        have hpos := hk j
        rw [bary_point] at hpos
        simp [hj] at hpos
      rw [Fin.sum_univ_three]
      unfold localAngle
      by_cases hcl : p ∈ (Ts i).closedInterior
      · by_cases hint : p ∈ (Ts i).interior
        · have hne : ∀ k : Fin 3, (Ts i).points k ≠ p := fun k hk => hpt_not_int k (hk.symm ▸ hint)
          simp [hcl, hint, hne 0, hne 1, hne 2]
        · by_cases hp0 : p = (Ts i).points 0
          · subst hp0
            simp [hcl, hint, h01.symm, h02.symm, hθ_eq i 0]
          · by_cases hp1 : p = (Ts i).points 1
            · subst hp1
              simp [hcl, hint, h01, h01.symm, h12.symm, hθ_eq i 1]
            · by_cases hp2 : p = (Ts i).points 2
              · subst hp2
                simp [hcl, hint, h02, h02.symm, h12, h12.symm, hθ_eq i 2]
              · have hall : ∀ k : Fin 3, (Ts i).points k ≠ p := by
                  intro k; fin_cases k <;> exact Ne.symm ‹_›
                simp [hcl, hint, hp0, hp1, hp2, Ne.symm hp0, Ne.symm hp1, Ne.symm hp2, hall]
      · have hint : p ∉ (Ts i).interior := fun h => hcl ((Ts i).interior_subset_closedInterior h)
        have hne : ∀ k : Fin 3, (Ts i).points k ≠ p := fun k hk =>
          hcl (hk ▸ (Ts i).point_mem_closedInterior k)
        simp [hcl, hint, hne 0, hne 1, hne 2]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        simp only [vCount, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]
      · simp only [eCount, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]
    · simp only [iCount, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul]
      ring
  have hT_local_corner : ∀ j : Fin 3, localAngle T (T.points j) = triAngle T j := by
    intro j
    have hinj := T.independent.injective
    have hpt_not_int : T.points j ∉ T.interior := by
      rw [mem_interior_iff_bary]
      intro hall
      have hother : ∃ k : Fin 3, k ≠ j := by
        fin_cases j
        · exact ⟨1, by decide⟩
        · exact ⟨0, by decide⟩
        · exact ⟨0, by decide⟩
      rcases hother with ⟨k, hk⟩
      have := hall k
      rw [bary_point] at this
      simp [hk] at this
    unfold localAngle
    have hcl := T.point_mem_closedInterior j
    rcases fin3_cases j with rfl | rfl | rfl
    · simp [hcl, hpt_not_int]
    · simp [hcl, hpt_not_int, hinj.ne (by decide : (1 : Fin 3) ≠ 0)]
    · simp [hcl, hpt_not_int, hinj.ne (by decide : (2 : Fin 3) ≠ 0),
        hinj.ne (by decide : (2 : Fin 3) ≠ 1)]
  have hcorner_eq : ∀ j : Fin 3,
      eCount (T.points j) = 0 ∧ iCount (T.points j) = 0 ∧
      ∑ k : Fin 3, (vCount (T.points j) k : ℝ) * θ k = triAngle T j := by
    intro j
    have hd := hlocal_decomp (T.points j)
    rw [hT_local_corner j] at hd
    have hlt := triAngle_lt_pi T j
    have hsum_nn : 0 ≤ ∑ k : Fin 3, (vCount (T.points j) k : ℝ) * θ k :=
      Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hθ_pos k))
    have he0 : eCount (T.points j) = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ (eCount (T.points j) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne
      have hi_nn : 0 ≤ 2 * (iCount (T.points j) : ℝ) * Real.pi := by positivity
      nlinarith [Real.pi_pos]
    have hi0 : iCount (T.points j) = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ (iCount (T.points j) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hne
      have he_nn : 0 ≤ (eCount (T.points j) : ℝ) * Real.pi := by positivity
      nlinarith [Real.pi_pos]
    rw [he0, hi0] at hd
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero] at hd
    exact ⟨he0, hi0, hd⟩
  have hind_Q : ∀ q : Fin 3 → ℚ, (∑ j : Fin 3, (q j : ℝ) * triAngle T j = 0) → q = 0 := by
    intro q hq
    let D : ℕ := (q 0).den * (q 1).den * (q 2).den
    have hD_pos : 0 < D := by
      dsimp [D]; exact mul_pos (mul_pos (q 0).pos (q 1).pos) (q 2).pos
    have hq_int : ∀ j : Fin 3, ∃ z : ℤ, (D : ℝ) * (q j : ℝ) = (z : ℝ) := by
      intro j
      fin_cases j
      · refine ⟨(q 0).num * ((q 1).den : ℤ) * ((q 2).den : ℤ), ?_⟩
        dsimp [D]
        rw [Rat.cast_def]
        have hne : ((q 0).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (q 0).pos)
        push_cast
        field_simp [hne]
      · refine ⟨(q 1).num * ((q 0).den : ℤ) * ((q 2).den : ℤ), ?_⟩
        dsimp [D]
        rw [Rat.cast_def]
        have hne : ((q 1).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (q 1).pos)
        push_cast
        field_simp [hne]
      · refine ⟨(q 2).num * ((q 0).den : ℤ) * ((q 1).den : ℤ), ?_⟩
        dsimp [D]
        rw [Rat.cast_def]
        have hne : ((q 2).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (q 2).pos)
        push_cast
        field_simp [hne]
    obtain ⟨z0, hz0⟩ := hq_int 0
    obtain ⟨z1, hz1⟩ := hq_int 1
    obtain ⟨z2, hz2⟩ := hq_int 2
    rw [Fin.sum_univ_three] at hq
    have hlin : (z0 : ℝ) * triAngle T 0 + (z1 : ℝ) * triAngle T 1 + (z2 : ℝ) * triAngle T 2 = 0 := by
      rw [← hz0, ← hz1, ← hz2]
      linear_combination (D : ℝ) * hq
    obtain ⟨h0, h1, h2⟩ := hind z0 z1 z2 hlin
    ext j
    have hD_ne : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hD_pos)
    have hjR : (q j : ℝ) = 0 := by
      fin_cases j
      · rw [h0, Int.cast_zero] at hz0; exact (mul_eq_zero.mp hz0).resolve_left hD_ne
      · rw [h1, Int.cast_zero] at hz1; exact (mul_eq_zero.mp hz1).resolve_left hD_ne
      · rw [h2, Int.cast_zero] at hz2; exact (mul_eq_zero.mp hz2).resolve_left hD_ne
    exact Rat.cast_eq_zero.mp hjR
  let M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun j k => (vCount (T.points j) k : ℚ)
  have hM_det : M.det ≠ 0 := by
    intro hdet
    have hdetT : M.transpose.det = 0 := by rw [Matrix.det_transpose, hdet]
    obtain ⟨c, hc_ne, hc_mul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
    have hsum0 : ∑ j : Fin 3, (c j : ℝ) * triAngle T j = 0 := by
      have h1 : ∀ j : Fin 3, (c j : ℝ) * triAngle T j =
          ∑ k : Fin 3, (c j : ℝ) * ((M j k : ℚ) : ℝ) * θ k := by
        intro j
        rw [← (hcorner_eq j).2.2, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [M, mul_assoc]
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hcol : ∑ j : Fin 3, (c j : ℝ) * ((M j k : ℚ) : ℝ) = 0 := by
        have hk := congrFun hc_mul k
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hk
        have hkR : (((∑ j : Fin 3, M j k * c j : ℚ)) : ℝ) = 0 := by rw [hk, Rat.cast_zero]
        push_cast at hkR
        simpa [mul_comm] using hkR
      rw [← Finset.sum_mul, hcol, zero_mul]
    exact hc_ne (hind_Q c hsum0)
  have hθ_ind : ∀ z : Fin 3 → ℤ, (∑ k : Fin 3, (z k : ℝ) * θ k = 0) → ∀ k, z k = 0 := by
    intro z hz
    let q : Fin 3 → ℚ := fun k => (z k : ℚ)
    let N : Matrix (Fin 3) (Fin 3) ℚ := M⁻¹
    have hNM : N * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM_det)
    have hθ_from_T : ∀ k : Fin 3, θ k = ∑ j : Fin 3, ((N k j : ℚ) : ℝ) * triAngle T j := by
      intro k
      have h1 : ∑ j : Fin 3, ((N k j : ℚ) : ℝ) * triAngle T j =
          ∑ l : Fin 3, (∑ j : Fin 3, ((N k j : ℚ) : ℝ) * ((M j l : ℚ) : ℝ)) * θ l := by
        have hstep : ∀ j : Fin 3, ((N k j : ℚ) : ℝ) * triAngle T j =
            ∑ l : Fin 3, ((N k j : ℚ) : ℝ) * ((M j l : ℚ) : ℝ) * θ l := by
          intro j
          rw [← (hcorner_eq j).2.2, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          simp [M, mul_assoc]
        simp_rw [hstep]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_mul]
      rw [h1]
      have hδ : ∀ l : Fin 3, ∑ j : Fin 3, ((N k j : ℚ) : ℝ) * ((M j l : ℚ) : ℝ) =
          if k = l then 1 else 0 := by
        intro l
        have hentry := congrFun (congrFun hNM k) l
        simp only [Matrix.mul_apply, Matrix.one_apply] at hentry
        have hentryR : ((∑ j : Fin 3, N k j * M j l : ℚ) : ℝ) =
            ((if k = l then (1 : ℚ) else 0 : ℚ) : ℝ) :=
          congrArg Rat.cast hentry
        push_cast at hentryR
        simpa [apply_ite] using hentryR
      simp_rw [hδ]
      simp
    let w : Fin 3 → ℚ := fun j => ∑ k : Fin 3, q k * N k j
    have hw_sum : ∑ j : Fin 3, (w j : ℝ) * triAngle T j = 0 := by
      have hrew : ∑ j : Fin 3, (w j : ℝ) * triAngle T j =
          ∑ k : Fin 3, (q k : ℝ) * (∑ j : Fin 3, ((N k j : ℚ) : ℝ) * triAngle T j) := by
        have hstep : ∀ j : Fin 3, (w j : ℝ) * triAngle T j =
            ∑ k : Fin 3, (q k : ℝ) * ((N k j : ℚ) : ℝ) * triAngle T j := by
          intro j
          dsimp [w]
          push_cast
          rw [Finset.sum_mul]
        simp_rw [hstep]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [hrew]
      simp_rw [← hθ_from_T]
      simpa [q] using hz
    have hw0 : w = 0 := hind_Q w hw_sum
    intro k
    have hqk : q k = 0 := by
      have hmul : ∑ j : Fin 3, w j * M j k = q k := by
        simp only [w, Finset.sum_mul]
        rw [Finset.sum_comm]
        have hinner : ∀ l : Fin 3, ∑ j : Fin 3, q l * N l j * M j k =
            q l * (∑ j : Fin 3, N l j * M j k) := by
          intro l
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
        simp_rw [hinner]
        have hδ : ∀ l : Fin 3, ∑ j : Fin 3, N l j * M j k = if l = k then 1 else 0 := by
          intro l
          have := congrFun (congrFun hNM l) k
          simpa [Matrix.mul_apply, Matrix.one_apply] using this
        simp_rw [hδ]
        simp
      rw [← hmul, hw0]
      simp
    exact Int.cast_eq_zero.mp hqk
  let corners : Finset ℝ² := Finset.univ.image T.points
  let V_all : Finset ℝ² :=
    corners ∪ Finset.univ.biUnion (fun i : Fin n => Finset.univ.image (Ts i).points)
  let V_nc : Finset ℝ² := V_all \ corners
  have hdeg_eq : ∀ p : ℝ²,
      (Finset.univ.filter fun i : Fin n => p ∈ Finset.univ.image (Ts i).points).card =
      ∑ k : Fin 3, vCount p k := by
    intro p
    have hsplit : (Finset.univ.filter fun i : Fin n => p ∈ Finset.univ.image (Ts i).points) =
        Finset.univ.biUnion (fun k : Fin 3 =>
          Finset.univ.filter fun i : Fin n => (Ts i).points k = p) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_biUnion]
    have hpw : (↑(Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint
        (fun k : Fin 3 => Finset.univ.filter fun i : Fin n => (Ts i).points k = p) := by
      intro k₁ _ k₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro i h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne ((Ts i).independent.injective (h1.trans h2.symm))
    rw [hsplit, Finset.card_biUnion hpw]
  have hnc_vCount : ∀ p ∈ V_nc, ∀ k : Fin 3, vCount p k = 1 := by
    intro p hp
    have hp_all : p ∈ V_all := (Finset.mem_sdiff.mp hp).1
    have hp_nc : p ∉ corners := (Finset.mem_sdiff.mp hp).2
    have hex_tile : ∃ i : Fin n, ∃ k : Fin 3, (Ts i).points k = p := by
      simp only [V_all, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_image] at hp_all
      exact hp_all.resolve_left hp_nc
    rcases hex_tile with ⟨i_p, k_p, hik_p⟩
    have hp_T : p ∈ T.closedInterior := by
      rw [← hunion]
      exact Set.mem_iUnion.mpr ⟨i_p, hik_p ▸ (Ts i_p).point_mem_closedInterior k_p⟩
    have hp_not_pt : ∀ j : Fin 3, p ≠ T.points j := fun j h =>
      hp_nc (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm⟩)
    have hT_ang : localAngle T p = Real.pi ∨ localAngle T p = 2 * Real.pi := by
      unfold localAngle
      simp only [hp_T, not_true_eq_false, ↓reduceIte, hp_not_pt 0, hp_not_pt 1, hp_not_pt 2]
      by_cases hint : p ∈ T.interior
      · right; simp [hint]
      · left; simp [hint]
    have hsum_pos : 0 < ∑ k : Fin 3, (vCount p k : ℝ) * θ k := by
      have hmem : i_p ∈ Finset.univ.filter fun i : Fin n => (Ts i).points k_p = p := by
        simp [hik_p]
      have hcard_pos : 0 < vCount p k_p := Finset.card_pos.mpr ⟨i_p, hmem⟩
      have hterm_pos : 0 < (vCount p k_p : ℝ) * θ k_p :=
        mul_pos (by exact_mod_cast hcard_pos) (hθ_pos k_p)
      have hle : (vCount p k_p : ℝ) * θ k_p ≤ ∑ k : Fin 3, (vCount p k : ℝ) * θ k :=
        Finset.single_le_sum (fun k _ => mul_nonneg (Nat.cast_nonneg _) (le_of_lt (hθ_pos k)))
          (Finset.mem_univ k_p)
      linarith
    have hd := hlocal_decomp p
    have hm_exists : ∃ m : ℤ, (m = 1 ∨ m = 2) ∧
        ∑ k : Fin 3, (vCount p k : ℝ) * θ k = (m : ℝ) * Real.pi := by
      rcases hT_ang with hpi | h2pi
      · rw [hpi] at hd
        let m : ℤ := 1 - (eCount p : ℤ) - 2 * (iCount p : ℤ)
        have hmeq : ∑ k : Fin 3, (vCount p k : ℝ) * θ k = (m : ℝ) * Real.pi := by
          dsimp [m]; push_cast; linarith
        have hm_pos : 0 < (m : ℝ) := by nlinarith [Real.pi_pos]
        have hm_le : m ≤ 1 := by dsimp [m]; omega
        have hm1 : m = 1 := by
          have : (0 : ℤ) < m := Int.cast_pos.mp hm_pos
          omega
        exact ⟨m, Or.inl hm1, hmeq⟩
      · rw [h2pi] at hd
        let m : ℤ := 2 - (eCount p : ℤ) - 2 * (iCount p : ℤ)
        have hmeq : ∑ k : Fin 3, (vCount p k : ℝ) * θ k = (m : ℝ) * Real.pi := by
          dsimp [m]; push_cast; linarith
        have hm_pos : 0 < (m : ℝ) := by nlinarith [Real.pi_pos]
        have hm_le : m ≤ 2 := by dsimp [m]; omega
        have hm12 : m = 1 ∨ m = 2 := by
          have : (0 : ℤ) < m := Int.cast_pos.mp hm_pos
          omega
        exact ⟨m, hm12, hmeq⟩
    rcases hm_exists with ⟨m, hm12, hmeq⟩
    have hdiff0 : ∑ k : Fin 3, (((vCount p k : ℤ) - m : ℤ) : ℝ) * θ k = 0 := by
      rw [Fin.sum_univ_three] at hmeq ⊢
      push_cast
      linear_combination hmeq - (m : ℝ) * hθ_sum
    have hv_eq : ∀ k : Fin 3, (vCount p k : ℤ) = m := fun k =>
      sub_eq_zero.mp (hθ_ind (fun k => (vCount p k : ℤ) - m) hdiff0 k)
    rcases hm12 with rfl | rfl
    · intro k; exact Int.ofNat.inj (hv_eq k)
    · exfalso
      have hdeg6 : (Finset.univ.filter fun i : Fin n => p ∈ Finset.univ.image (Ts i).points).card = 6 := by
        rw [hdeg_eq, Fin.sum_univ_three]
        have h0 : vCount p 0 = 2 := Int.ofNat.inj (hv_eq 0)
        have h1 : vCount p 1 = 2 := Int.ofNat.inj (hv_eq 1)
        have h2 : vCount p 2 = 2 := Int.ofNat.inj (hv_eq 2)
        omega
      have hle : (Finset.univ.filter fun i : Fin n => p ∈ Finset.univ.image (Ts i).points).card ≤ n := by
        simpa using Finset.card_le_univ (Finset.univ.filter fun i : Fin n =>
          p ∈ Finset.univ.image (Ts i).points)
      omega
  have hcol_sum : ∀ k : Fin 3,
      (∑ j : Fin 3, vCount (T.points j) k) + V_nc.card = n := by
    intro k
    have hpart : ∑ p ∈ V_all, vCount p k = n := by
      have hcard := Finset.card_eq_sum_card_fiberwise
        (f := fun i : Fin n => (Ts i).points k) (s := Finset.univ) (t := V_all)
        (fun i _ =>
          Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩⟩))
      simpa [vCount] using hcard.symm
    have hunion_all : corners ∪ V_nc = V_all := Finset.union_sdiff_of_subset Finset.subset_union_left
    have hdisj_all : Disjoint corners V_nc := Finset.disjoint_sdiff
    rw [← hunion_all, Finset.sum_union hdisj_all] at hpart
    have hsum_corners : ∑ p ∈ corners, vCount p k = ∑ j : Fin 3, vCount (T.points j) k :=
      Finset.sum_image (fun j₁ _ j₂ _ h => T.independent.injective h)
    have hsum_nc : ∑ p ∈ V_nc, vCount p k = V_nc.card := by
      calc ∑ p ∈ V_nc, vCount p k = ∑ p ∈ V_nc, 1 := Finset.sum_congr rfl fun p hp => hnc_vCount p hp k
        _ = V_nc.card := by simp
    rw [hsum_corners, hsum_nc] at hpart
    exact hpart
  have hs_eq_one : ∀ k : Fin 3, ∑ j : Fin 3, vCount (T.points j) k = 1 := by
    let s : ℕ := ∑ j : Fin 3, vCount (T.points j) 0
    have hseq : ∀ k : Fin 3, ∑ j : Fin 3, vCount (T.points j) k = s := by
      intro k
      have h0 := hcol_sum 0
      have hk := hcol_sum k
      omega
    have hpi : Real.pi = (s : ℝ) * Real.pi := by
      calc Real.pi = triAngle T 0 + triAngle T 1 + triAngle T 2 := (triAngle_sum T).symm
        _ = ∑ j : Fin 3, triAngle T j := (Fin.sum_univ_three _).symm
        _ = ∑ j : Fin 3, ∑ k : Fin 3, (vCount (T.points j) k : ℝ) * θ k :=
            Finset.sum_congr rfl fun j _ => (hcorner_eq j).2.2.symm
        _ = ∑ k : Fin 3, (∑ j : Fin 3, (vCount (T.points j) k : ℝ)) * θ k := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
        _ = ∑ k : Fin 3, (s : ℝ) * θ k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            have hk := hseq k
            have hkR : (∑ j : Fin 3, (vCount (T.points j) k : ℝ)) = (s : ℝ) := by exact_mod_cast hk
            rw [hkR]
        _ = (s : ℝ) * (θ 0 + θ 1 + θ 2) := by rw [← Finset.mul_sum, Fin.sum_univ_three]
        _ = (s : ℝ) * Real.pi := by rw [hθ_sum]
    have hs1 : (s : ℝ) = 1 := by nlinarith [Real.pi_pos]
    have hs1' : s = 1 := Nat.cast_eq_one.mp hs1
    intro k; rw [hseq k, hs1']
  have hVnc_card : V_nc.card = n - 1 := by
    have h0 := hcol_sum 0
    have hs := hs_eq_one 0
    omega
  have hdeg_nc : ∀ p ∈ V_nc,
      (Finset.univ.filter fun i : Fin n => p ∈ Finset.univ.image (Ts i).points).card = 3 := by
    intro p hp
    rw [hdeg_eq, Fin.sum_univ_three, hnc_vCount p hp 0, hnc_vCount p hp 1, hnc_vCount p hp 2]
  rcases hn with rfl | rfl | rfl
  · -- Case n = 2
    have hcard1 : V_nc.card = 1 := hVnc_card
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < V_nc.card)
    have h3 := hdeg_nc p hp
    have hle : (Finset.univ.filter fun i : Fin 2 => p ∈ Finset.univ.image (Ts i).points).card ≤ 2 := by
      simpa using Finset.card_le_univ (Finset.univ.filter fun i : Fin 2 =>
        p ∈ Finset.univ.image (Ts i).points)
    omega
  · -- Case n = 3
    have hcard2 : V_nc.card = 2 := hVnc_card
    obtain ⟨p₁, p₂, hp12, hVnc_eq⟩ := Finset.card_eq_two.mp hcard2
    have hp1 : p₁ ∈ V_nc := by rw [hVnc_eq]; simp
    have hp2 : p₂ ∈ V_nc := by rw [hVnc_eq]; simp
    have hall1 : ∀ i : Fin 3, p₁ ∈ Set.range (Ts i).points := by
      have hcard := hdeg_nc p₁ hp1
      have hfull : (Finset.univ.filter fun i : Fin 3 => p₁ ∈ Finset.univ.image (Ts i).points) =
          Finset.univ := Finset.eq_univ_of_card _ (by simpa using hcard)
      intro i
      have hi : i ∈ Finset.univ.filter fun i : Fin 3 => p₁ ∈ Finset.univ.image (Ts i).points := by
        rw [hfull]; exact Finset.mem_univ i
      have himg := (Finset.mem_filter.mp hi).2
      rcases Finset.mem_image.mp himg with ⟨k, _, hk⟩
      exact ⟨k, hk⟩
    have hall2 : ∀ i : Fin 3, p₂ ∈ Set.range (Ts i).points := by
      have hcard := hdeg_nc p₂ hp2
      have hfull : (Finset.univ.filter fun i : Fin 3 => p₂ ∈ Finset.univ.image (Ts i).points) =
          Finset.univ := Finset.eq_univ_of_card _ (by simpa using hcard)
      intro i
      have hi : i ∈ Finset.univ.filter fun i : Fin 3 => p₂ ∈ Finset.univ.image (Ts i).points := by
        rw [hfull]; exact Finset.mem_univ i
      have himg := (Finset.mem_filter.mp hi).2
      rcases Finset.mem_image.mp himg with ⟨k, _, hk⟩
      exact ⟨k, hk⟩
    have hthird : ∀ i : Fin 3, ∃ r : ℝ², r ∈ Set.range (Ts i).points ∧
        cross (p₂ - p₁) (r - p₁) ≠ 0 := by
      intro i
      rcases hall1 i with ⟨k₁, hk₁⟩
      rcases hall2 i with ⟨k₂, hk₂⟩
      have hk12 : k₁ ≠ k₂ := fun h => hp12 (by rw [← hk₁, ← hk₂, h])
      have hex3 : ∃ k₃ : Fin 3, k₃ ≠ k₁ ∧ k₃ ≠ k₂ := by
        fin_cases k₁ <;> fin_cases k₂ <;> simp at hk12 ⊢
        · exact ⟨2, by decide, by decide⟩
        · exact ⟨1, by decide, by decide⟩
        · exact ⟨2, by decide, by decide⟩
        · exact ⟨0, by decide, by decide⟩
        · exact ⟨1, by decide, by decide⟩
        · exact ⟨0, by decide, by decide⟩
      rcases hex3 with ⟨k₃, h31, h32⟩
      refine ⟨(Ts i).points k₃, ⟨k₃, rfl⟩, ?_⟩
      rw [← hk₁, ← hk₂]
      exact fin3_cross_ne_zero (Ts i) hk12 h31.symm h32.symm
    choose r hr_mem hr_ne using hthird
    have hpair : ∃ i j : Fin 3, i ≠ j ∧
        0 < cross (p₂ - p₁) (r i - p₁) * cross (p₂ - p₁) (r j - p₁) := by
      rcases lt_or_gt_of_ne (hr_ne 0) with h0 | h0 <;>
      rcases lt_or_gt_of_ne (hr_ne 1) with h1 | h1 <;>
      rcases lt_or_gt_of_ne (hr_ne 2) with h2 | h2
      · exact ⟨0, 1, by decide, mul_pos_of_neg_of_neg h0 h1⟩
      · exact ⟨0, 1, by decide, mul_pos_of_neg_of_neg h0 h1⟩
      · exact ⟨0, 2, by decide, mul_pos_of_neg_of_neg h0 h2⟩
      · exact ⟨1, 2, by decide, mul_pos h1 h2⟩
      · exact ⟨1, 2, by decide, mul_pos_of_neg_of_neg h1 h2⟩
      · exact ⟨0, 2, by decide, mul_pos h0 h2⟩
      · exact ⟨0, 1, by decide, mul_pos h0 h1⟩
      · exact ⟨0, 1, by decide, mul_pos h0 h1⟩
    rcases hpair with ⟨i, j, hij, hside⟩
    exact not_disjoint_of_shared_edge_same_side (hall1 i) (hall2 i) (hr_mem i)
      (hall1 j) (hall2 j) (hr_mem j) hside (hdisj hij)
  · -- Case n = 5
    have hrow_pos : ∀ j : Fin 3, 1 ≤ ∑ k : Fin 3, vCount (T.points j) k := by
      intro j
      by_contra h0
      have hzero : ∑ k : Fin 3, vCount (T.points j) k = 0 := by omega
      have hval : ∀ k : Fin 3, vCount (T.points j) k = 0 := fun k => by
        rw [Fin.sum_univ_three] at hzero
        match k with
        | 0 => omega
        | 1 => omega
        | 2 => omega
      have hce := (hcorner_eq j).2.2
      simp_rw [hval] at hce
      simp at hce
      linarith [triAngle_pos T j]
    have hrow_one : ∀ j : Fin 3, ∑ k : Fin 3, vCount (T.points j) k = 1 := by
      have htot : ∑ j : Fin 3, ∑ k : Fin 3, vCount (T.points j) k = 3 := by
        rw [Finset.sum_comm]
        simp_rw [hs_eq_one]
        simp
      rw [Fin.sum_univ_three] at htot
      intro j
      match j with
      | 0 => linarith [hrow_pos 0, hrow_pos 1, hrow_pos 2]
      | 1 => linarith [hrow_pos 0, hrow_pos 1, hrow_pos 2]
      | 2 => linarith [hrow_pos 0, hrow_pos 1, hrow_pos 2]
    have huniq_corner : ∀ j : Fin 3, ∃ i₀ : Fin 5,
        T.points j ∈ Set.range (Ts i₀).points ∧
        ∀ i : Fin 5, i ≠ i₀ → T.points j ∉ (Ts i).closedInterior := by
      intro j
      have hdeg1 : (Finset.univ.filter fun i : Fin 5 =>
          T.points j ∈ Finset.univ.image (Ts i).points).card = 1 := by
        rw [hdeg_eq, hrow_one j]
      obtain ⟨i₀, hi₀_eq⟩ := Finset.card_eq_one.mp hdeg1
      have hi₀_mem : T.points j ∈ Finset.univ.image (Ts i₀).points := by
        have : i₀ ∈ Finset.univ.filter fun i : Fin 5 =>
            T.points j ∈ Finset.univ.image (Ts i).points := by rw [hi₀_eq]; simp
        exact (Finset.mem_filter.mp this).2
      rcases Finset.mem_image.mp hi₀_mem with ⟨k, _, hk⟩
      refine ⟨i₀, ⟨k, hk⟩, fun i hi hcl => ?_⟩
      have hnotv : ∀ k' : Fin 3, (Ts i).points k' ≠ T.points j := by
        intro k' hk'
        have him : i ∈ Finset.univ.filter fun i : Fin 5 =>
            T.points j ∈ Finset.univ.image (Ts i).points :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, Finset.mem_image.mpr ⟨k', Finset.mem_univ k', hk'⟩⟩
        rw [hi₀_eq, Finset.mem_singleton] at him
        exact hi him
      by_cases hint : T.points j ∈ (Ts i).interior
      · have hpos : 0 < iCount (T.points j) := Finset.card_pos.mpr ⟨i, by simp [hint]⟩
        have h0 := (hcorner_eq j).2.1
        omega
      · have hpos : 0 < eCount (T.points j) :=
          Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcl, hint, hnotv⟩⟩
        have h0 := (hcorner_eq j).1
        omega
    choose cTile hcTile_mem hcTile_uniq using huniq_corner
    have hcTile_inj : Function.Injective cTile := by
      intro j₁ j₂ heq
      by_contra hne
      have hex3 : ∃ j₃ : Fin 3, j₃ ≠ j₁ ∧ j₃ ≠ j₂ := by
        fin_cases j₁ <;> fin_cases j₂ <;> simp at hne ⊢
        · exact ⟨2, by decide, by decide⟩
        · exact ⟨1, by decide, by decide⟩
        · exact ⟨2, by decide, by decide⟩
        · exact ⟨0, by decide, by decide⟩
        · exact ⟨1, by decide, by decide⟩
        · exact ⟨0, by decide, by decide⟩
      rcases hex3 with ⟨j₃, h31, h32⟩
      obtain ⟨p₁, q₁, -, -, hp1_b, hp1_a, hq1_a, hq1_b, himg1⟩ :=
        corner_tile_edges hunion hne h31.symm h32.symm (hcTile_uniq j₁) (hcTile_mem j₁)
      obtain ⟨p₂, q₂, -, -, hp2_b, hp2_a, hq2_a, hq2_b, himg2⟩ :=
        corner_tile_edges hunion (Ne.symm hne) h32.symm h31.symm (hcTile_uniq j₂) (hcTile_mem j₂)
      rw [← heq] at himg2
      have hv2_in : T.points j₂ ∈ ({T.points j₁, p₁, q₁} : Finset ℝ²) := by
        rw [← himg1, heq]
        rcases hcTile_mem j₂ with ⟨k, hk⟩
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩
      have hv1_in : T.points j₁ ∈ ({T.points j₂, p₂, q₂} : Finset ℝ²) := by
        rw [← himg2]
        rcases hcTile_mem j₁ with ⟨k, hk⟩
        exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩
      have hp1_eq : p₁ = T.points j₂ := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv2_in
        rcases hv2_in with h | h | h
        · exact False.elim (hne (T.independent.injective h.symm))
        · exact h.symm
        · exfalso
          rw [← h] at hq1_a
          rw [bary_point] at hq1_a
          simp at hq1_a
      have hp2_eq : p₂ = T.points j₁ := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv1_in
        rcases hv1_in with h | h | h
        · exact False.elim (hne (T.independent.injective h))
        · exact h.symm
        · exfalso
          rw [← h] at hq2_a
          rw [bary_point] at hq2_a
          simp at hq2_a
      have hq_eq : q₁ = q₂ := by
        have hq1_in : q₁ ∈ ({T.points j₂, T.points j₁, q₂} : Finset ℝ²) := by
          rw [← hp2_eq, ← himg2, himg1]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq1_in
        rcases hq1_in with rfl | rfl | h
        · rw [bary_point] at hq1_a; simp at hq1_a
        · rw [bary_point] at hq1_b; simp [h31] at hq1_b
        · exact h
      have hq1_v3 : q₁ = T.points j₃ := by
        have hq1_T : q₁ ∈ T.closedInterior := by
          have hmem : q₁ ∈ Finset.univ.image (Ts (cTile j₁)).points := by rw [himg1]; simp
          rcases Finset.mem_image.mp hmem with ⟨k, _, hk⟩
          rw [← hunion]; exact Set.mem_iUnion.mpr ⟨cTile j₁, hk ▸ (Ts (cTile j₁)).point_mem_closedInterior k⟩
        have hsum := bary_sum T q₁
        rw [Fin.sum_univ_three] at hsum
        rw [← hq_eq] at hq2_a
        have hperm := fin3_sum_perm (bary T q₁) hne h31.symm h32.symm
        have h3 : bary T q₁ j₃ = 1 := by linarith
        exact fin3_bary_eq_point T h3 ((mem_closedInterior_iff_bary T q₁).mp hq1_T)
      have hsame_verts : Finset.univ.image (Ts (cTile j₁)).points = Finset.univ.image T.points := by
        rw [himg1, hp1_eq, hq1_v3, fin3_img_eq T.points hne h31.symm h32.symm]
      have hint_eq : (Ts (cTile j₁)).interior = T.interior := interior_eq_of_same_vertices hsame_verts
      have hex_other : ∃ i' : Fin 5, i' ≠ cTile j₁ := by
        by_cases h0 : (0 : Fin 5) = cTile j₁
        · exact ⟨1, by rw [← h0]; decide⟩
        · exact ⟨0, h0⟩
      rcases hex_other with ⟨i', hi'⟩
      obtain ⟨x, hx⟩ := interior_nonempty (Ts i')
      have hxT : x ∈ T.interior :=
        sub_triangle_interior_subset (fun y hy => by rw [← hunion]; exact Set.mem_iUnion.mpr ⟨i', hy⟩) hx
      rw [← hint_eq] at hxT
      exact Set.disjoint_left.mp (hdisj hi') hx hxT
    let C : Finset (Fin 5) := Finset.univ.image cTile
    have hC_card : C.card = 3 := by
      rw [Finset.card_image_of_injective _ hcTile_inj]; simp
    let R : Finset (Fin 5) := Finset.univ \ C
    have hR_card : R.card = 2 := by
      dsimp [R]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hC_card]
    obtain ⟨i₃, i₄, hi34, hR_eq⟩ := Finset.card_eq_two.mp hR_card
    have hi3_R : i₃ ∈ R := by rw [hR_eq]; simp
    have hi4_R : i₄ ∈ R := by rw [hR_eq]; simp
    have hR_sub_nc : ∀ i ∈ R, Finset.univ.image (Ts i).points ⊆ V_nc := by
      intro i hi p hp
      rw [Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · simp only [V_all, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact Or.inr ⟨i, hp⟩
      · intro hcor
        rcases Finset.mem_image.mp hcor with ⟨j, _, hj⟩
        have hne : i ≠ cTile j := by
          intro heq
          have hiC : i ∈ C := Finset.mem_image.mpr ⟨j, Finset.mem_univ j, heq.symm⟩
          exact (Finset.mem_sdiff.mp hi).2 hiC
        rcases Finset.mem_image.mp hp with ⟨k, _, hk⟩
        have hcl : T.points j ∈ (Ts i).closedInterior := by
          rw [hj, ← hk]; exact (Ts i).point_mem_closedInterior k
        exact hcTile_uniq j i hne hcl
    let S₃ : Finset ℝ² := Finset.univ.image (Ts i₃).points
    let S₄ : Finset ℝ² := Finset.univ.image (Ts i₄).points
    have hS3_sub : S₃ ⊆ V_nc := hR_sub_nc i₃ hi3_R
    have hS4_sub : S₄ ⊆ V_nc := hR_sub_nc i₄ hi4_R
    have hS3_card : S₃.card = 3 := by
      rw [Finset.card_image_of_injective _ (Ts i₃).independent.injective]; simp
    have hS4_card : S₄.card = 3 := by
      rw [Finset.card_image_of_injective _ (Ts i₄).independent.injective]; simp
    have hS34_ne : S₃ ≠ S₄ := by
      intro heq
      have hint := interior_eq_of_same_vertices heq
      obtain ⟨x, hx⟩ := interior_nonempty (Ts i₃)
      exact Set.disjoint_left.mp (hdisj hi34) hx (hint ▸ hx)
    have hVnc4 : V_nc.card = 4 := hVnc_card
    have hunion_le : (S₃ ∪ S₄).card ≤ 4 :=
      hVnc4 ▸ Finset.card_le_card (Finset.union_subset hS3_sub hS4_sub)
    have hunion_gt3 : 3 < (S₃ ∪ S₄).card := by
      have hle : S₃.card ≤ (S₃ ∪ S₄).card := Finset.card_le_card Finset.subset_union_left
      refine lt_of_le_of_ne (hS3_card ▸ hle) ?_
      intro heq
      have hS3_eq : S₃ = S₃ ∪ S₄ := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
      have hS4_sub_S3 : S₄ ⊆ S₃ := by rw [hS3_eq]; exact Finset.subset_union_right
      exact hS34_ne (Finset.eq_of_subset_of_card_le hS4_sub_S3 (by omega)).symm
    have hunion_card : (S₃ ∪ S₄).card = 4 := by omega
    have hunion_eq_Vnc : S₃ ∪ S₄ = V_nc :=
      Finset.eq_of_subset_of_card_le (Finset.union_subset hS3_sub hS4_sub) (by omega)
    have hinter_card : (S₃ ∩ S₄).card = 2 := by
      have h := Finset.card_union_add_card_inter S₃ S₄
      omega
    obtain ⟨p₁, p₂, hp12, hinter_eq⟩ := Finset.card_eq_two.mp hinter_card
    have hp1_S3 : p₁ ∈ S₃ := (Finset.mem_inter.mp (by rw [hinter_eq]; simp)).1
    have hp1_S4 : p₁ ∈ S₄ := (Finset.mem_inter.mp (by rw [hinter_eq]; simp)).2
    have hp2_S3 : p₂ ∈ S₃ := (Finset.mem_inter.mp (by rw [hinter_eq]; simp)).1
    have hp2_S4 : p₂ ∈ S₄ := (Finset.mem_inter.mp (by rw [hinter_eq]; simp)).2
    have hS3_sdiff_card : (S₃ \ S₄).card = 1 := by
      have := Finset.card_sdiff_add_card_inter S₃ S₄
      omega
    have hS4_sdiff_card : (S₄ \ S₃).card = 1 := by
      have h := Finset.card_sdiff_add_card_inter S₄ S₃
      rw [Finset.inter_comm] at h
      omega
    obtain ⟨p₃, hp3_eq⟩ := Finset.card_eq_one.mp hS3_sdiff_card
    obtain ⟨p₄, hp4_eq⟩ := Finset.card_eq_one.mp hS4_sdiff_card
    have hp3_S3 : p₃ ∈ S₃ := (Finset.mem_sdiff.mp (by rw [hp3_eq]; simp)).1
    have hp3_not_S4 : p₃ ∉ S₄ := (Finset.mem_sdiff.mp (by rw [hp3_eq]; simp)).2
    have hp4_S4 : p₄ ∈ S₄ := (Finset.mem_sdiff.mp (by rw [hp4_eq]; simp)).1
    have hp4_not_S3 : p₄ ∉ S₃ := (Finset.mem_sdiff.mp (by rw [hp4_eq]; simp)).2
    let degC (p : ℝ²) : ℕ := (C.filter fun i : Fin 5 => p ∈ Finset.univ.image (Ts i).points).card
    let degR (p : ℝ²) : ℕ := (R.filter fun i : Fin 5 => p ∈ Finset.univ.image (Ts i).points).card
    have hdeg_split : ∀ p ∈ V_nc, degC p + degR p = 3 := by
      intro p hp
      have hpart : Finset.univ = C ∪ R := (Finset.union_sdiff_of_subset (Finset.subset_univ C)).symm
      have hdj : Disjoint C R := Finset.disjoint_sdiff
      have h3 := hdeg_nc p hp
      rw [hpart, Finset.filter_union, Finset.card_union_of_disjoint
        (hdj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))] at h3
      exact h3
    have hdegR_eq : ∀ p : ℝ², degR p = (if p ∈ S₃ then 1 else 0) + (if p ∈ S₄ then 1 else 0) := by
      intro p
      dsimp only [degR, S₃, S₄]
      rw [hR_eq]
      exact card_filter_pair hi34 (fun i : Fin 5 => p ∈ Finset.univ.image (Ts i).points)
    have hdegC_p1 : degC p₁ = 1 := by
      have h := hdeg_split p₁ (hS3_sub hp1_S3)
      rw [hdegR_eq, if_pos hp1_S3, if_pos hp1_S4] at h
      omega
    have hdegC_eq1_imp : ∀ p ∈ V_nc, degC p = 1 → p = p₁ ∨ p = p₂ := by
      intro p hp h1
      have hsp := hdeg_split p hp
      rw [hdegR_eq] at hsp
      have hp3 : p ∈ S₃ := by by_contra hn; simp [hn] at hsp; split_ifs at hsp <;> omega
      have hp4 : p ∈ S₄ := by by_contra hn; simp [hn, hp3] at hsp; omega
      have hmem : p ∈ S₃ ∩ S₄ := Finset.mem_inter.mpr ⟨hp3, hp4⟩
      rw [hinter_eq] at hmem
      simpa using hmem
    -- Now extract the corner-tile non-corner edge vertices for each j : Fin 3
    obtain ⟨q01, q02, -, -, hq01_2, hq01_1, hq02_1, hq02_2, himg0⟩ :=
      corner_tile_edges hunion (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2)
        (by decide : (1 : Fin 3) ≠ 2) (hcTile_uniq 0) (hcTile_mem 0)
    obtain ⟨q12, q10, -, -, hq12_0, hq12_2, hq10_2, hq10_0, himg1⟩ :=
      corner_tile_edges hunion (by decide : (1 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 0)
        (by decide : (2 : Fin 3) ≠ 0) (hcTile_uniq 1) (hcTile_mem 1)
    obtain ⟨q20, q21, -, -, hq20_1, hq20_0, hq21_0, hq21_1, himg2⟩ :=
      corner_tile_edges hunion (by decide : (2 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
        (by decide : (0 : Fin 3) ≠ 1) (hcTile_uniq 2) (hcTile_mem 2)
    have hq_in_Vnc : ∀ j : Fin 3, ∀ y ∈ Finset.univ.image (Ts (cTile j)).points,
        y ≠ T.points j → y ∈ V_nc := by
      intro j y hy hne
      rw [Finset.mem_sdiff]
      refine ⟨?_, ?_⟩
      · simp only [V_all, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact Or.inr ⟨cTile j, hy⟩
      · intro hcor
        rcases Finset.mem_image.mp hcor with ⟨j', _, hj'⟩
        by_cases hjj : j' = j
        · exact hne (hj'.symm.trans (congrArg T.points hjj))
        · have hneTile : cTile j ≠ cTile j' := fun h => hjj (hcTile_inj h).symm
          rcases Finset.mem_image.mp hy with ⟨k, _, hk⟩
          have hcl : T.points j' ∈ (Ts (cTile j)).closedInterior := by
            rw [hj', ← hk]; exact (Ts (cTile j)).point_mem_closedInterior k
          exact hcTile_uniq j' (cTile j) hneTile hcl
    have hq_strict : ∀ {j a b : Fin 3} {y : ℝ²},
        j ≠ a → j ≠ b → a ≠ b →
        y ∈ Finset.univ.image (Ts (cTile j)).points →
        bary T y b = 0 → 0 < bary T y a →
        0 < bary T y j ∧ y ∈ V_nc := by
      intro j a b y hja hjb hab hy hyb hya
      have hy_T : y ∈ T.closedInterior := by
        rcases Finset.mem_image.mp hy with ⟨k, _, hk⟩
        rw [← hunion]; exact Set.mem_iUnion.mpr ⟨cTile j, hk ▸ (Ts (cTile j)).point_mem_closedInterior k⟩
      have hnn := (mem_closedInterior_iff_bary T y).mp hy_T
      have hsum := bary_sum T y
      rw [Fin.sum_univ_three] at hsum
      have hy_nej : y ≠ T.points j := by
        rintro rfl
        rw [bary_point] at hya
        simp [hja.symm] at hya
      have hy_Vnc : y ∈ V_nc := hq_in_Vnc j y hy hy_nej
      have hy_nea : y ≠ T.points a := fun h =>
        (Finset.mem_sdiff.mp hy_Vnc).2 (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, h.symm⟩)
      have hyj_pos : 0 < bary T y j := by
        refine lt_of_le_of_ne (hnn j) ?_
        intro h0
        have hperm := fin3_sum_perm (bary T y) hja hjb hab
        have hya1 : bary T y a = 1 := by linarith
        exact hy_nea (fin3_bary_eq_point T hya1 hnn)
      exact ⟨hyj_pos, hy_Vnc⟩
    have hq01_mem : q01 ∈ Finset.univ.image (Ts (cTile 0)).points := by rw [himg0]; simp
    have hq02_mem : q02 ∈ Finset.univ.image (Ts (cTile 0)).points := by rw [himg0]; simp
    have hq12_mem : q12 ∈ Finset.univ.image (Ts (cTile 1)).points := by rw [himg1]; simp
    have hq10_mem : q10 ∈ Finset.univ.image (Ts (cTile 1)).points := by rw [himg1]; simp
    have hq20_mem : q20 ∈ Finset.univ.image (Ts (cTile 2)).points := by rw [himg2]; simp
    have hq21_mem : q21 ∈ Finset.univ.image (Ts (cTile 2)).points := by rw [himg2]; simp
    obtain ⟨hq01_0, hq01_nc⟩ := hq_strict (by decide : (0 : Fin 3) ≠ 1) (by decide) (by decide) hq01_mem hq01_2 hq01_1
    obtain ⟨hq02_0, hq02_nc⟩ := hq_strict (by decide : (0 : Fin 3) ≠ 2) (by decide) (by decide) hq02_mem hq02_1 hq02_2
    obtain ⟨hq12_1, hq12_nc⟩ := hq_strict (by decide : (1 : Fin 3) ≠ 2) (by decide) (by decide) hq12_mem hq12_0 hq12_2
    obtain ⟨hq10_1, hq10_nc⟩ := hq_strict (by decide : (1 : Fin 3) ≠ 0) (by decide) (by decide) hq10_mem hq10_2 hq10_0
    obtain ⟨hq20_2, hq20_nc⟩ := hq_strict (by decide : (2 : Fin 3) ≠ 0) (by decide) (by decide) hq20_mem hq20_1 hq20_0
    obtain ⟨hq21_2, hq21_nc⟩ := hq_strict (by decide : (2 : Fin 3) ≠ 1) (by decide) (by decide) hq21_mem hq21_0 hq21_1
    have hC_eq : C = {cTile 0, cTile 1, cTile 2} := by
      ext i
      simp only [C, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨j, rfl⟩; fin_cases j <;> simp
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
    have hc01 : cTile 0 ≠ cTile 1 := hcTile_inj.ne (by decide)
    have hc02 : cTile 0 ≠ cTile 2 := hcTile_inj.ne (by decide)
    have hc12 : cTile 1 ≠ cTile 2 := hcTile_inj.ne (by decide)
    have hdegC_eval : ∀ y : ℝ²,
        degC y =
          (if y ∈ Finset.univ.image (Ts (cTile 0)).points then 1 else 0) +
          (if y ∈ Finset.univ.image (Ts (cTile 1)).points then 1 else 0) +
          (if y ∈ Finset.univ.image (Ts (cTile 2)).points then 1 else 0) := by
      intro y
      dsimp only [degC]
      rw [hC_eq]
      exact card_filter_triple hc01 hc02 hc12 (fun i : Fin 5 => y ∈ Finset.univ.image (Ts i).points)
    have hsame_edge : ∃ c : Fin 3, bary T p₁ c = 0 ∧ bary T p₂ c = 0 := by
      have hp1_inC : ∃ j : Fin 3, p₁ ∈ Finset.univ.image (Ts (cTile j)).points := by
        have hpos : 0 < degC p₁ := by omega
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
        rcases Finset.mem_filter.mp hi with ⟨hiC, hp1i⟩
        rcases Finset.mem_image.mp hiC with ⟨j, _, rfl⟩
        exact ⟨j, hp1i⟩
      have hp1_not_v : ∀ j : Fin 3, p₁ ≠ T.points j := fun j h =>
        (Finset.mem_sdiff.mp (hS3_sub hp1_S3)).2 (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm⟩)
      have hnot_in_c2 : ∀ y : ℝ², bary T y 2 = 0 → y ∉ Finset.univ.image (Ts (cTile 2)).points := by
        intro y hy2 hy
        rw [himg2] at hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · rw [bary_point] at hy2; simp at hy2
        · linarith
        · linarith
      have hnot_in_c0 : ∀ y : ℝ², bary T y 0 = 0 → y ∉ Finset.univ.image (Ts (cTile 0)).points := by
        intro y hy0 hy
        rw [himg0] at hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · rw [bary_point] at hy0; simp at hy0
        · linarith
        · linarith
      have hnot_in_c1 : ∀ y : ℝ², bary T y 1 = 0 → y ∉ Finset.univ.image (Ts (cTile 1)).points := by
        intro y hy1 hy
        rw [himg1] at hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl | rfl
        · rw [bary_point] at hy1; simp at hy1
        · linarith
        · linarith
      have hpair_edge : ∀ {c : Fin 3} {u v : ℝ²} {i₁ i₂ : Fin 3},
          i₁ ≠ i₂ →
          u ∈ V_nc → v ∈ V_nc →
          bary T u c = 0 → bary T v c = 0 →
          u ∈ Finset.univ.image (Ts (cTile i₁)).points →
          v ∈ Finset.univ.image (Ts (cTile i₂)).points →
          (∀ y, bary T y c = 0 → ∀ j : Fin 3, j ≠ i₁ → j ≠ i₂ →
            y ∉ Finset.univ.image (Ts (cTile j)).points) →
          (u ∈ Finset.univ.image (Ts (cTile i₂)).points → u = v) →
          (v ∈ Finset.univ.image (Ts (cTile i₁)).points → v = u) →
          p₁ = u →
          ∃ c' : Fin 3, bary T p₁ c' = 0 ∧ bary T p₂ c' = 0 := by
        intro c u v i₁ i₂ h12 hu_nc hv_nc huc hvc hu1 hv2 hnot3 hu2_imp hv1_imp hp1_eq
        subst hp1_eq
        have huv_ne : p₁ ≠ v := by
          rintro rfl
          have hd := hdegC_eval p₁
          rw [hdegC_p1] at hd
          rcases fin3_cases i₁ with rfl | rfl | rfl <;> rcases fin3_cases i₂ with rfl | rfl | rfl <;>
            first | exact absurd rfl h12 | (simp only [hu1, hv2, ↓reduceIte] at hd; omega)
        have hv_not1 : v ∉ Finset.univ.image (Ts (cTile i₁)).points := fun h => huv_ne (hv1_imp h).symm
        have hdegv : degC v = 1 := by
          rw [hdegC_eval v]
          rcases fin3_cases i₁ with rfl | rfl | rfl <;> rcases fin3_cases i₂ with rfl | rfl | rfl
          · exact absurd rfl h12
          · simp [hv_not1, hv2, hnot3 v hvc 2 (by decide) (by decide)]
          · simp [hv_not1, hv2, hnot3 v hvc 1 (by decide) (by decide)]
          · simp [hv_not1, hv2, hnot3 v hvc 2 (by decide) (by decide)]
          · exact absurd rfl h12
          · simp [hv_not1, hv2, hnot3 v hvc 0 (by decide) (by decide)]
          · simp [hv_not1, hv2, hnot3 v hvc 1 (by decide) (by decide)]
          · simp [hv_not1, hv2, hnot3 v hvc 0 (by decide) (by decide)]
          · exact absurd rfl h12
        rcases hdegC_eq1_imp v hv_nc hdegv with rfl | rfl
        · exact absurd rfl huv_ne
        · exact ⟨c, huc, hvc⟩
      have h01_imp1 : q01 ∈ Finset.univ.image (Ts (cTile 1)).points → q01 = q10 := by
        intro h; rw [himg1] at h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h | h
        · exfalso; rw [h, bary_point] at hq01_0; simp at hq01_0
        · exfalso; rw [h] at hq01_2; linarith
        · exact h
      have h10_imp0 : q10 ∈ Finset.univ.image (Ts (cTile 0)).points → q10 = q01 := by
        intro h; rw [himg0] at h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h | h
        · exfalso; rw [h, bary_point] at hq10_1; simp at hq10_1
        · exact h
        · exfalso; rw [h] at hq10_2; linarith
      have h12_imp2 : q12 ∈ Finset.univ.image (Ts (cTile 2)).points → q12 = q21 := by
        intro h; rw [himg2] at h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h | h
        · exfalso; rw [h, bary_point] at hq12_1; simp at hq12_1
        · exfalso; rw [h] at hq12_0; linarith
        · exact h
      have h21_imp1 : q21 ∈ Finset.univ.image (Ts (cTile 1)).points → q21 = q12 := by
        intro h; rw [himg1] at h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h | h
        · exfalso; rw [h, bary_point] at hq21_2; simp at hq21_2
        · exact h
        · exfalso; rw [h] at hq21_0; linarith
      have h20_imp0 : q20 ∈ Finset.univ.image (Ts (cTile 0)).points → q20 = q02 := by
        intro h; rw [himg0] at h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h | h
        · exfalso; rw [h, bary_point] at hq20_2; simp at hq20_2
        · exfalso; rw [h] at hq20_1; linarith
        · exact h
      have h02_imp2 : q02 ∈ Finset.univ.image (Ts (cTile 2)).points → q02 = q20 := by
        intro h; rw [himg2] at h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h | h
        · exfalso; rw [h, bary_point] at hq02_0; simp at hq02_0
        · exact h
        · exfalso; rw [h] at hq02_1; linarith
      rcases hp1_inC with ⟨j, hj⟩
      rcases fin3_cases j with rfl | rfl | rfl
      · rw [himg0] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with h | h | h
        · exact absurd h (hp1_not_v 0)
        · exact hpair_edge (c := 2) (by decide) hq01_nc hq10_nc hq01_2 hq10_2 hq01_mem hq10_mem
            (fun y hy k hk0 hk1 => by
              have hk2 : k = 2 := by fin_cases k <;> simp at hk0 hk1 ⊢
              subst hk2; exact hnot_in_c2 y hy)
            h01_imp1 h10_imp0 h
        · exact hpair_edge (c := 1) (by decide) hq02_nc hq20_nc hq02_1 hq20_1 hq02_mem hq20_mem
            (fun y hy k hk0 hk2 => by
              have hk1 : k = 1 := by fin_cases k <;> simp at hk0 hk2 ⊢
              subst hk1; exact hnot_in_c1 y hy)
            h02_imp2 h20_imp0 h
      · rw [himg1] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with h | h | h
        · exact absurd h (hp1_not_v 1)
        · exact hpair_edge (c := 0) (by decide) hq12_nc hq21_nc hq12_0 hq21_0 hq12_mem hq21_mem
            (fun y hy k hk1 hk2 => by
              have hk0 : k = 0 := by fin_cases k <;> simp at hk1 hk2 ⊢
              subst hk0; exact hnot_in_c0 y hy)
            h12_imp2 h21_imp1 h
        · exact hpair_edge (c := 2) (by decide) hq10_nc hq01_nc hq10_2 hq01_2 hq10_mem hq01_mem
            (fun y hy k hk1 hk0 => by
              have hk2 : k = 2 := by fin_cases k <;> simp at hk1 hk0 ⊢
              subst hk2; exact hnot_in_c2 y hy)
            h10_imp0 h01_imp1 h
      · rw [himg2] at hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with h | h | h
        · exact absurd h (hp1_not_v 2)
        · exact hpair_edge (c := 1) (by decide) hq20_nc hq02_nc hq20_1 hq02_1 hq20_mem hq02_mem
            (fun y hy k hk2 hk0 => by
              have hk1 : k = 1 := by fin_cases k <;> simp at hk2 hk0 ⊢
              subst hk1; exact hnot_in_c1 y hy)
            h20_imp0 h02_imp2 h
        · exact hpair_edge (c := 0) (by decide) hq21_nc hq12_nc hq21_0 hq12_0 hq21_mem hq12_mem
            (fun y hy k hk2 hk1 => by
              have hk0 : k = 0 := by fin_cases k <;> simp at hk2 hk1 ⊢
              subst hk0; exact hnot_in_c0 y hy)
            h21_imp1 h12_imp2 h
    rcases hsame_edge with ⟨c, hp1_c, hp2_c⟩
    have hp1_r3 : p₁ ∈ Set.range (Ts i₃).points := by
      rcases Finset.mem_image.mp hp1_S3 with ⟨k, _, hk⟩; exact ⟨k, hk⟩
    have hp2_r3 : p₂ ∈ Set.range (Ts i₃).points := by
      rcases Finset.mem_image.mp hp2_S3 with ⟨k, _, hk⟩; exact ⟨k, hk⟩
    have hp3_r3 : p₃ ∈ Set.range (Ts i₃).points := by
      rcases Finset.mem_image.mp hp3_S3 with ⟨k, _, hk⟩; exact ⟨k, hk⟩
    have hp1_r4 : p₁ ∈ Set.range (Ts i₄).points := by
      rcases Finset.mem_image.mp hp1_S4 with ⟨k, _, hk⟩; exact ⟨k, hk⟩
    have hp2_r4 : p₂ ∈ Set.range (Ts i₄).points := by
      rcases Finset.mem_image.mp hp2_S4 with ⟨k, _, hk⟩; exact ⟨k, hk⟩
    have hp4_r4 : p₄ ∈ Set.range (Ts i₄).points := by
      rcases Finset.mem_image.mp hp4_S4 with ⟨k, _, hk⟩; exact ⟨k, hk⟩
    have hcross_ne : ∀ (Δ : Triangle ℝ ℝ²) {u v w : ℝ²},
        u ≠ v → u ≠ w → v ≠ w →
        u ∈ Set.range Δ.points → v ∈ Set.range Δ.points → w ∈ Set.range Δ.points →
        cross (v - u) (w - u) ≠ 0 := by
      intro Δ u v w huv huw hvw ⟨ku, hku⟩ ⟨kv, hkv⟩ ⟨kw, hkw⟩
      have h1 : ku ≠ kv := fun h => huv (by rw [← hku, ← hkv, h])
      have h2 : ku ≠ kw := fun h => huw (by rw [← hku, ← hkw, h])
      have h3 : kv ≠ kw := fun h => hvw (by rw [← hkv, ← hkw, h])
      rw [← hku, ← hkv, ← hkw]
      exact fin3_cross_ne_zero Δ h1 h2 h3
    have hcr3_ne : cross (p₂ - p₁) (p₃ - p₁) ≠ 0 :=
      hcross_ne (Ts i₃) hp12 (fun h => hp3_not_S4 (h ▸ hp1_S4)) (fun h => hp3_not_S4 (h ▸ hp2_S4))
        hp1_r3 hp2_r3 hp3_r3
    have hcr4_ne : cross (p₂ - p₁) (p₄ - p₁) ≠ 0 :=
      hcross_ne (Ts i₄) hp12 (fun h => hp4_not_S3 (h ▸ hp1_S3)) (fun h => hp4_not_S3 (h ▸ hp2_S3))
        hp1_r4 hp2_r4 hp4_r4
    have hp3_T : p₃ ∈ T.closedInterior := by
      rcases hp3_r3 with ⟨k, hk⟩
      rw [← hunion]; exact Set.mem_iUnion.mpr ⟨i₃, hk ▸ (Ts i₃).point_mem_closedInterior k⟩
    have hp4_T : p₄ ∈ T.closedInterior := by
      rcases hp4_r4 with ⟨k, hk⟩
      rw [← hunion]; exact Set.mem_iUnion.mpr ⟨i₄, hk ▸ (Ts i₄).point_mem_closedInterior k⟩
    have hp3_c_nn : 0 ≤ bary T p₃ c := (mem_closedInterior_iff_bary T p₃).mp hp3_T c
    have hp4_c_nn : 0 ≤ bary T p₄ c := (mem_closedInterior_iff_bary T p₄).mp hp4_T c
    have hside : 0 < cross (p₂ - p₁) (p₃ - p₁) * cross (p₂ - p₁) (p₄ - p₁) := by
      have hex_ab : ∃ a b : Fin 3, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
        fin_cases c
        · exact ⟨1, 2, by decide, by decide, by decide⟩
        · exact ⟨0, 2, by decide, by decide, by decide⟩
        · exact ⟨0, 1, by decide, by decide, by decide⟩
      rcases hex_ab with ⟨a, b, hab, hac, hbc⟩
      let lam : ℝ := bary T p₂ b - bary T p₁ b
      have hlam_ne : lam ≠ 0 := by
        intro h0
        have hb_eq : bary T p₂ b = bary T p₁ b := sub_eq_zero.mp h0
        have hsum1 := bary_sum T p₁
        have hsum2 := bary_sum T p₂
        rw [Fin.sum_univ_three] at hsum1 hsum2
        have ha_eq : bary T p₂ a = bary T p₁ a := by
          have hp1s := fin3_sum_perm (bary T p₁) hab hac hbc
          have hp2s := fin3_sum_perm (bary T p₂) hab hac hbc
          linarith
        have hw_eq : bary T p₂ = bary T p₁ :=
          fin3_fun_eq hab hac hbc ha_eq hb_eq (by linarith)
        apply hp12
        rw [← bary_affineCombination T p₁, ← bary_affineCombination T p₂, hw_eq]
      have hDT : cross (T.points b - T.points a) (T.points c - T.points a) ≠ 0 :=
        hcross_ne T (T.independent.injective.ne hab) (T.independent.injective.ne hac)
          (T.independent.injective.ne hbc) ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, rfl⟩
      let μ : ℝ := lam * cross (T.points b - T.points a) (T.points c - T.points a)
      have hμ_ne : μ ≠ 0 := mul_ne_zero hlam_ne hDT
      have hformula : ∀ x : ℝ², cross (p₂ - p₁) (x - p₁) = μ * bary T x c := by
        intro x
        have hvec : ∀ y : ℝ², y - T.points a =
            bary T y b • (T.points b - T.points a) + bary T y c • (T.points c - T.points a) :=
          fin3_vec_decomp T hab hac hbc
        have hp21 : p₂ - p₁ = lam • (T.points b - T.points a) := by
          have h1 := hvec p₁
          have h2 := hvec p₂
          rw [hp1_c, zero_smul, add_zero] at h1
          rw [hp2_c, zero_smul, add_zero] at h2
          have hsub : p₂ - p₁ = (p₂ - T.points a) - (p₁ - T.points a) := by abel
          rw [hsub, h1, h2]
          apply ext2 <;> (simp only [lam, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring)
        have hxp1 : x - p₁ =
            (bary T x b - bary T p₁ b) • (T.points b - T.points a) +
            bary T x c • (T.points c - T.points a) := by
          have h1 := hvec p₁
          have hx := hvec x
          rw [hp1_c, zero_smul, add_zero] at h1
          have hsub : x - p₁ = (x - T.points a) - (p₁ - T.points a) := by abel
          rw [hsub, h1, hx]
          apply ext2 <;> (simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring)
        rw [hp21, hxp1]
        simp only [μ, cross, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      have hf3 := hformula p₃
      have hf4 := hformula p₄
      have hp3_pos : 0 < bary T p₃ c := lt_of_le_of_ne hp3_c_nn fun h => by
        rw [← h, mul_zero] at hf3; exact hcr3_ne hf3
      have hp4_pos : 0 < bary T p₄ c := lt_of_le_of_ne hp4_c_nn fun h => by
        rw [← h, mul_zero] at hf4; exact hcr4_ne hf4
      rw [hf3, hf4]
      have hμ2 : 0 < μ * μ := mul_self_pos.mpr hμ_ne
      have : (μ * bary T p₃ c) * (μ * bary T p₄ c) = (μ * μ) * (bary T p₃ c * bary T p₄ c) := by ring
      rw [this]
      exact mul_pos hμ2 (mul_pos hp3_pos hp4_pos)
    exact not_disjoint_of_shared_edge_same_side hp1_r3 hp2_r3 hp3_r3 hp1_r4 hp2_r4 hp4_r4
      hside (hdisj hi34)

end Erdos633ExistsSimiliCuttableProof

theorem OMA.solution : type_of% @Erdos633.exists_isSimiliCuttable_iff_ne_zero_two_three_five := by
  obtain ⟨T, hind⟩ := Erdos633ExistsSimiliCuttableProof.exists_angle_indep_triangle
  refine ⟨T, fun n => ⟨fun h => ?_, fun ⟨hn0, hn2, hn3, hn5⟩ =>
    Erdos633ExistsSimiliCuttableProof.isSimiliCuttable_of_ne T hn0 hn2 hn3 hn5⟩⟩
  refine ⟨h.ne_zero, ?_, ?_, ?_⟩
  · intro hn2
    exact Erdos633ExistsSimiliCuttableProof.not_isSimiliCuttable_two_three_five hind (Or.inl hn2) h
  · intro hn3
    exact Erdos633ExistsSimiliCuttableProof.not_isSimiliCuttable_two_three_five hind (Or.inr (Or.inl hn3)) h
  · intro hn5
    exact Erdos633ExistsSimiliCuttableProof.not_isSimiliCuttable_two_three_five hind (Or.inr (Or.inr hn5)) h
