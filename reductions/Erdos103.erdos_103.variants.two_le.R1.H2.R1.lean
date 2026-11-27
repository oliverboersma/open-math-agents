import OMAReductions.R_Erdos103_erdos_103_variants_two_le_R1
import Mathlib

-- Reduction Erdos103.erdos_103.variants.two_le.R1.H2.R1 of step Erdos103.erdos_103.variants.two_le.R1.H2
-- Credit: @tamoghnokandar

/-!
Two further sources of a second minimiser, leaving only a rigid core.

* Plateau: if some separated set of `n+1` points has diameter at most the
  minimal diameter for `n` points, then deleting one point at a time gives
  `n+1` minimisers for `n`.  If they were all congruent, every point would
  have the same sum of squared distances to the others, so the points would
  lie on a circle around their centroid; `H1` says such a set is beaten by a
  fixed competitor, which is then not of this kind itself.
* Sliding: a point `p` of a minimiser can be pushed in a direction `v` as
  soon as `v` does not point towards a unit neighbour and points strictly
  towards every diameter partner.

`H2` is what is left: `n` is a jump of the minimal diameter and every point
of every minimiser is blocked in every direction.
-/

open EuclideanGeometry Filter Finset
open Erdos103
open scoped Classical ENNReal

namespace OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1

/-- For large `n` one fixed separated set of `n` points has smaller diameter
than every separated set of `n` points lying on a circle around its centroid. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ C ∈ separatedSets n, ∀ B ∈ separatedSets n,
    (∃ c : ℝ², ∃ R : ℝ, (∀ x ∈ B, dist x c = R) ∧ ∑ x ∈ B, (x - c) = 0) →
    Metric.diam (C : Set ℝ²) < Metric.diam (B : Set ℝ²)

/-- The rigid core: `n+1` points need a strictly larger diameter, and in every
minimiser every point is blocked in every direction `v`, either by a unit
neighbour on the side of `v` or by a diameter partner not on the side of `v`. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℝ², IsMinimiser n A →
    (∀ B ∈ separatedSets (n + 1),
      Metric.diam (A : Set ℝ²) < Metric.diam (B : Set ℝ²)) →
    (∀ X : Finset ℝ², IsMinimiser n X → ∀ p ∈ X, ∀ v : ℝ², v ≠ 0 →
      (∃ q ∈ X, dist p q = 1 ∧ 0 < inner ℝ v (q - p)) ∨
      (∃ r ∈ X, dist p r = Metric.diam (X : Set ℝ²) ∧ inner ℝ v (r - p) ≤ 0)) →
    ∃ B : Finset ℝ², IsMinimiser n B ∧ ¬ Congruent A B

section Proof

theorem sep_dist {n : ℕ} {B : Finset ℝ²} (hB : B ∈ separatedSets n) {x y : ℝ²}
    (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y) : 1 ≤ dist x y := by
  have hh := hB.2 hx hy hxy
  change (1:ℝ≥0∞) ≤ edist x y at hh
  rwa [edist_dist,← ENNReal.ofReal_one,ENNReal.ofReal_le_ofReal_iff dist_nonneg] at hh

theorem mk_sep {n : ℕ} {B : Finset ℝ²} (hc : B.card = n)
    (h : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → 1 ≤ dist x y) : B ∈ separatedSets n := by
  refine ⟨hc,?_⟩
  intro x hx y hy hxy
  change (1:ℝ≥0∞) ≤ edist x y
  rw [edist_dist,← ENNReal.ofReal_one,ENNReal.ofReal_le_ofReal_iff dist_nonneg]
  exact h x hx y hy hxy

theorem erase_min {n : ℕ} {A B : Finset ℝ²} (hA : IsMinimiser n A)
    (hB : B ∈ separatedSets (n+1))
    (hd : Metric.diam (B : Set ℝ²) ≤ Metric.diam (A : Set ℝ²))
    {x : ℝ²} (hx : x ∈ B) : IsMinimiser n (B.erase x) := by
  refine ⟨mk_sep (by rw [card_erase_of_mem hx,hB.1]; rfl) ?_,?_⟩
  · intro u hu w hw huw
    exact sep_dist hB (mem_of_mem_erase hu) (mem_of_mem_erase hw) huw
  · intro X hX
    have h1 : Metric.diam ((B.erase x : Finset ℝ²) : Set ℝ²) ≤ Metric.diam (B : Set ℝ²) :=
      Metric.diam_mono (by exact_mod_cast erase_subset x B) B.finite_toSet.isBounded
    exact (h1.trans hd).trans (hA.2 hX)

theorem T_congr {X Y : Finset ℝ²} (h : Congruent X Y) :
    ∑ u ∈ X, ∑ w ∈ X, dist u w ^ 2 = ∑ u ∈ Y, ∑ w ∈ Y, dist u w ^ 2 := by
  obtain ⟨e,he⟩ := h
  have hY : Y = X.image e := by
    apply Finset.coe_injective
    rw [Finset.coe_image]
    exact he.symm
  subst hY
  rw [sum_image (fun a _ b _ hab => e.injective hab)]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_image (fun a _ b _ hab => e.injective hab)]
  refine sum_congr rfl fun w _ => ?_
  rw [e.isometry.dist_eq]

theorem T_insert {X : Finset ℝ²} {x : ℝ²} (hx : x ∉ X) :
    ∑ u ∈ insert x X, ∑ w ∈ insert x X, dist u w ^ 2
      = ∑ u ∈ X, ∑ w ∈ X, dist u w ^ 2 + 2 * ∑ w ∈ X, dist x w ^ 2 := by
  have h1 : ∀ u ∈ X, ∑ w ∈ insert x X, dist u w ^ 2
      = dist x u ^ 2 + ∑ w ∈ X, dist u w ^ 2 := by
    intro u _
    rw [sum_insert hx,dist_comm]
  rw [sum_insert hx,sum_insert hx,sum_congr rfl h1,sum_add_distrib]
  simp only [dist_self]
  ring

theorem moment_eq {B : Finset ℝ²} {x y : ℝ²} (hx : x ∈ B) (hy : y ∈ B)
    (h : Congruent (B.erase x) (B.erase y)) :
    ∑ z ∈ B, dist x z ^ 2 = ∑ z ∈ B, dist y z ^ 2 := by
  have key : ∀ a ∈ B, ∑ u ∈ B, ∑ w ∈ B, dist u w ^ 2
      = ∑ u ∈ B.erase a, ∑ w ∈ B.erase a, dist u w ^ 2 + 2 * ∑ z ∈ B, dist a z ^ 2 := by
    intro a ha
    have h1 := T_insert (notMem_erase a B)
    rw [insert_erase ha] at h1
    rw [h1,sum_erase B (f := fun z => dist a z ^ 2) (by simp)]
  have hx' := key x hx
  have hy' := key y hy
  rw [T_congr h] at hx'
  linarith

theorem le_of_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hh
  push Not at hh
  nlinarith

theorem concyclic {B : Finset ℝ²} (hB : B.Nonempty)
    (h : ∀ x ∈ B, ∀ y ∈ B, Congruent (B.erase x) (B.erase y)) :
    ∃ c : ℝ², ∃ R : ℝ, (∀ x ∈ B, dist x c = R) ∧ ∑ x ∈ B, (x - c) = 0 := by
  have hm : (0:ℝ) < B.card := by exact_mod_cast hB.card_pos
  let c : ℝ² := (B.card : ℝ)⁻¹ • ∑ z ∈ B, z
  have hsum : ∑ x ∈ B, (x - c) = 0 := by
    rw [sum_sub_distrib,sum_const]
    dsimp [c]
    rw [← Nat.cast_smul_eq_nsmul ℝ,smul_smul,mul_inv_cancel₀ hm.ne',one_smul,sub_self]
  have hS : ∀ x : ℝ², ∑ z ∈ B, dist x z ^ 2
      = B.card * dist x c ^ 2 + ∑ z ∈ B, dist z c ^ 2 := by
    intro x
    have h1 : ∀ z ∈ B, dist x z ^ 2
        = dist x c ^ 2 - 2 * inner ℝ (x - c) (z - c) + dist z c ^ 2 := by
      intro z _
      rw [dist_eq_norm,dist_eq_norm,dist_eq_norm,
        show x - z = (x - c) - (z - c) by abel,norm_sub_sq_real]
    rw [sum_congr rfl h1,sum_add_distrib,sum_sub_distrib,sum_const,← mul_sum,
      ← inner_sum,hsum,inner_zero_right]
    simp
  obtain ⟨x0,hx0⟩ := hB
  refine ⟨c,dist x0 c,?_,hsum⟩
  intro x hx
  have h1 := moment_eq hx hx0 (h x hx x0 hx0)
  rw [hS x,hS x0] at h1
  have h2 : dist x c ^ 2 = dist x0 c ^ 2 := by
    have := mul_left_cancel₀ hm.ne' (add_right_cancel h1)
    exact this
  exact le_antisymm (le_of_sq_le dist_nonneg h2.le) (le_of_sq_le dist_nonneg h2.ge)

theorem dist_move_sq (p q v : ℝ²) (t : ℝ) :
    dist (p + t • v) q ^ 2
      = dist p q ^ 2 - 2 * t * inner ℝ v (q - p) + t ^ 2 * ‖v‖ ^ 2 := by
  rw [dist_eq_norm,dist_eq_norm,show p + t • v - q = (p - q) + t • v by abel,
    norm_add_sq_real,norm_smul,inner_smul_right,show q - p = -(p - q) by abel,
    inner_neg_right,real_inner_comm v (p - q),Real.norm_eq_abs,mul_pow,sq_abs]
  ring

set_option maxHeartbeats 1000000 in
theorem exists_slid {n : ℕ} {A : Finset ℝ²} (hA : IsMinimiser n A) (hn : 2 ≤ n)
    {p : ℝ²} (hp : p ∈ A) {v : ℝ²} (hv : v ≠ 0)
    (hU : ∀ q ∈ A, dist p q = 1 → inner ℝ v (q - p) ≤ 0)
    (hDm : ∀ r ∈ A, dist p r = Metric.diam (A : Set ℝ²) → 0 < inner ℝ v (r - p)) :
    ∃ B, IsMinimiser n B ∧ ¬ Congruent A B := by
  let C := A.erase p
  let D := Metric.diam (A : Set ℝ²)
  have hAcard : A.card = n := hA.1.1
  have hCcard : C.card = n-1 := by rw [card_erase_of_mem hp,hAcard]
  have hC : C.Nonempty := card_pos.mp (by omega)
  obtain ⟨q0,hq0⟩ := id hC
  have hN : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hOld (u : ℝ²) (hu : u ∈ C) : u ∈ A := mem_of_mem_erase hu
  have hlow (u : ℝ²) (hu : u ∈ C) : 1 ≤ dist p u :=
    sep_dist hA.1 hp (hOld u hu) (mem_erase.mp hu).1.symm
  have hhigh (u : ℝ²) (hu : u ∈ C) : dist p u ≤ D :=
    Metric.dist_le_diam_of_mem A.finite_toSet.isBounded hp (hOld u hu)
  have hD1 : 1 ≤ D := (hlow q0 hq0).trans (hhigh q0 hq0)
  let τ (u : ℝ²) : ℝ :=
    min (if dist p u = 1 then 1 else (dist p u - 1) / ‖v‖)
      (if dist p u = D then 2 * inner ℝ v (u - p) / ‖v‖ ^ 2 else (D - dist p u) / ‖v‖)
  have hτ (u : ℝ²) (hu : u ∈ C) : 0 < τ u := by
    apply lt_min
    · split_ifs with h1
      · exact one_pos
      · exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hlow u hu) (Ne.symm h1))) hN
    · split_ifs with h1
      · exact div_pos (mul_pos two_pos (hDm u (hOld u hu) h1)) (pow_pos hN 2)
      · exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hhigh u hu) h1)) hN
  let ε0 := C.inf' hC τ
  have hε0 : 0 < ε0 := by
    obtain ⟨x,hx,hEq⟩ := exists_mem_eq_inf' hC τ
    change 0 < C.inf' hC τ
    rw [hEq]
    exact hτ x hx
  have hε0le (u : ℝ²) (hu : u ∈ C) : ε0 ≤ τ u := inf'_le τ hu
  let b := inner ℝ v (q0 - p)
  let ε1 : ℝ := if 0 < b then b / ‖v‖ ^ 2 else 1
  have hε1 : 0 < ε1 := by
    dsimp [ε1]
    split_ifs with h1
    · exact div_pos h1 (pow_pos hN 2)
    · exact one_pos
  let ε := min ε0 ε1
  have hε : 0 < ε := lt_min hε0 hε1
  let g (t : ℝ) : ℝ := dist p q0 ^ 2 - 2 * t * b + t ^ 2 * ‖v‖ ^ 2
  have hinj : Set.InjOn g (Set.Ioo 0 ε) := by
    intro t1 ht1 t2 ht2 h12
    have hfac : (t1 - t2) * (‖v‖ ^ 2 * (t1 + t2) - 2 * b) = 0 := by
      dsimp [g] at h12
      linarith
    rcases mul_eq_zero.mp hfac with h|h
    · linarith
    · exfalso
      have hN2 : 0 < ‖v‖ ^ 2 := pow_pos hN 2
      by_cases hb : 0 < b
      · have h1 : ε ≤ b / ‖v‖ ^ 2 := by
          refine (min_le_right _ _).trans ?_
          dsimp [ε1]
          rw [if_pos hb]
        have h2 : ε * ‖v‖ ^ 2 ≤ b := (le_div_iff₀ hN2).mp h1
        nlinarith [ht1.2,ht2.2,ht1.1,ht2.1]
      · nlinarith [ht1.1,ht2.1]
  let DS := (A ×ˢ A).image fun xy => dist xy.1 xy.2 ^ 2
  have hex : ∃ t ∈ Set.Ioo 0 ε, g t ∉ DS := by
    by_contra hcon
    push Not at hcon
    exact (Set.infinite_of_injOn_mapsTo hinj hcon (Set.Ioo_infinite hε)) DS.finite_toSet
  obtain ⟨t,ht,htDS⟩ := hex
  have ht0 : 0 < t := ht.1
  let z := p + t • v
  have hzp : dist z p = t * ‖v‖ := by
    rw [dist_eq_norm]
    change ‖p + t • v - p‖ = _
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht0.le]
  have htτ (u : ℝ²) (hu : u ∈ C) : t ≤ τ u :=
    (ht.2.le.trans (min_le_left _ _)).trans (hε0le u hu)
  have hDistances (u : ℝ²) (hu : u ∈ C) : 1 ≤ dist z u ∧ dist z u ≤ D := by
    have hsq := dist_move_sq p u v t
    have h3 := dist_triangle p z u
    have h4 := dist_triangle z p u
    rw [dist_comm p z] at h3
    have hN2 : 0 < ‖v‖ ^ 2 := pow_pos hN 2
    constructor
    · by_cases h1 : dist p u = 1
      · have hb := hU u (hOld u hu) h1
        have : (1:ℝ) ^ 2 ≤ dist z u ^ 2 := by
          change (1:ℝ) ^ 2 ≤ dist (p + t • v) u ^ 2
          rw [hsq,h1]
          nlinarith [mul_nonneg ht0.le (neg_nonneg.mpr hb),mul_pos (pow_pos ht0 2) hN2]
        exact le_of_sq_le dist_nonneg this
      · have h5 : t ≤ (dist p u - 1) / ‖v‖ := by
          have := (htτ u hu).trans (min_le_left _ _)
          rwa [if_neg h1] at this
        have h6 : t * ‖v‖ ≤ dist p u - 1 := (le_div_iff₀ hN).mp h5
        linarith
    · by_cases h1 : dist p u = D
      · have h5 : t ≤ 2 * inner ℝ v (u - p) / ‖v‖ ^ 2 := by
          have := (htτ u hu).trans (min_le_right _ _)
          rwa [if_pos h1] at this
        have h6 : t * ‖v‖ ^ 2 ≤ 2 * inner ℝ v (u - p) := (le_div_iff₀ hN2).mp h5
        have : dist z u ^ 2 ≤ D ^ 2 := by
          change dist (p + t • v) u ^ 2 ≤ D ^ 2
          rw [hsq,h1]
          nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr h6)]
        exact le_of_sq_le (by linarith) this
      · have h5 : t ≤ (D - dist p u) / ‖v‖ := by
          have := (htτ u hu).trans (min_le_right _ _)
          rwa [if_neg h1] at this
        have h6 : t * ‖v‖ ≤ D - dist p u := (le_div_iff₀ hN).mp h5
        linarith
  have hzC : z ∉ C := by
    intro h
    have hh := (hDistances z h).1
    simp only [dist_self] at hh
    linarith
  let B := insert z C
  have hBcard : B.card = n := by rw [card_insert_of_notMem hzC,hCcard]; omega
  have hSep : B ∈ separatedSets n := by
    refine mk_sep hBcard ?_
    intro x hx y hy hxy
    rcases mem_insert.mp hx with rfl|hx <;> rcases mem_insert.mp hy with rfl|hy
    · exact (hxy rfl).elim
    · exact (hDistances y hy).1
    · simpa [dist_comm] using (hDistances x hx).1
    · exact sep_dist hA.1 (hOld x hx) (hOld y hy) hxy
  have hDiam : Metric.diam (B : Set ℝ²) ≤ D := by
    apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
    intro x hx y hy
    change x ∈ B at hx
    change y ∈ B at hy
    rcases mem_insert.mp hx with rfl|hx <;> rcases mem_insert.mp hy with rfl|hy
    · simp [Metric.diam_nonneg]
    · exact (hDistances y hy).2
    · simpa [dist_comm] using (hDistances x hx).2
    · exact Metric.dist_le_diam_of_mem A.finite_toSet.isBounded (hOld x hx) (hOld y hy)
  refine ⟨B,⟨hSep,?_⟩,?_⟩
  · intro X hX
    exact hDiam.trans (hA.2 hX)
  · rintro ⟨e,he⟩
    have hzB : z ∈ (B : Set ℝ²) := mem_insert_self _ _
    have hqB : q0 ∈ (B : Set ℝ²) := mem_insert_of_mem hq0
    have hzImage : z ∈ e '' (A : Set ℝ²) := by rw [he]; exact hzB
    have hqImage : q0 ∈ e '' (A : Set ℝ²) := by rw [he]; exact hqB
    obtain ⟨u,hu,huZ⟩ := hzImage
    obtain ⟨w,hw,hwQ⟩ := hqImage
    apply htDS
    refine mem_image.mpr ⟨(u,w),mem_product.mpr ⟨hu,hw⟩,?_⟩
    have h1 : dist u w = dist z q0 := by
      rw [← huZ,← hwQ]
      exact (e.isometry.dist_eq u w).symm
    change dist u w ^ 2 = g t
    rw [h1]
    exact dist_move_sq p q0 v t

theorem main : H1 → H2 → OMA.R_Erdos103_erdos_103_variants_two_le_R1.H2 := by
  intro h1 h2
  have h1' := (tendsto_add_atTop_nat 1).eventually h1
  filter_upwards [h1',h2,(eventually_ge_atTop 2 : ∀ᶠ n : ℕ in atTop, 2 ≤ n)]
    with n hn1 hn2 hn hEx _
  obtain ⟨A,hA⟩ := hEx
  by_cases hP : ∃ B ∈ separatedSets (n+1),
      Metric.diam (B : Set ℝ²) ≤ Metric.diam (A : Set ℝ²)
  · obtain ⟨B,hB,hBd⟩ := hP
    obtain ⟨C0,hC0,hC0lt⟩ := hn1
    have hne : ∀ X ∈ separatedSets (n+1), X.Nonempty := by
      intro X hX
      exact card_pos.mp (by rw [hX.1]; omega)
    by_cases hc : ∀ x ∈ B, ∀ y ∈ B, Congruent (B.erase x) (B.erase y)
    · have hlt := hC0lt B hB (concyclic (hne B hB) hc)
      by_cases hc0 : ∀ x ∈ C0, ∀ y ∈ C0, Congruent (C0.erase x) (C0.erase y)
      · exact absurd (hC0lt C0 hC0 (concyclic (hne C0 hC0) hc0)) (lt_irrefl _)
      · push Not at hc0
        obtain ⟨x,hx,y,hy,hxy⟩ := hc0
        exact ⟨_,_,erase_min hA hC0 (hlt.le.trans hBd) hx,
          erase_min hA hC0 (hlt.le.trans hBd) hy,hxy⟩
    · push Not at hc
      obtain ⟨x,hx,y,hy,hxy⟩ := hc
      exact ⟨_,_,erase_min hA hB hBd hx,erase_min hA hB hBd hy,hxy⟩
  · push Not at hP
    by_cases hS : ∀ X : Finset ℝ², IsMinimiser n X → ∀ p ∈ X, ∀ v : ℝ², v ≠ 0 →
        (∃ q ∈ X, dist p q = 1 ∧ 0 < inner ℝ v (q - p)) ∨
        (∃ r ∈ X, dist p r = Metric.diam (X : Set ℝ²) ∧ inner ℝ v (r - p) ≤ 0)
    · obtain ⟨B,hB,hAB⟩ := hn2 A hA hP hS
      exact ⟨A,B,hA,hB,hAB⟩
    · push Not at hS
      obtain ⟨X,hX,p,hp,v,hv,hU,hDm⟩ := hS
      obtain ⟨B,hB,hN⟩ := exists_slid hX hn hp hv hU hDm
      exact ⟨X,B,hX,hB,hN⟩

end Proof

end OMA.R_Erdos103_erdos_103_variants_two_le_R1_H2_R1
