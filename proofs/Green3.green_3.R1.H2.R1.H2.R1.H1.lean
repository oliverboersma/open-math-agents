import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R1
import Mathlib

open Filter Topology MeasureTheory

namespace GreenGeometricCells

/-- The geometric cell between two successive powers of q. -/
private def cell (q : ℝ) (i : ℕ) : Set ℝ := Set.Icc (q^(i+1)) (q^i)

private theorem pow_mem_cell {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) {i r : ℕ}
    (hi : i ≤ r) (hr : r ≤ i+1) : q^r ∈ cell q i :=
  ⟨pow_le_pow_of_le_one hq hq1 hr, pow_le_pow_of_le_one hq hq1 hi⟩

/-- Closed cells in a product-free set have a separation of at least one endpoint. -/
private theorem separated {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) {U : Set ℝ}
    (hfree : ∀ x ∈ U, ∀ y ∈ U, x*y ∉ U) {i j l : ℕ}
    (hi : cell q i ⊆ U) (hj : cell q j ⊆ U) (hl : cell q l ⊆ U) :
    l+1 < i+j ∨ i+j+2 < l := by
  by_contra! h
  let r := max (i+j) l
  have hr0 : i+j ≤ r := le_max_left _ _
  have hr1 : l ≤ r := le_max_right _ _
  have hr2 : r ≤ i+j+2 := max_le (by omega) h.2
  have hr3 : r ≤ l+1 := max_le h.1 (by omega)
  let d := r - (i+j)
  have hd : d ≤ 2 := by dsimp [d]; omega
  let s := min d 1
  let t := d - s
  have hs : s ≤ 1 := min_le_right _ _
  have ht : t ≤ 1 := by dsimp [t,s]; omega
  have hst : s + t = d := Nat.add_sub_of_le (min_le_left _ _)
  have heq : i+s+(j+t) = r := by dsimp [d] at hst; omega
  have hmul : q^(i+s) * q^(j+t) ∈ U := by
    rw [← pow_add, heq]
    exact hl (pow_mem_cell hq hq1 hr1 hr3)
  exact hfree _ (hi (pow_mem_cell hq hq1 (by omega) (by omega)))
    _ (hj (pow_mem_cell hq hq1 (by omega) (by omega))) hmul

theorem main (U : Set ℝ) (hU : IsOpen U) (hUI : U ⊆ Set.Icc 0 1)
    (hvol : 1/3 < volume U) (hfree : ∀ x ∈ U, ∀ y ∈ U, x*y ∉ U) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∃ T : Finset ℕ, T.Nonempty ∧
      (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) ∧
      1/3 < (1-q)*(∑ i ∈ T, q^i) := by
  classical
  obtain ⟨K, hKU, hK, hKvol⟩ := hU.measurableSet.exists_lt_isCompact hvol
  have hKne : K.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, measure_empty] at hKvol
    exact (not_lt_of_ge zero_le) hKvol
  have hzero : (0 : ℝ) ∉ U := by
    intro hz
    exact hfree 0 hz 0 hz (by simpa using hz)
  obtain ⟨m, hm, hmmin⟩ := hK.exists_isMinOn hKne continuous_id.continuousOn
  have hm0 : 0 < m := lt_of_le_of_ne (hUI (hKU hm)).1 (fun h => hzero (h ▸ hKU hm))
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let q := 1 - min (δ/2) (1/2)
  have hq0 : 0 < q := by dsimp [q]; linarith [min_le_right (δ/2) (1/2)]
  have hq1 : q < 1 := by dsimp [q]; linarith [lt_min (half_pos hδ) (show (0:ℝ) < 1/2 by norm_num)]
  have hqδ : 1 - q ≤ δ := by dsimp [q]; linarith [min_le_left (δ/2) (1/2)]
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
  obtain ⟨N, hN⟩ := (hp.eventually_lt_const hm0).exists
  let T := (Finset.range N).filter (fun i => cell q i ⊆ U)
  have hmem {i : ℕ} (hi : i ∈ T) : cell q i ⊆ U := (Finset.mem_filter.mp hi).2
  have hcover : ∀ x ∈ K, ∃ i ∈ T, x ∈ cell q i := by
    intro x hx
    have hxmin : m ≤ x := hmmin hx
    have hx1 : x ≤ 1 := (hUI (hKU hx)).2
    have hex : ∃ n : ℕ, q^n < x := ⟨N, hN.trans_le hxmin⟩
    have hpos : Nat.find hex ≠ 0 := by
      intro h
      have hf := Nat.find_spec hex
      rw [h, pow_zero] at hf
      exact (not_lt_of_ge hx1) hf
    obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hir : i < N := by
      have hle := Nat.find_min' hex (hN.trans_le hxmin)
      omega
    have hxcell : x ∈ cell q i := by
      refine ⟨?_, ?_⟩
      · have hlt := Nat.find_spec hex
        rw [hi] at hlt
        exact hlt.le
      · exact le_of_not_gt (Nat.find_min hex (by omega : i < Nat.find hex))
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hir, ?_⟩, hxcell⟩
    intro y hy
    apply hδU
    apply Metric.mem_cthickening_of_dist_le y x δ K hx
    have hwidth : q^i - q^(i+1) ≤ δ := by
      rw [pow_succ, ← mul_one_sub]
      exact (mul_le_of_le_one_left (sub_nonneg.mpr hq1.le) (pow_le_one₀ hq0.le hq1.le)).trans hqδ
    have hxrange : q^(i+1) ≤ x ∧ x ≤ q^i := hxcell
    have hyrange : q^(i+1) ≤ y ∧ y ≤ q^i := hy
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hTne : T.Nonempty := by
    obtain ⟨x,hx⟩ := hKne
    obtain ⟨i,hi,_⟩ := hcover x hx
    exact ⟨i,hi⟩
  have hKsub : K ⊆ ⋃ i ∈ T, cell q i := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := hcover x hx
    exact Set.mem_iUnion₂.mpr ⟨i,hi,hx⟩
  have hupper : volume K ≤ ENNReal.ofReal ((1-q)*(∑ i ∈ T, q^i)) := by
    calc
      volume K ≤ volume (⋃ i ∈ T, cell q i) := measure_mono hKsub
      _ ≤ ∑ i ∈ T, volume (cell q i) := measure_biUnion_finset_le _ _
      _ = ENNReal.ofReal ((1-q)*(∑ i ∈ T, q^i)) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg
          (fun i _ => mul_nonneg (sub_nonneg.mpr hq1.le) (pow_nonneg hq0.le _))]
        apply Finset.sum_congr rfl
        intro i hi
        rw [cell, Real.volume_Icc, pow_succ]
        congr 1
        ring
  have hthird : ENNReal.ofReal (1/3) = 1/3 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3)]
    norm_cast
  refine ⟨q, hq0, hq1, T, hTne, fun i hi j hj l hl => separated hq0.le hq1.le hfree
    (hmem hi) (hmem hj) (hmem hl), ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp
    (hthird.symm ▸ hKvol.trans_le hupper)

end GreenGeometricCells

theorem OMA.solution : OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H1 :=
  GreenGeometricCells.main