import OMAReductions.R_Green3_green_3_R1

/-! Dyadic inner approximation for the finite formulation of Green 3.
Lean proof by @Deldor14. -/

open Set MeasureTheory Finset

open OMA.R_Green3_green_3_R1

theorem OMA.solution : OMA.R_Green3_green_3_R1.H1 := by
  classical
  intro A hA hsub hvol
  obtain ⟨K,hKA,hK,hlarge⟩ := hA.measurableSet.exists_lt_isCompact hvol
  obtain ⟨δ,hδ,hthick⟩ := hK.exists_thickening_subset_open hA hKA
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (1/δ) (by norm_num : (1:ℝ)<2)
  let N : ℕ := 2^k
  have hNr : (0:ℝ)<N := by dsimp [N]; positivity
  have hwidth : 1/(N:ℝ) < δ := by
    have hh : (1:ℝ)/δ < N := by simpa [N] using hk
    apply (div_lt_iff₀ hNr).2
    simpa [mul_comm] using (div_lt_iff₀ hδ).mp hh
  let C : ℕ → Set ℝ := fun i => Set.Icc ((i:ℝ)/N) (((i:ℝ)+1)/N)
  let S := (range N).filter fun i => C i ⊆ A
  have hS : S ⊆ range N := filter_subset _ _
  have hclosed (i : ℕ) (hi : i ∈ S) : C i ⊆ A := (mem_filter.mp hi).2
  have hpart : A ⊆ Set.Ioo 0 1 := by simpa using interior_maximal hsub hA
  have hcover : K ⊆ ⋃ i ∈ S, C i := by
    intro x hx
    obtain ⟨hx0,hx1⟩ := hpart (hKA hx)
    let i := ⌊x*N⌋₊
    have hfl : (i:ℝ) ≤ x*N := Nat.floor_le (by positivity)
    have hfr : x*N < (i:ℝ)+1 := Nat.lt_floor_add_one _
    have hi : (i:ℝ)<N := hfl.trans_lt (by nlinarith only [mul_lt_mul_of_pos_right hx1 hNr])
    have hir : i < N := by exact_mod_cast hi
    have hleft : (i:ℝ)/N ≤ x := (div_le_iff₀ hNr).2 hfl
    have hright : x < ((i:ℝ)+1)/N := (lt_div_iff₀ hNr).2 hfr
    have hstay : C i ⊆ A := by
      intro y hy
      apply hthick
      apply Metric.mem_thickening_iff.mpr
      refine ⟨x,hx,?_⟩
      have he : ((i:ℝ)+1)/N = (i:ℝ)/N + 1/N := add_div _ _ _
      obtain ⟨hyl,hyr⟩ := hy
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact mem_iUnion₂.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr hir,hstay⟩,hleft,hright.le⟩
  have hmeas (i : ℕ) : volume (C i) = ENNReal.ofReal (1/(N:ℝ)) := by
    rw [show C i = Set.Icc ((i:ℝ)/N) (((i:ℝ)+1)/N) from rfl, Real.volume_Icc]
    congr 1
    ring
  have hupper : volume K ≤ ENNReal.ofReal ((S.card:ℝ)/N) := calc
    volume K ≤ volume (⋃ i ∈ S, C i) := measure_mono hcover
    _ ≤ ∑ i ∈ S, volume (C i) := measure_biUnion_finset_le _ _
    _ = ∑ _i ∈ S, ENNReal.ofReal (1/(N:ℝ)) := sum_congr rfl fun i _ => hmeas i
    _ = ENNReal.ofReal (∑ _i ∈ S, 1/(N:ℝ)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)).symm
    _ = ENNReal.ofReal ((S.card:ℝ)/N) := by simp [nsmul_eq_mul, div_eq_mul_inv]
  have hreal : (1:ℝ)/3 < S.card/N := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<3)]
    simpa using hlarge.trans_le hupper
  have hbig : (N:ℝ) < 3*S.card := by
    have h := (lt_div_iff₀ hNr).mp hreal
    linarith
  exact ⟨k,S,hS,by exact_mod_cast hbig,fun i hi => Set.Ioo_subset_Icc_self.trans (hclosed i hi)⟩
