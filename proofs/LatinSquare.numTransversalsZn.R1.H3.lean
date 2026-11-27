import OMAReductions.R_LatinSquare_numTransversalsZn_R1

-- Step LatinSquare.numTransversalsZn.R1.H3
-- Credit: @caa1982

open Filter Set
open scoped Topology

theorem OMA.solution : OMA.R_LatinSquare_numTransversalsZn_R1.H3 := by
  intro u x hu hx hub
  let a₀ : ℝ := x / 2
  let b₀ : ℝ := (x + 1) / 2
  have ha₀ : 0 < a₀ := by dsimp [a₀]; linarith [hx.1]
  have ha₀x : a₀ < x := by dsimp [a₀]; linarith [hx.1]
  have hxb₀ : x < b₀ := by dsimp [b₀]; linarith [hx.2]
  have hb₀ : b₀ < 1 := by dsimp [b₀]; linarith [hx.2]
  have hev : ∀ᶠ n in atTop, u n ∈ Ioo a₀ b₀ := hu.eventually (Ioo_mem_nhds ha₀x hxb₀)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  let S : Finset ℝ := insert a₀ ((Finset.Ico 1 N).image u)
  let T : Finset ℝ := insert b₀ ((Finset.Ico 1 N).image u)
  let a : ℝ := S.min' (Finset.insert_nonempty _ _)
  let b : ℝ := T.max' (Finset.insert_nonempty _ _)
  have ha_le : a ≤ a₀ := Finset.min'_le S a₀ (Finset.mem_insert_self _ _)
  have hb_ge : b₀ ≤ b := Finset.le_max' T b₀ (Finset.mem_insert_self _ _)
  refine ⟨a, b, ?_, ?_, by linarith, ?_⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact ha₀
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy'
      exact (hub n (Finset.mem_Ico.mp hn).1).1
  · rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact hb₀
    · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy'
      exact (hub n (Finset.mem_Ico.mp hn).1).2
  · intro n hn
    by_cases hlt : n < N
    · have hmem : u n ∈ (Finset.Ico 1 N).image u :=
        Finset.mem_image.mpr ⟨n, Finset.mem_Ico.mpr ⟨hn, hlt⟩, rfl⟩
      exact ⟨Finset.min'_le S _ (Finset.mem_insert_of_mem hmem),
        Finset.le_max' T _ (Finset.mem_insert_of_mem hmem)⟩
    · have hmem := hN n (not_lt.mp hlt)
      exact ⟨le_trans ha_le hmem.1.le, le_trans hmem.2.le hb_ge⟩
