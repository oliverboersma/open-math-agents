import OMAStatements.S_mse_4462775

/-!
# A compact surjective linear map has finite-dimensional codomain

Credit: @lucasfreund2-cmd
Source: Mathematics Stack Exchange question 4462775.
The classical argument is also given in Ryszard Szwarc's answer of 31 May 2022.
Continuity is derived from compactness, then the open mapping theorem gives
local compactness of the codomain.
-/

open Set Filter Topology

theorem OMA.solution : type_of% @OMA.S_mse_4462775.main := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T hT hcompact
  obtain ⟨D, hD, hTD⟩ := hcompact
  have hcompactT : IsCompactOperator T := by
    refine ⟨D, hD, Filter.mem_of_superset (Metric.ball_mem_nhds (0 : X) zero_lt_one) ?_⟩
    intro x hx
    exact hTD ⟨x, hx, rfl⟩
  let L : X →L[𝕜] Y := ⟨T, hcompactT.continuous⟩
  have hopen : IsOpen (L '' Metric.ball 0 1) := L.isOpenMap hT _ Metric.isOpen_ball
  have hzero : (0 : Y) ∈ L '' Metric.ball 0 1 := by
    exact ⟨0, by simp, by simp⟩
  have hDnhds : D ∈ 𝓝 (0 : Y) :=
    Filter.mem_of_superset (hopen.mem_nhds hzero) hTD
  let : LocallyCompactSpace Y := hD.locallyCompactSpace_of_mem_nhds_of_addGroup hDnhds
  exact FiniteDimensional.of_locallyCompactSpace 𝕜
