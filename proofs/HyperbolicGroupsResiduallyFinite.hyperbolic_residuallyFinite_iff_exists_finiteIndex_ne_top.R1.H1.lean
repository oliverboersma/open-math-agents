import OMAReductions.R_HyperbolicGroupsResiduallyFinite_hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top_R1

-- Step HyperbolicGroupsResiduallyFinite.hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top.R1.H1: hypothesis H1 of reduction HyperbolicGroupsResiduallyFinite.hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top.R1

/-!
A non-trivial group has an element `g ≠ 1`. If the group is residually finite, some finite-index
normal subgroup misses `g`, so it is a proper subgroup of finite index.
-/

theorem OMA.solution :
    OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top_R1.H1 := by
  unfold OMA.R_HyperbolicGroupsResiduallyFinite_hyperbolic_residuallyFinite_iff_exists_finiteIndex_ne_top_R1.H1
  intro hall G _ _ _
  have hrf : Group.ResiduallyFinite G := hall G
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  obtain ⟨H, hH⟩ := Group.exists_finiteIndexNormalSubgroup_notMem g hg
  refine ⟨H.toSubgroup, ?_, H.isFiniteIndex'⟩
  intro htop
  apply hH
  have hmem : g ∈ H.toSubgroup := by
    rw [htop]
    exact Subgroup.mem_top g
  exact FiniteIndexNormalSubgroup.mem_toSubgroup_iff.mp hmem
