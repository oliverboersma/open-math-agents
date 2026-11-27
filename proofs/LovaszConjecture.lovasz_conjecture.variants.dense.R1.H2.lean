import OMAReductions.R_LovaszConjecture_lovasz_conjecture_variants_dense_R1

/-! The tail of a Hamiltonian cycle, that is the cycle without its first edge, visits
every vertex exactly once. -/

theorem OMA.solution : OMA.R_LovaszConjecture_lovasz_conjecture_variants_dense_R1.H2 := by
  intro V _ _ G v c hc
  exact ⟨_, _, c.tail,
    (SimpleGraph.Walk.isHamiltonianCycle_isCycle_and_isHamiltonian_tail.1 hc).2⟩
