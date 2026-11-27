import OMAStatements.S_oeis_a010845

-- Problem: oeis-a010845
-- Credit: @LAPRAI (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OMA.S_oeis_a010845.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  rw [show OMA.S_oeis_a010845.a (m + 2) = 3 * (m + 2) * OMA.S_oeis_a010845.a (m + 1) + 1 from rfl,
    show OMA.S_oeis_a010845.a (m + 1) = 3 * (m + 1) * OMA.S_oeis_a010845.a m + 1 from rfl]
  push_cast
  ring
