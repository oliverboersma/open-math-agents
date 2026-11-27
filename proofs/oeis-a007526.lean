import OMAStatements.S_oeis_a007526

-- Problem: A007526: a(n) = n*(a(n-1) + 1), a(0) = 0.
-- Upstream: formal-conjectures statements/oeis-a007526.lean:0 (declaration OMA.S_oeis_a007526.main)
-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

theorem OMA.solution : type_of% @OMA.S_oeis_a007526.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  simp only [OMA.S_oeis_a007526.a]
  push_cast
  ring
