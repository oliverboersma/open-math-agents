import OMAStatements.S_oeis_a323397

theorem OMA.solution : type_of% @OMA.S_oeis_a323397.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [OMA.S_oeis_a323397.a, show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  push_cast
  ring
