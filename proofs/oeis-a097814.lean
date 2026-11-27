import OMAStatements.S_oeis_a097814

theorem OMA.solution : type_of% @OMA.S_oeis_a097814.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  rw [show OMA.S_oeis_a097814.a (m + 2) = 3 * (m + 2) * OMA.S_oeis_a097814.a (m + 1) + 3 ^ (m + 2) from rfl,
    show OMA.S_oeis_a097814.a (m + 1) = 3 * (m + 1) * OMA.S_oeis_a097814.a m + 3 ^ (m + 1) from rfl]
  push_cast
  ring
