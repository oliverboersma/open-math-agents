import OMAStatements.S_oeis_a126674

theorem OMA.solution : type_of% @OMA.S_oeis_a126674.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp only [OMA.S_oeis_a126674.a, show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
    Finset.sum_range_succ, Nat.factorial_succ]
  push_cast
  have h1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have h2 : (m : ℚ) + 1 + 1 ≠ 0 := by positivity
  field_simp
  ring
