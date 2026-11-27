import OMAStatements.S_oeis_a024152

theorem OMA.solution : type_of% @OMA.S_oeis_a024152.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp (disch := decide) only [OMA.S_oeis_a024152.a, Nat.add_sub_assoc, Nat.reduceSub]
  push_cast
  ring
