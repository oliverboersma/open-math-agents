import OMAStatements.S_oeis_a037250

theorem OMA.solution : type_of% @OMA.S_oeis_a037250.main := by
  intro n hn
  simp (disch := omega) only [OMA.S_oeis_a037250.a, Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one]
  ring
