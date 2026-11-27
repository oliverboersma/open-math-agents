import OMAStatements.S_oeis_a071287

open OMA.S_oeis_a071287

/-! The conjectured series begins in degree twelve. The order-six Peirce
stream already has a nonzero numerator at index six. -/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071287.main) := by
  intro h
  have hsix := h.2 6
  have hstream : numeratorAt 6 6 = 1 := by decide
  have hseries : gfCoeff 21
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 2,
       3, 4, 5, 2, 4, 6, 5, 3, 1, 5, 4, 3, 4, 2, 3, 2, 3, 1, 2, 2, 1, 1, 1, 1] 6 = 0 :=
    by decide
  rw [hstream, hseries] at hsix
  exact Nat.one_ne_zero hsix
