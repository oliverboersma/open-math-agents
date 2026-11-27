import OMAStatements.S_oeis_a071283

open OMA.S_oeis_a071283

/-! The proposed numerator starts in degree eight. The order-four stream
already has numerator one at index four, so the generating function fails. -/

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071283.main) := by
  intro h
  have hfour := h.2 4
  have hstream : numeratorAt 4 4 = 1 := by decide
  have hseries : gfCoeff 10
      [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 3, 2, 2, 1, 1, 1] 4 = 0 :=
    by decide
  rw [hstream, hseries] at hfour
  exact Nat.one_ne_zero hfour
