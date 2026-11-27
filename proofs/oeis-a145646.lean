import OMAStatements.S_oeis_a145646

-- Disproof: the claimed order-5 recurrence fails at n = 15.
-- wavelength 15 = 205035, while the recurrence predicts 205034.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a145646.main) := by
  rintro ⟨-, -, h⟩
  have h15 := h 15 (by norm_num)
  norm_num [OMA.S_oeis_a145646.wavelength] at h15
