import OMAStatements.S_oeis_a082994

-- Disproof: k = 2178 has rev10 k = 8712 and 2178 * 8712 = 4356 ^ 2, but 2178 is not a square.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a082994.main) := by
  intro h
  have hr : OMA.S_oeis_a082994.rev10 2178 = 8712 := by
    simp [OMA.S_oeis_a082994.rev10, Nat.ofDigits]
  have h2 := (h 2178 (by norm_num) (by norm_num) (by rw [hr]; norm_num)
    ⟨4356, by rw [hr]⟩).1
  obtain ⟨r, hr2⟩ := h2
  rcases (show r ≤ 46 ∨ 47 ≤ r by omega) with h3 | h3 <;> nlinarith
