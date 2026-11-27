import OMAStatements.S_oeis_a136433

-- Credit: @yuka30240
open OMA.S_oeis_a136433

theorem OMA.solution : type_of% @OMA.S_oeis_a136433.main := by
  intro m hm
  -- The coefficients have period six. Keep the block index arbitrary and
  -- expand the defining recurrence back to the same term in each residue class.
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < 6 ∧ m = 6 * q + r + 10 :=
    ⟨(m - 10) / 6, (m - 10) % 6, by omega, by omega⟩
  interval_cases r <;> simp [a, Nat.add_mod, Nat.mul_mod] <;> ring
