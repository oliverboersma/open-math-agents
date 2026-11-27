import OMAStatements.S_oeis_a233398

theorem OMA.solution : type_of% @OMA.S_oeis_a233398.main := by
  intro x ⟨y, hy⟩
  unfold OMA.S_oeis_a233398.a
  apply Nat.mod_eq_zero_of_dvd
  subst hy
  rw [mul_pow, show (3 * y) = 3 * y from rfl]
  exact ⟨y ^ (3 * y), by ring⟩
