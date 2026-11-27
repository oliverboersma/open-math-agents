import OMAStatements.S_oeis_a267623

section Aux
open OMA.S_oeis_a267623

lemma rule_eq (l c r : Bool) : rule l c r = (!c || r) := by
  cases l <;> cases c <;> cases r <;> decide

lemma state_succ (n : ℕ) (x : ℤ) : state (n + 1) x = (!state n x || state n (x + 1)) := by
  simp only [state, step, rule_eq]

lemma state_ge (n : ℕ) : ∀ x, state (n + 1) x = decide (x ≠ -(n : ℤ)) := by
  induction n with
  | zero =>
    intro x
    rw [state_succ]
    simp only [state, initial]
    by_cases h : x = 0 <;> by_cases h2 : x + 1 = 0 <;> simp [h, h2] <;> omega
  | succ n ih =>
    intro x
    rw [state_succ, ih, ih]
    by_cases h : x = -(n : ℤ) <;> by_cases h2 : x + 1 = -(n : ℤ) <;> simp [h, h2] <;> omega

lemma a_val (n : ℕ) (hn : 2 ≤ n) : a n = 10 * a (n - 1) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h : state (m + 2) 0 = true := by
    rw [state_ge (m + 1)]; simp; omega
  show column (m + 2 + 1) = 10 * column (m + 1 + 1) + 1
  rw [column]
  simp [bit, h]

end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a267623.main := by
  open OMA.S_oeis_a267623 in
  have a0 : a 0 = 1 := by
    show column 1 = 1
    simp [column, bit, state, initial]
  have a1 : a 1 = 10 := by
    show column 2 = 10
    have : state 1 0 = false := by rw [state_ge 0]; simp
    show 10 * (10 * 0 + bit (state 0 0)) + bit (state 1 0) = 10
    rw [this]
    simp [bit, state, initial]
  refine ⟨fun n hn => ?_, ?_⟩
  · have h1 := a_val (n - 1) (by omega)
    have h2 : n - 1 - 1 = n - 2 := by omega
    rw [h2] at h1
    have h3 := a_val n (by omega)
    push_cast [h3, h1] at *
    omega
  · ext n
    have hm : series * ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X)) =
        series - PowerSeries.C (11 : ℤ) * (series * PowerSeries.X ^ 1) + PowerSeries.C (10 : ℤ) * (series * PowerSeries.X ^ 2) := by
      simp only [map_ofNat]; ring
    rw [hm]
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', series, PowerSeries.coeff_mk,
      PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    rcases n with _ | _ | _ | m
    · simp [a0]
    · simp [a1, a0]
    · have : a 2 = 101 := by
        have := a_val 2 (by norm_num)
        simpa [a1] using this
      simp [this, a1, a0]
    · have h1 := a_val (m + 3) (by omega)
      have h2 := a_val (m + 2) (by omega)
      simp only [show m + 3 - 1 = m + 2 by omega] at h1
      simp only [show m + 2 - 1 = m + 1 by omega] at h2
      simp [h1, h2, show m + 3 - 2 = m + 1 by omega]
      push_cast
      ring
