import OMAStatements.S_oeis_a168670

theorem OMA.solution : type_of% @OMA.S_oeis_a168670.main := by
  intro n hn hmod p hp hp2 heq
  have hfac : 36 * n ^ 2 + 72 * n + 35 = (6 * n + 5) * (6 * n + 7) := by ring
  rw [hfac] at heq
  have hpe : p = 6 * n + 5 := by
    rcases lt_trichotomy p (6 * n + 5) with h | h | h
    · have h1 : p * (p + 2) < (6 * n + 5) * (6 * n + 7) := by
        have : p + 2 < 6 * n + 7 := by omega
        exact Nat.mul_lt_mul'' h this
      omega
    · exact h
    · have h1 : (6 * n + 5) * (6 * n + 7) < p * (p + 2) := by
        have : 6 * n + 7 < p + 2 := by omega
        exact Nat.mul_lt_mul'' h this
      omega
  subst hpe
  rcases hmod with h | h
  · have hd : 11 ∣ 6 * n + 5 := by omega
    rcases hp.eq_one_or_self_of_dvd 11 hd with h1 | h1 <;> omega
  · have hd : 11 ∣ 6 * n + 5 + 2 := by omega
    rcases hp2.eq_one_or_self_of_dvd 11 hd with h1 | h1 <;> omega
