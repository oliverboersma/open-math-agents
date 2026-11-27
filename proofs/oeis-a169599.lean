import OMAStatements.S_oeis_a169599

theorem OMA.solution : type_of% @OMA.S_oeis_a169599.main := by
  intro n hn hmod p hp hp2 h
  have hpn : p = 6 * n + 5 := by
    rcases lt_trichotomy p (6 * n + 5) with hl | he | hg
    · exfalso
      have hlt : p * (p + 2) < 36 * n ^ 2 + 72 * n + 35 := by nlinarith
      exact (ne_of_lt hlt) h.symm
    · exact he
    · exfalso
      have hlt : 36 * n ^ 2 + 72 * n + 35 < p * (p + 2) := by nlinarith
      exact (ne_of_lt hlt) h
  subst hpn
  rcases hmod with hm | hm
  · have hd : 29 ∣ 6 * n + 5 := by omega
    rcases hp.eq_one_or_self_of_dvd 29 hd with h1 | h1 <;> omega
  · have hd : 29 ∣ 6 * n + 5 + 2 := by omega
    rcases hp2.eq_one_or_self_of_dvd 29 hd with h1 | h1 <;> omega
