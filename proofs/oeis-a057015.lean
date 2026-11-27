import OMAStatements.S_oeis_a057015

open OMA.S_oeis_a057015

theorem OMA.solution : type_of% @OMA.S_oeis_a057015.main := by
  intro k hT hk
  obtain ⟨h1, -, -, h9⟩ := hT
  have hsq : k ^ 2 % 10 = (k % 10) ^ 2 % 10 := Nat.pow_mod k 2 10
  have hk4 : 9 ≤ k ^ 2 := by nlinarith
  have hr : k % 10 < 10 := Nat.mod_lt _ (by norm_num)
  by_contra hne
  have key : 2 ∣ k ^ 2 + 1 ∨ 5 ∣ k ^ 2 + 1 ∨ 5 ∣ k ^ 2 + 9 := by
    interval_cases h : k % 10 <;> omega
  rcases key with h | h | h
  · have := (Nat.Prime.eq_one_or_self_of_dvd h1 _ h); omega
  · have := (Nat.Prime.eq_one_or_self_of_dvd h1 _ h); omega
  · have := (Nat.Prime.eq_one_or_self_of_dvd h9 _ h); omega
