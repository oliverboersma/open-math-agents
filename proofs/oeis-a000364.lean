import OMAStatements.S_oeis_a000364

section Aux
open OMA.S_oeis_a000364

lemma sec_succ (n : ℕ) : secantNumber (n + 1) = ∑ j ∈ Finset.range (n + 1),
    (-1 : ℤ) ^ (j + 2) * ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * secantNumber (n - j) := by
  rw [secantNumber]
  exact Fin.sum_univ_eq_sum_range (fun j => (-1 : ℤ) ^ (j + 2) * ((2 * (n + 1)).choose (2 * (j + 1)) : ℤ) * secantNumber (n - j)) (n + 1)

lemma s0 : secantNumber 0 = 1 := by rw [secantNumber]
lemma s1 : secantNumber 1 = 1 := by
  rw [show secantNumber 1 = secantNumber (0 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0]
lemma s2 : secantNumber 2 = 5 := by
  rw [show secantNumber 2 = secantNumber (1 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1]
lemma s3 : secantNumber 3 = 61 := by
  rw [show secantNumber 3 = secantNumber (2 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2]
lemma s4 : secantNumber 4 = 1385 := by
  rw [show secantNumber 4 = secantNumber (3 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3]
lemma s5 : secantNumber 5 = 50521 := by
  rw [show secantNumber 5 = secantNumber (4 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4]
lemma s6 : secantNumber 6 = 2702765 := by
  rw [show secantNumber 6 = secantNumber (5 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5]
lemma s7 : secantNumber 7 = 199360981 := by
  rw [show secantNumber 7 = secantNumber (6 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6]
lemma s8 : secantNumber 8 = 19391512145 := by
  rw [show secantNumber 8 = secantNumber (7 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7]
lemma s9 : secantNumber 9 = 2404879675441 := by
  rw [show secantNumber 9 = secantNumber (8 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8]
lemma s10 : secantNumber 10 = 370371188237525 := by
  rw [show secantNumber 10 = secantNumber (9 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9]
lemma s11 : secantNumber 11 = 69348874393137901 := by
  rw [show secantNumber 11 = secantNumber (10 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]
lemma s12 : secantNumber 12 = 15514534163557086905 := by
  rw [show secantNumber 12 = secantNumber (11 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
lemma s13 : secantNumber 13 = 4087072509293123892361 := by
  rw [show secantNumber 13 = secantNumber (12 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12]
lemma s14 : secantNumber 14 = 1252259641403629865468285 := by
  rw [show secantNumber 14 = secantNumber (13 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13]
lemma s15 : secantNumber 15 = 441543893249023104553682821 := by
  rw [show secantNumber 15 = secantNumber (14 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14]
lemma s16 : secantNumber 16 = 177519391579539289436664789665 := by
  rw [show secantNumber 16 = secantNumber (15 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15]
lemma s17 : secantNumber 17 = 80723299235887898062168247453281 := by
  rw [show secantNumber 17 = secantNumber (16 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16]
lemma s18 : secantNumber 18 = 41222060339517702122347079671259045 := by
  rw [show secantNumber 18 = secantNumber (17 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17]
lemma s19 : secantNumber 19 = 23489580527043108252017828576198947741 := by
  rw [show secantNumber 19 = secantNumber (18 + 1) from rfl, sec_succ]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18]
end Aux

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a000364.main) := by
  open OMA.S_oeis_a000364 in
  intro h
  obtain ⟨p, hp, hd, hmod⟩ := h 27 (by norm_num)
  have ht : Nat.totient 27 = 18 := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
    norm_num
  rw [ht] at hd
  have hp18 : p ≤ 18 := Nat.le_of_dvd (by norm_num) hd
  have h1 := hmod 1 le_rfl
  have h2 := hmod 2 (by norm_num)
  interval_cases p <;> first
    | (exfalso; revert hd; decide)
    | (simp only [Int.ModEq] at h1; norm_num [s0, s1, s2, s3, s4, s5, s6, s7, s8, s10, s19] at h1; done)
    | (simp only [Int.ModEq] at h2; norm_num [s0, s1, s2, s3, s4, s5, s6, s7, s8, s10, s19] at h2; done)
