import OMAReductions.R_Erdos242_erdos_242_variants_schinzel_generalization_R1

-- Step Erdos242.erdos_242.variants.schinzel_generalization.R1.H2
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1.H2 := by
  intro a n ha h2a hrem
  have hmod_lt : n % a < a := Nat.mod_lt n ha
  by_cases h0 : n % a = 0
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    have hk2 : 2 ≤ k := by nlinarith
    have hkk1 : 2 ≤ k * (k + 1) := by nlinarith
    refine ⟨k + 1, k * (k + 1) + 1, k * (k + 1) * (k * (k + 1) + 1),
      by omega, by nlinarith, lt_mul_of_one_lt_left (by positivity) (by omega), ?_⟩
    have haq : (a : ℚ) ≠ 0 := by positivity
    have hkq : (k : ℚ) ≠ 0 := by positivity
    have h1q : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have h2q : ((k * (k + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [hk]
    push_cast
    field_simp
    ring
  · have hle : a ≤ n % a + 2 := hrem.resolve_left h0
    by_cases h1 : n % a + 1 = a
    · have hdvd : a ∣ n + 1 := by
        rw [Nat.dvd_iff_mod_eq_zero]
        have : (n % a + 1) % a = 0 := by rw [h1, Nat.mod_self]
        rwa [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl a), ← Nat.add_mod] at this
      obtain ⟨k, hk⟩ := hdvd
      have hk2 : 2 ≤ k := by nlinarith
      have hn1 : 1 ≤ n := by omega
      have hkn2 : 2 ≤ k * n := by nlinarith
      refine ⟨k, k * n + 1, k * n * (k * n + 1),
        by omega, by nlinarith, lt_mul_of_one_lt_left (by positivity) (by omega), ?_⟩
      have hnq : (n : ℚ) ≠ 0 := by positivity
      have hkq : (k : ℚ) ≠ 0 := by positivity
      have h1q : ((k * n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hrel : (a : ℚ) * (k : ℚ) = (n : ℚ) + 1 := by exact_mod_cast hk.symm
      push_cast
      field_simp
      linear_combination ((k : ℚ) * (n : ℚ) + 1) * hrel
    · have h2eq : n % a + 2 = a := by omega
      have ha3 : 3 ≤ a := by omega
      have hdvd : a ∣ n + 2 := by
        rw [Nat.dvd_iff_mod_eq_zero]
        have : (n % a + 2) % a = 0 := by rw [h2eq, Nat.mod_self]
        rwa [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl a), ← Nat.add_mod] at this
      obtain ⟨k, hk⟩ := hdvd
      have hk3 : 3 ≤ k := by nlinarith
      have hn6 : 6 ≤ n := by omega
      rcases Nat.even_or_odd (k * n) with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hm2 : k * n = 2 * m := by omega
        have hm3 : 2 ≤ m := by nlinarith
        have hmk : k < m + 1 := by nlinarith
        refine ⟨k, m + 1, m * (m + 1), by omega, hmk,
          lt_mul_of_one_lt_left (by positivity) (by omega), ?_⟩
        have hnq : (n : ℚ) ≠ 0 := by positivity
        have hkq : (k : ℚ) ≠ 0 := by positivity
        have hmq : (m : ℚ) ≠ 0 := by positivity
        have hm1q : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        have hrel : (a : ℚ) * (k : ℚ) = (n : ℚ) + 2 := by exact_mod_cast hk.symm
        have hknq : (k : ℚ) * (n : ℚ) = 2 * (m : ℚ) := by exact_mod_cast hm2
        push_cast
        field_simp
        linear_combination ((m : ℚ) * ((m : ℚ) + 1)) * hrel - ((m : ℚ) + 1) * hknq
      · let u := m + 1
        have hu2 : 2 * u = k * n + 1 := by omega
        have huk : k < u := by nlinarith
        have hkn2 : 2 ≤ k * n := by nlinarith
        refine ⟨k, u, u * (k * n), by omega, huk,
          lt_mul_of_one_lt_right (by positivity) (by omega), ?_⟩
        have hnq : (n : ℚ) ≠ 0 := by positivity
        have hkq : (k : ℚ) ≠ 0 := by positivity
        have huq : (u : ℚ) ≠ 0 := by positivity
        have hrel : (a : ℚ) * (k : ℚ) = (n : ℚ) + 2 := by exact_mod_cast hk.symm
        have huq2 : 2 * (u : ℚ) = (k : ℚ) * (n : ℚ) + 1 := by exact_mod_cast hu2
        push_cast
        field_simp
        linear_combination (u : ℚ) * hrel + huq2
