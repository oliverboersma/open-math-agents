import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1

-- Step Erdos936.erdos_936.variants.factorial_add_one.R1.H2: hypothesis H2 of reduction Erdos936.erdos_936.variants.factorial_add_one.R1
-- Credit: @NoahPuckett-IO
-- primorial n ≤ 4^n, and (4^e)^n / n! tends to 0, so eventually C * (4^e)^n < n!.

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H2 := by
  intro C e
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop ((4 : ℝ) ^ e)
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ((4 : ℝ) ^ e) ^ n / (n.factorial : ℝ) < 1 / ((C : ℝ) + 1) :=
    ht.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev] with n hn
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hC : (0 : ℝ) < (C : ℝ) + 1 := by positivity
  rw [div_lt_div_iff₀ hf hC, one_mul] at hn
  have hp : primorial n ^ e ≤ (4 ^ e) ^ n := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (primorial_le_four_pow n) e
  have hpR : ((primorial n : ℕ) : ℝ) ^ e ≤ ((4 : ℝ) ^ e) ^ n := by exact_mod_cast hp
  have hpos : (0 : ℝ) < ((4 : ℝ) ^ e) ^ n := by positivity
  have hreal : ((C * primorial n ^ e : ℕ) : ℝ) < n.factorial := by
    have h1 : ((C * primorial n ^ e : ℕ) : ℝ) ≤ (C : ℝ) * ((4 : ℝ) ^ e) ^ n := by
      push_cast
      exact mul_le_mul_of_nonneg_left hpR (by positivity)
    nlinarith
  exact_mod_cast hreal
