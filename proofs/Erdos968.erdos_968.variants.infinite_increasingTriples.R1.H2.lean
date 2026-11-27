import OMAReductions.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1

/-! The normalized n-th prime is at most twice the logarithm of the n-th prime. With
m the n-th prime, exactly n + 1 primes are at most m, and the explicit Chebyshev lower
bound gives (n + 1) log m at least m log 2 - log (m + 1), which exceeds m / 2 from
m = 18 on. -/

theorem OMA.solution :
    OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1.H2 := by
  filter_upwards [Filter.eventually_ge_atTop 18] with n hn
  obtain ⟨m, hm⟩ : ∃ m, m = Nat.nth Nat.Prime n := ⟨_, rfl⟩
  have hmono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hmn : n ≤ m := by
    rw [hm]
    exact hmono.le_apply
  have hm18 : (18:ℝ) ≤ m := by exact_mod_cast le_trans hn hmn
  have hpi : Nat.primeCounting m = n + 1 := by
    rw [hm]
    exact Nat.count_nth_succ (fun hf => absurd hf Nat.infinite_setOfPred_prime)
  have hmpos : (0:ℝ) < m := by linarith
  have hlogm : 0 < Real.log m := Real.log_pos (by linarith)
  have hcheb := Chebyshev.pi_ge m
  rw [div_le_iff₀ hlogm, hpi] at hcheb
  push_cast at hcheb
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h1 : Real.log ((m:ℝ) + 1) ≤ ((m:ℝ) + 1) / 8 - 1 + Real.log 8 := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < ((m:ℝ) + 1) / 8)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    linarith
  have h2 : (m:ℝ) * 0.6931471803 ≤ m * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le hmpos.le
  show Erdos968.u n ≤ 2 * Real.log (Nat.nth Nat.Prime n)
  simp only [Erdos968.u]
  rw [← hm, div_le_iff₀ (by positivity)]
  linarith
