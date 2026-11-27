import OMAStatements.S_oeis_a354478

-- Credit: @Ciphore

open Filter OMA.S_oeis_a354478

private theorem stirlingFirst_lower (n k : ℕ) (hn : 4 ≤ n) (hk₀ : 0 < k)
    (hk : k < n) : n * (n - 1) ≤ 2 * n.stirlingFirst k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    by_cases hn' : 4 ≤ n
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk₀.ne'
      rw [Nat.stirlingFirst_succ_succ]
      by_cases hj : j + 1 < n
      · have h := ih (j + 1) hn' (by omega) hj
        have hcompare : n + 1 ≤ n * (n - 1) := by
          have h₁ := Nat.mul_le_mul_left n (show 2 ≤ n - 1 by omega)
          omega
        calc
          (n + 1) * (n + 1 - 1) = n * (n + 1) := by simp [Nat.mul_comm]
          _ ≤ n * (n * (n - 1)) := Nat.mul_le_mul_left n hcompare
          _ ≤ n * (2 * n.stirlingFirst (j + 1)) := Nat.mul_le_mul_left n h
          _ ≤ 2 * (n * n.stirlingFirst (j + 1) + n.stirlingFirst j) := by
            rw [← mul_assoc, mul_comm n 2, mul_assoc]
            omega
      · have hj' : j + 1 = n := by omega
        have h := ih j hn' (by omega) (by omega)
        rw [hj', Nat.stirlingFirst_self, mul_one]
        have he : (n + 1) * (n + 1 - 1) = n * (n - 1) + 2 * n := by
          rw [← hj']
          simp only [Nat.add_sub_cancel]
          ring
        omega
    · have hn₃ : n = 3 := by omega
      subst n
      interval_cases k <;> decide

private theorem error_bound (m : ℕ) (hm : 3 ≤ m) :
    |(rowSum (m + 1) : ℝ) - 1| ≤ 2 / ((m + 1 : ℕ) : ℝ) := by
  have hdiag : (signedStirling (m + 1) (m + 1) : ℝ) = 1 := by
    simp [signedStirling, Nat.stirlingFirst_self]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hterm (j : ℕ) (hj : j ∈ Finset.range m) :
      |(1 : ℝ) / (signedStirling (m + 1) (j + 1) : ℝ)| ≤
        2 / (((m + 1 : ℕ) : ℝ) * m) := by
    have hj' := Finset.mem_range.mp hj
    have hNat : (m + 1) * m ≤ 2 * (m + 1).stirlingFirst (j + 1) := by
      simpa using stirlingFirst_lower (m + 1) (j + 1) (by omega) (by omega) (by omega)
    have hReal : ((m + 1 : ℕ) : ℝ) * m ≤
        2 * ((m + 1).stirlingFirst (j + 1) : ℝ) := by exact_mod_cast hNat
    have hpos : (0 : ℝ) < ((m + 1).stirlingFirst (j + 1) : ℝ) := by
      have hp := mul_pos hnpos hmpos
      linarith
    have habs : |(signedStirling (m + 1) (j + 1) : ℝ)| =
        ((m + 1).stirlingFirst (j + 1) : ℝ) := by
      simp [signedStirling, abs_mul, abs_pow]
    rw [abs_div, abs_one, habs]
    exact (div_le_div_iff₀ hpos (mul_pos hnpos hmpos)).2 (by simpa using hReal)
  simp only [rowSum, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_intCast]
  rw [Finset.sum_range_succ, hdiag, div_one, add_sub_cancel_right]
  calc
    _ ≤ ∑ j ∈ Finset.range m, |(1 : ℝ) / (signedStirling (m + 1) (j + 1) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range m, 2 / (((m + 1 : ℕ) : ℝ) * m) :=
      Finset.sum_le_sum hterm
    _ = 2 / ((m + 1 : ℕ) : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hmpos.ne']

theorem OMA.solution : type_of% @OMA.S_oeis_a354478.main := by
  simp_rw [← Rat.cast_def]
  apply tendsto_iff_norm_sub_tendsto_zero.2
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa only [Real.norm_eq_abs] using error_bound m (by omega)
