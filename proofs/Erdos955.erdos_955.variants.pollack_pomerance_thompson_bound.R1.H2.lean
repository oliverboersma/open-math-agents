import OMAReductions.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1

-- Step Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound.R1.H2
-- Credit: @caa1982

open Finset

private lemma sum_inv_le_one_add_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log (n : ℝ) := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hset : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : m + 1 ∉ Finset.Icc 1 m := by simp
      rw [hset, Finset.sum_insert hnotmem]
      have ihm := ih hm
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hm1R : (0 : ℝ) < (m : ℝ) + 1 := by linarith
      have hlog : Real.log ((m : ℝ) / ((m : ℝ) + 1)) ≤ (m : ℝ) / ((m : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hmR hm1R)
      rw [Real.log_div hmR.ne' hm1R.ne'] at hlog
      have hstep : 1 / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := by
        have heq : (m : ℝ) / ((m : ℝ) + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by
          field_simp
          ring
        linarith
      push_cast
      linarith

theorem OMA.solution : OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1.H2 := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsig : (ArithmeticFunction.sigma 1 n : ℝ) = (n : ℝ) * ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ) := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_bij (fun d _ => n / d) ?_ ?_ ?_ ?_
    · intro d hd
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hn0⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      have h1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd₁)
      have h2 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd₂)
      have hpos : 0 < n / d₁ := Nat.div_pos (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd₁))
        (Nat.pos_of_mem_divisors hd₁)
      have : d₁ * (n / d₁) = d₂ * (n / d₁) := by rw [h1, heq, h2]
      exact Nat.eq_of_mul_eq_mul_right hpos this
    · intro d hd
      refine ⟨n / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hn0⟩, ?_⟩
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hn0
    · intro d hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      have hdiv_pos : (0 : ℝ) < ((n / d : ℕ) : ℝ) := by
        exact_mod_cast Nat.div_pos (Nat.le_of_dvd hn hdvd) (Nat.pos_of_mem_divisors hd)
      have hmul : (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast Nat.mul_div_cancel' hdvd
      field_simp [hdiv_pos.ne']
      linarith
  rw [hsig]
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)⟩
  have hsum_le : ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ) ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / (k : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  exact mul_le_mul_of_nonneg_left (hsum_le.trans (sum_inv_le_one_add_log n hn)) hnR.le
