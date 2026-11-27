import FormalConjectures.Paper.PartitionParity

/-!
This reduction follows the range split in Bellaïche and Nicolas, *Parité des coefficients de
formes modulaires*, Theorem 6. The first hypothesis uses Nicolas's earlier estimate (1.14).
The second separates the final modular-form estimate (6.20), with the parameter bound (6.14).
The rest of the proof checks the numerical comparisons and the small range directly in Lean.
-/

namespace OMA.R_PartitionParity_bellaiche_nicolas_odd_explicit_R1

open Real

/-- The earlier explicit lower bound on the middle range of Theorem 6. -/
def H1 : Prop := ∀ x : ℝ, 7 ≤ x → x ≤ exp (exp 24) / 8 →
  4.57 * sqrt x / log x ≤
    ({n : ℕ | n ≤ x ∧ Odd (Nat.partitionNumber n)}.ncard : ℝ)

/-- The large-range estimate before eliminating the nilpotence parameter. -/
def H2 : Prop := ∀ x : ℝ, 2 ≤ x → exp (exp 24) / 8 < x →
  ∃ h : ℕ, log (log x) ≤ 8 * (h : ℝ) ∧
    0.28 * exp ((h : ℝ) - 2) * sqrt x / log x ≤
      ({n : ℕ | n ≤ x ∧ Odd (Nat.partitionNumber n)}.ncard : ℝ)

lemma oddPartitionBound_small (x : ℝ) (hx : 2 ≤ x) (hx7 : x ≤ 7) :
    0.037 * Real.sqrt x / Real.log x ^ (7 / 8 : ℝ) ≤
      ({n : ℕ | n ≤ x ∧ Odd (Nat.partitionNumber n)}.ncard : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log x :=
    (show (1 / 2 : ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]).trans
      (Real.log_le_log (by norm_num) hx)
  have hpow : (1 / 2 : ℝ) ≤ Real.log x ^ (7 / 8 : ℝ) := by
    calc
      (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (1 : ℝ) := by norm_num
      _ ≤ (1 / 2 : ℝ) ^ (7 / 8 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
      _ ≤ Real.log x ^ (7 / 8 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hlog (by norm_num)
  have hsqrt : Real.sqrt x ≤ 3 :=
    (Real.sqrt_le_left (by norm_num)).2 (by linarith)
  have hbound : 0.037 * Real.sqrt x / Real.log x ^ (7 / 8 : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hpow)).2
    linarith
  have hfinite : {n : ℕ | n ≤ x ∧ Odd (Nat.partitionNumber n)}.Finite := by
    refine (Set.finite_Iic ⌊x⌋₊).subset ?_
    intro n hn
    exact (Nat.le_floor_iff hx0).2 hn.1
  have hnonempty : {n : ℕ | n ≤ x ∧ Odd (Nat.partitionNumber n)}.Nonempty := by
    refine ⟨0, ?_, ?_⟩
    · simpa using hx0
    · rw [Nat.partitionNumber_zero]
      exact odd_one
  have hcount : 1 ≤ ({n : ℕ | n ≤ x ∧ Odd (Nat.partitionNumber n)}.ncard : ℝ) := by
    exact_mod_cast hnonempty.ncard_pos hfinite
  exact hbound.trans hcount

lemma odd_partition_bound_of_coefficient {x c : ℝ} (hlog : 0 < log x)
    (hc : 0.037 * (log x) ^ (1 / 8 : ℝ) ≤ c) :
    0.037 * √x / (log x) ^ (7 / 8 : ℝ) ≤ c * √x / log x := by
  have hpow : 0 < (log x) ^ (7 / 8 : ℝ) := rpow_pos_of_pos hlog _
  have hsplit : (log x) ^ (7 / 8 : ℝ) * (log x) ^ (1 / 8 : ℝ) = log x := by
    rw [← rpow_add hlog, show (7 / 8 : ℝ) + 1 / 8 = 1 by norm_num, rpow_one]
  apply (div_le_div_iff₀ hpow hlog).2
  calc
    (0.037 * √x) * log x =
        (0.037 * √x) * ((log x) ^ (7 / 8 : ℝ) * (log x) ^ (1 / 8 : ℝ)) :=
      congrArg ((0.037 * √x) * ·) hsplit.symm
    _ = (0.037 * (log x) ^ (1 / 8 : ℝ)) * √x * (log x) ^ (7 / 8 : ℝ) := by ring
    _ ≤ (c * √x) * (log x) ^ (7 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sqrt_nonneg x)) hpow.le

lemma odd_partition_medium_bridge {x : ℝ} (hx : 7 ≤ x) (hmax : x ≤ exp (exp 24) / 8) :
    0.037 * √x / (log x) ^ (7 / 8 : ℝ) ≤ 4.57 * √x / log x := by
  have hlog : 0 < log x := log_pos (by linarith)
  have hlog_upper : log x ≤ exp 24 := by
    have hxx := hmax.trans (div_le_self (exp_pos _).le (by norm_num : (1 : ℝ) ≤ 8))
    calc
      log x ≤ log (exp (exp 24)) :=
        (log_le_log_iff (by linarith) (exp_pos _)).2 hxx
      _ = exp 24 := log_exp _
  have hpow : (log x) ^ (1 / 8 : ℝ) ≤ exp 3 := by
    calc
      (log x) ^ (1 / 8 : ℝ) ≤ (exp 24) ^ (1 / 8 : ℝ) :=
        rpow_le_rpow hlog.le hlog_upper (by norm_num)
      _ = exp 3 := by
        rw [rpow_def_of_pos (exp_pos 24), log_exp]
        norm_num
  have hexp : exp 3 ≤ 27 := by
    calc
      exp 3 = (exp 1) ^ (3 : ℕ) := by rw [← exp_nat_mul]; norm_num
      _ ≤ (3 : ℝ) ^ (3 : ℕ) := pow_le_pow_left₀ (exp_pos _).le exp_one_lt_three.le _
      _ = 27 := by norm_num
  apply odd_partition_bound_of_coefficient hlog
  have := hpow.trans hexp
  linarith

lemma odd_partition_large_bridge {x h : ℝ} (hx : 2 ≤ x) (hh : log (log x) ≤ 8 * h) :
    0.037 * √x / (log x) ^ (7 / 8 : ℝ) ≤ 0.28 * exp (h - 2) * √x / log x := by
  have hlog : 0 < log x := log_pos (by linarith)
  have hpow : (log x) ^ (1 / 8 : ℝ) ≤ exp h := by
    rw [rpow_def_of_pos hlog]
    exact exp_le_exp.mpr (by linarith)
  have hexp : exp 2 ≤ (2.72 : ℝ) ^ (2 : ℕ) := by
    rw [show exp 2 = (exp 1) ^ (2 : ℕ) by rw [← exp_nat_mul]; norm_num]
    exact pow_le_pow_left₀ (exp_pos _).le (by linarith [exp_one_lt_d9]) _
  have hconst : (0.037 : ℝ) * exp 2 ≤ 0.28 := by nlinarith only [hexp]
  apply odd_partition_bound_of_coefficient hlog
  calc
    0.037 * (log x) ^ (1 / 8 : ℝ) ≤ 0.037 * exp h := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ 0.28 * exp (h - 2) := by
      rw [exp_sub, ← mul_div_assoc]
      apply (le_div_iff₀ (exp_pos 2)).2
      calc
        (0.037 * exp h) * exp 2 = (0.037 * exp 2) * exp h := by ring
        _ ≤ 0.28 * exp h := mul_le_mul_of_nonneg_right hconst (exp_pos _).le

theorem main : H1 → H2 → type_of% @PartitionParity.bellaiche_nicolas.odd_explicit := by
  intro hmid hlarge x hx
  by_cases hsmall : x ≤ 7
  · exact oddPartitionBound_small x hx hsmall
  by_cases hthreshold : x ≤ exp (exp 24) / 8
  · have hx7 : 7 ≤ x := (lt_of_not_ge hsmall).le
    exact (odd_partition_medium_bridge hx7 hthreshold).trans (hmid x hx7 hthreshold)
  · obtain ⟨h, hlog, hbound⟩ := hlarge x hx (lt_of_not_ge hthreshold)
    exact (odd_partition_large_bridge hx hlog).trans hbound

end OMA.R_PartitionParity_bellaiche_nicolas_odd_explicit_R1
