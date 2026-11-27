import FormalConjectures.ErdosProblems.«820»

-- Reduction Erdos820.erdos_820.variants.erdos_lower.R1 of Erdős Problem 820 — erdos lower
-- Credit: @MrZaow
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1

def H1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in Filter.atTop,
    (n : ℝ) ^ (c / Real.log (Real.log (n : ℝ)) ^ 2) ≤
      (((Finset.range (n + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ n)).card : ℝ)

def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∏ p ∈ (Finset.range (n + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ n), p) <
      Erdos820.H n ^ 2

lemma two_pow_card_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    2 ^ S.card ≤ ∏ p ∈ S, p := by
  calc 2 ^ S.card = ∏ _p ∈ S, (2 : ℕ) := (Finset.prod_const 2).symm
    _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod' hS

lemma log_div_log_log_sq_tendsto :
    Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ^ 2)
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro M
  set K : ℝ := max M 1
  have hK_pos : 0 < K := lt_of_lt_of_le one_pos (le_max_right M 1)
  have hMK : M ≤ K := le_max_left M 1
  refine ⟨Nat.ceil (Real.exp ((16 * K) ^ 2 + 20)), fun n hn => ?_⟩
  have hN_le : Real.exp ((16 * K) ^ 2 + 20) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.ceil_le.mp hn)
  have hn_pos : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hN_le
  set u : ℝ := Real.log (n : ℝ)
  have hu_ge : (16 * K) ^ 2 + 20 ≤ u := by
    dsimp [u]
    exact (Real.le_log_iff_exp_le hn_pos).mpr hN_le
  have hu20 : 20 ≤ u := by linarith [sq_nonneg (16 * K)]
  have hu_pos : 0 < u := by linarith
  have hexp2 : Real.exp 2 < u := by
    have h1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [sq, ← Real.exp_add]
      norm_num
    nlinarith [Real.exp_pos 1]
  have hlogu_gt : 2 < Real.log u := (Real.lt_log_iff_exp_lt hu_pos).mpr hexp2
  have hlogu_pos : 0 < Real.log u := by linarith
  have hsr_pos : 0 < Real.sqrt (Real.sqrt u) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hu_pos)
  have hlog_sr : Real.log (Real.sqrt (Real.sqrt u)) ≤ Real.sqrt (Real.sqrt u) := by
    linarith [Real.log_le_sub_one_of_pos hsr_pos]
  have hlog_eq : Real.log (Real.sqrt (Real.sqrt u)) = Real.log u / 4 := by
    rw [Real.log_sqrt (Real.sqrt_nonneg u), Real.log_sqrt hu_pos.le]
    ring
  have hlogu_le : Real.log u ≤ 4 * Real.sqrt (Real.sqrt u) := by linarith
  have hlogu_sq_le : Real.log u ^ 2 ≤ 16 * Real.sqrt u := by
    have hsq : Real.log u ^ 2 ≤ (4 * Real.sqrt (Real.sqrt u)) ^ 2 := by
      nlinarith [hlogu_pos, hlogu_le]
    have hsr_sq : (4 * Real.sqrt (Real.sqrt u)) ^ 2 = 16 * Real.sqrt u := by
      calc (4 * Real.sqrt (Real.sqrt u)) ^ 2 = 16 * Real.sqrt (Real.sqrt u) ^ 2 := by ring
        _ = 16 * Real.sqrt u := by rw [Real.sq_sqrt (Real.sqrt_nonneg u)]
    linarith
  have hsqrt_u_ge : 16 * K ≤ Real.sqrt u := by
    refine Real.le_sqrt_of_sq_le ?_
    linarith
  have hdiv : Real.sqrt u / 16 ≤ u / Real.log u ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (sq_pos_of_pos hlogu_pos)]
    have hmul : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu_pos.le
    nlinarith [Real.sqrt_nonneg u]
  linarith

theorem main : H1 → H2 → type_of% @Erdos820.erdos_820.variants.erdos_lower := by
  rintro ⟨c, hc, hfreq⟩ h2
  refine ⟨c / 2, by positivity, ?_⟩
  have h_ev : ∀ᶠ n : ℕ in Filter.atTop,
      27 ≤ n ∧ 2 / Real.log 2 ≤ (n : ℝ) ^ ((c / 2) / Real.log (Real.log (n : ℝ)) ^ 2) := by
    have h_tend :
        Filter.Tendsto
          (fun n : ℕ => (c / 2) * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ^ 2))
          Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop (by positivity) log_div_log_log_sq_tendsto
    have h_ge := (Filter.tendsto_atTop.mp h_tend) (Real.log (2 / Real.log 2))
    filter_upwards [h_ge, Filter.eventually_ge_atTop 27] with n hn hn27
    refine ⟨hn27, ?_⟩
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    rw [Real.rpow_def_of_pos hn_pos]
    have hmul :
        Real.log (n : ℝ) * ((c / 2) / Real.log (Real.log (n : ℝ)) ^ 2) =
          (c / 2) * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ^ 2) := by ring
    rw [hmul]
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpos_rhs : 0 < 2 / Real.log 2 := div_pos two_pos hlog2_pos
    calc 2 / Real.log 2 = Real.exp (Real.log (2 / Real.log 2)) := (Real.exp_log hpos_rhs).symm
      _ ≤ Real.exp ((c / 2) * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)) ^ 2)) :=
        Real.exp_le_exp.mpr hn
  refine (hfreq.and_eventually h_ev).mono ?_
  rintro n ⟨hcard, hn27, hA_lb⟩
  set S := (Finset.range (n + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ n)
  set A : ℝ := (n : ℝ) ^ ((c / 2) / Real.log (Real.log (n : ℝ)) ^ 2)
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hAA : A * A = (n : ℝ) ^ (c / Real.log (Real.log (n : ℝ)) ^ 2) := by
    dsimp [A]
    rw [← Real.rpow_add hn_pos]
    congr 1
    ring
  have hA_sq : A * A ≤ (S.card : ℝ) := hAA ▸ hcard
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2A : 2 * A ≤ (S.card : ℝ) * Real.log 2 := by
    have h1 : 2 ≤ A * Real.log 2 := (div_le_iff₀ hlog2_pos).mp hA_lb
    have hA_nonneg : 0 ≤ A := Real.rpow_nonneg (Nat.cast_nonneg n) _
    nlinarith
  have hexp_sq : Real.exp A ^ 2 < (Erdos820.H n : ℝ) ^ 2 := by
    calc Real.exp A ^ 2 = Real.exp (2 * A) := by rw [sq, ← Real.exp_add, two_mul]
      _ ≤ Real.exp ((S.card : ℝ) * Real.log 2) := Real.exp_le_exp.mpr h2A
      _ = (2 : ℝ) ^ S.card := by
        rw [mul_comm, ← Real.rpow_def_of_pos two_pos, Real.rpow_natCast]
      _ = ((2 ^ S.card : ℕ) : ℝ) := by norm_cast
      _ ≤ ((∏ p ∈ S, p : ℕ) : ℝ) := by
        exact_mod_cast
          two_pow_card_le_prod S (fun p hp => (Finset.mem_filter.mp hp).2.1.two_le)
      _ < ((Erdos820.H n ^ 2 : ℕ) : ℝ) := by exact_mod_cast h2 n (by omega)
      _ = (Erdos820.H n : ℝ) ^ 2 := by norm_cast
  have hH_nonneg : (0 : ℝ) ≤ (Erdos820.H n : ℝ) := Nat.cast_nonneg _
  nlinarith [Real.exp_pos A]

end OMA.R_Erdos820_erdos_820_variants_erdos_lower_R1
