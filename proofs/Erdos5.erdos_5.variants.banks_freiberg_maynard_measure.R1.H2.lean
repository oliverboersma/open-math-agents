import OMAReductions.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_measure_R1

-- Step Erdos5.erdos_5.variants.banks_freiberg_maynard_measure.R1.H2: hypothesis H2 of reduction Erdos5.erdos_5.variants.banks_freiberg_maynard_measure.R1
-- Credit: @ishaanzee
-- Proof: n + 2 <= p_n gives the lower bound; Chebyshev's pi_ge at p_n (where pi(p_n) = n + 1)
-- gives p_n <= 2 (n + 3) log p_n, hence log p_n <= c + log n + log (a + 2 log n), and the
-- ratio is squeezed to 1.

open Filter Real
open scoped Topology

namespace MerikoskiAux

lemma pc_nth (n : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, ← Nat.primeCounting',
    Nat.primeCounting'_nth_eq, if_pos (Nat.prime_nth_prime n)]

/-- `p_n ≤ 2 (n + 3) log p_n`, from Chebyshev's lower bound for `π`. -/
lemma nth_le (n : ℕ) :
    ((Nat.nth Nat.Prime n : ℕ) : ℝ) ≤ 2 * ((n : ℝ) + 3) * log (Nat.nth Nat.Prime n) := by
  set P := Nat.nth Nat.Prime n with hP
  have hP2 : 2 ≤ P := le_trans (by omega) (Nat.add_two_le_nth_prime n)
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP2
  have hlogP : 0 < log (P : ℝ) := log_pos (by linarith)
  have hpi := Chebyshev.pi_ge P
  rw [pc_nth, div_le_iff₀ hlogP] at hpi
  push_cast at hpi
  have hlog1 : log ((P : ℝ) + 1) ≤ 2 * log (P : ℝ) := by
    rw [← log_rpow (by linarith)]
    apply log_le_log (by linarith)
    rw [show ((P : ℝ) ^ (2 : ℝ)) = (P : ℝ) * P by rw [rpow_two, sq]]
    nlinarith
  have hl2 := log_two_gt_d9
  nlinarith

lemma log_le_two_sqrt {L : ℝ} (hL : 0 < L) : log L ≤ 2 * √L := by
  have hs : 0 < √L := sqrt_pos.2 hL
  have h1 := log_le_sub_one_of_pos hs
  rw [log_sqrt hL.le] at h1
  linarith

/-- `log p_n ≤ c + log n + log (a + 2 log n)` for `n ≥ 1`. -/
lemma log_nth_le (n : ℕ) (hn : 1 ≤ n) :
    log (Nat.nth Nat.Prime n) ≤ (log 2 + log 4) + log n +
      log ((16 + 2 * log 2 + 2 * log 4) + 2 * log n) := by
  set P := Nat.nth Nat.Prime n with hP
  have hP2 : 2 ≤ P := le_trans (by omega) (Nat.add_two_le_nth_prime n)
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP2
  set L := log (P : ℝ) with hLdef
  have hL : 0 < L := log_pos (by linarith)
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb := nth_le n
  rw [← hP] at hb
  -- take logs
  have h1 : L ≤ log 2 + log ((n : ℝ) + 3) + log L := by
    have : L ≤ log (2 * ((n : ℝ) + 3) * L) := log_le_log (by linarith) hb
    rwa [log_mul (by positivity) hL.ne', log_mul (by norm_num) (by positivity)] at this
  have h4 : log ((n : ℝ) + 3) ≤ log 4 + log n := by
    rw [← log_mul (by norm_num) (by positivity)]
    exact log_le_log (by positivity) (by linarith)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hl4 : 0 < log (4 : ℝ) := log_pos (by norm_num)
  have hln : 0 ≤ log (n : ℝ) := log_nonneg hnr
  -- a crude bound on L
  have hcrude : L ≤ 16 + 2 * log 2 + 2 * log 4 + 2 * log n := by
    have hsq := log_le_two_sqrt hL
    by_cases h16 : L ≤ 16
    · linarith
    · push_neg at h16
      have hs4 : 4 ≤ √L := by
        rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
        exact sqrt_le_sqrt h16.le
      have hss : √L * √L = L := mul_self_sqrt hL.le
      nlinarith
  have h5 : log L ≤ log ((16 + 2 * log 2 + 2 * log 4) + 2 * log n) :=
    log_le_log hL (by linarith)
  linarith

lemma tendsto_aux (a c : ℝ) :
    Tendsto (fun t : ℝ => (c + log (a + 2 * t)) / t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => c / t) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hlin : Tendsto (fun t : ℝ => a + 2 * t) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (by norm_num))
  have h2 := (tendsto_pow_log_div_mul_add_atTop (1 / 2) (-a / 2) 1 (by norm_num)).comp hlin
  have h2' : Tendsto (fun t : ℝ => log (a + 2 * t) / t) atTop (𝓝 0) := by
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp, pow_one]
    congr 1
    ring
  have := h1.add h2'
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [add_div]

end MerikoskiAux

open MerikoskiAux

theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_measure_R1.H2 := by
  unfold OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_measure_R1.H2
  set a : ℝ := 16 + 2 * log 2 + 2 * log 4
  set c : ℝ := log 2 + log 4
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun n : ℕ => 1 + (c + log (a + 2 * log n)) / log n) atTop (𝓝 1) := by
    have := (tendsto_aux a c).comp hlog
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hl : 0 < log (n : ℝ) := log_pos hn'
    rw [le_div_iff₀ hl, one_mul]
    apply log_le_log (by linarith)
    exact_mod_cast le_trans (by omega) (Nat.add_two_le_nth_prime n)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (1 : ℝ) < n := by exact_mod_cast hn
    have hl : 0 < log (n : ℝ) := log_pos hn'
    have hb := log_nth_le n (by omega)
    rw [div_le_iff₀ hl, add_mul, one_mul, div_mul_cancel₀ _ hl.ne']
    linarith
