import OMAReductions.R_Erdos687_erdos_687_variants_iwaniec_R1
import Mathlib

/-!
Lower bound in Mertens' third theorem: the product of (1 - 1/p) over primes p ≤ x is at
least 1/(3 log x) for x ≥ 3, and equals 1/2 at x = 2.

Credit: the explicit Mertens bound is the merged proof
proofs/Erdos1141.erdos_1141.variants.mertens_third.lean by Sebastian Bachmaier (PR #1431),
reused verbatim (namespace OMA_M3); only the final step x = 2 and the change from 1 / p to
p⁻¹ are new.
-/


namespace OMA_M3
open Real Finset

noncomputable def Sm (n : ℕ) : ℝ := ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p / p
noncomputable def Lm (n : ℕ) : ℝ := ∑ p ∈ (range (n + 1)).filter Nat.Prime, -Real.log (1 - 1 / (p:ℝ))
noncomputable def Qm (n : ℕ) : ℝ := ∏ p ∈ (range (n + 1)).filter Nat.Prime, (1 - 1 / (p:ℝ))
noncomputable def cM : ℝ := 2 * Real.log 2 - 1 + 1 / 12
noncomputable def Hm (n : ℕ) : ℝ :=
  Lm n - Real.log (Real.log n) + (Real.log n + cM - Sm n) / Real.log n + 1 / n

lemma filter_succ (n : ℕ) : (range (n + 2)).filter Nat.Prime =
    if (n+1).Prime then insert (n+1) ((range (n+1)).filter Nat.Prime)
    else (range (n+1)).filter Nat.Prime := by
  rw [Finset.range_add_one, Finset.filter_insert]

lemma not_mem_filter (n : ℕ) : n + 1 ∉ (range (n+1)).filter Nat.Prime := by simp

lemma Sm_succ (n : ℕ) : Sm (n+1) = Sm n +
    (if (n+1).Prime then Real.log ((n:ℝ)+1) / ((n:ℝ)+1) else 0) := by
  unfold Sm
  rw [filter_succ]
  split_ifs
  · rw [sum_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Lm_succ (n : ℕ) : Lm (n+1) = Lm n +
    (if (n+1).Prime then -Real.log (1 - 1 / ((n:ℝ)+1)) else 0) := by
  unfold Lm
  rw [filter_succ]
  split_ifs
  · rw [sum_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Qm_succ (n : ℕ) : Qm (n+1) = Qm n *
    (if (n+1).Prime then (1 - 1 / ((n:ℝ)+1)) else 1) := by
  unfold Qm
  rw [filter_succ]
  split_ifs
  · rw [prod_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Qm_nonneg (n : ℕ) : 0 ≤ Qm n := by
  unfold Qm
  apply prod_nonneg
  intro p hp
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
  have : 1 / (p:ℝ) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
  linarith

lemma Qm_anti (n : ℕ) : ∀ m, n ≤ m → Qm m ≤ Qm n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih =>
    rw [Qm_succ]
    refine le_trans ?_ ih
    split_ifs
    · have h0 := Qm_nonneg m
      have h1 : (0:ℝ) ≤ 1 / ((m:ℝ)+1) := by positivity
      nlinarith
    · simp

lemma Qm_eq_exp (n : ℕ) : Qm n = Real.exp (- Lm n) := by
  unfold Qm Lm
  rw [← sum_neg_distrib, Real.exp_sum]
  apply prod_congr rfl
  intro p hp
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
  have : 0 < 1 - 1 / (p:ℝ) := by
    have : 1 / (p:ℝ) < 1 := by rw [div_lt_iff₀ (by linarith)]; linarith
    linarith
  rw [neg_neg, Real.exp_log this]

lemma log_fact_le (t : ℕ) (ht : 1 ≤ t) :
    Real.log (t.factorial) ≤ ((t:ℝ)+1) * Real.log t - t + 1 := by
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    have htp : (0:ℝ) < t := by exact_mod_cast ht
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have h1 := Real.one_sub_inv_le_log_of_pos (x := ((t:ℝ)+1)/t) (by positivity)
    rw [Real.log_div (by positivity) (by positivity), inv_div] at h1
    have h2 : 1 - (t:ℝ) / (t+1) = 1 / (t+1) := by field_simp; ring
    rw [h2] at h1
    have h3 : 1 ≤ ((t:ℝ)+1) * (Real.log (t+1) - Real.log t) := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    push_cast
    nlinarith

lemma sum_div_log_le (t : ℕ) :
    ∑ p ∈ (range (t+1)).filter Nat.Prime, ((t / p : ℕ) : ℝ) * Real.log p
      ≤ Real.log (t.factorial) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (s := (range (t+1)).filter Nat.Prime) ?_ ?_)
  · apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpt : p ≤ t := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
    apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
    rw [Nat.factorization_factorial hpp (Nat.lt_succ_of_le (Nat.log_le_self p t))]
    have h1 : 1 ∈ Ico 1 (t+1) := by
      simp only [mem_Ico]; have := hpp.two_le; omega
    have := Finset.single_le_sum (f := fun i => t / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simp only [pow_one] at this
    exact_mod_cast this
  · intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpt : p ≤ t := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
    rw [Nat.support_factorization, Nat.mem_primeFactors]
    exact ⟨hpp, Nat.dvd_factorial hpp.pos hpt, Nat.factorial_ne_zero t⟩
  · intro p _ _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

lemma theta_le (t : ℕ) :
    ∑ p ∈ (range (t+1)).filter Nat.Prime, Real.log p ≤ 2 * Real.log 2 * t := by
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg t)
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range] at h
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [this] at h
  linarith

lemma log_aux (t : ℝ) (ht : 64 ≤ t) : Real.log t + 1 ≤ t / 12 := by
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
  have h1 := Real.log_le_sub_one_of_pos (x := t / 64) (by positivity)
  rw [Real.log_div (by positivity) (by norm_num), h64] at h1
  have := Real.log_two_lt_d9
  linarith

lemma mertens1 (t : ℕ) (ht : 64 ≤ t) : Sm t ≤ Real.log t + cM := by
  have htr : (64:ℝ) ≤ t := by exact_mod_cast ht
  have h1 : (t:ℝ) * Sm t ≤ ∑ p ∈ (range (t+1)).filter Nat.Prime,
      (((t / p : ℕ) : ℝ) * Real.log p + Real.log p) := by
    unfold Sm
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp2 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hlt := Nat.lt_mul_div_succ t hpp.pos
    have hle : (t:ℝ) ≤ p * (((t / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt.le
    have : (t:ℝ) / p ≤ ((t / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp2]; linarith
    have hl := Real.log_natCast_nonneg p
    calc (t:ℝ) * (Real.log p / p) = ((t:ℝ) / p) * Real.log p := by ring
      _ ≤ (((t / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right this hl
      _ = _ := by ring
  rw [sum_add_distrib] at h1
  have h2 := sum_div_log_le t
  have h3 := theta_le t
  have h4 := log_fact_le t (by omega)
  have h5 := log_aux t htr
  have htp : (0:ℝ) < t := by linarith
  have key : (t:ℝ) * Sm t ≤ t * (Real.log t + cM) := by
    unfold cM; nlinarith
  exact le_of_mul_le_mul_left key htp

lemma key_ineq (a b u : ℝ) (ha : 0 < a) (hab : a < b) (hu : -a ≤ u) :
    u / b - Real.log b ≤ u / a - Real.log a := by
  have hb : 0 < b := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (x := b / a) (by positivity)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h1
  have e1 : u / b - u / a = -(u * (b - a)) / (a * b) := by field_simp; ring
  have e2 : 1 - a / b = (b - a) / b := by field_simp
  have h2 : -(u * (b - a)) / (a * b) ≤ (b - a) / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    have : 0 < b - a := by linarith
    have : -u * (b - a) ≤ a * (b - a) := mul_le_mul_of_nonneg_right (by linarith) this.le
    nlinarith
  linarith

lemma H_step (m : ℕ) (hm : 64 ≤ m) : Hm (m+1) ≤ Hm m := by
  have hS := mertens1 m hm
  have hmr : (64:ℝ) ≤ m := by exact_mod_cast hm
  have ha : 0 < Real.log m := Real.log_pos (by linarith)
  have hab : Real.log m < Real.log ((m:ℝ)+1) := Real.log_lt_log (by linarith) (by linarith)
  have hb : 0 < Real.log ((m:ℝ)+1) := by linarith
  have K := key_ineq _ _ (cM - Sm m) ha hab (by linarith)
  have hD : -Real.log (1 - 1 / ((m:ℝ)+1)) ≤ 1 / m := by
    have e : 1 - 1 / ((m:ℝ)+1) = ((m:ℝ)+1)⁻¹ * m := by field_simp; ring
    have := Real.log_le_sub_one_of_pos (x := ((m:ℝ)+1) / m) (by positivity)
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_inv]
    rw [Real.log_div (by positivity) (by positivity)] at this
    have e2 : ((m:ℝ)+1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  have hinv : 1 / ((m:ℝ)+1) ≤ 1 / m := one_div_le_one_div_of_le (by linarith) (by linarith)
  have hinv0 : 0 ≤ 1 / ((m:ℝ)+1) := by positivity
  have ea : (Real.log m + cM - Sm m) / Real.log m = 1 + (cM - Sm m) / Real.log m := by
    field_simp; ring
  unfold Hm
  rw [Lm_succ, Sm_succ]
  push_cast
  rw [ea]
  split_ifs
  · have eb : (Real.log ((m:ℝ)+1) + cM - (Sm m + Real.log ((m:ℝ)+1) / ((m:ℝ)+1)))
        / Real.log ((m:ℝ)+1) = 1 + (cM - Sm m) / Real.log ((m:ℝ)+1) - 1 / ((m:ℝ)+1) := by
      field_simp; ring
    rw [eb]; linarith
  · have eb : (Real.log ((m:ℝ)+1) + cM - (Sm m + 0))
        / Real.log ((m:ℝ)+1) = 1 + (cM - Sm m) / Real.log ((m:ℝ)+1) := by
      field_simp; ring
    rw [eb]; linarith

lemma H_le (n : ℕ) (hn : 64 ≤ n) : Hm n ≤ Hm 64 := by
  induction n, hn using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans (H_step n hn) ih

lemma log_ge (p q m : ℕ) (hq : 0 < q) (h : 2 ^ m ≤ p ^ q) :
    (m:ℝ) / q * Real.log 2 ≤ Real.log p := by
  have hq' : (0:ℝ) < q := by exact_mod_cast hq
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; rw [zero_pow hq.ne'] at h; have := Nat.one_le_two_pow (n := m); omega
    · exact h0
  have : (m:ℝ) * Real.log 2 ≤ q * Real.log p := by
    rw [← Real.log_pow, ← Real.log_pow]
    apply Real.log_le_log (by positivity)
    exact_mod_cast h
  rw [div_mul_eq_mul_div, div_le_iff₀ hq']
  linarith

lemma filt64 : (Finset.range 65).filter Nat.Prime =
    {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61} := by decide

lemma Q64 : Qm 64 = 770527199232000/5855632691117327 := by
  unfold Qm
  rw [filt64]
  norm_num [prod_insert]

lemma S64 : (419/100 : ℝ) * Real.log 2 ≤ Sm 64 := by
  unfold Sm
  rw [filt64]
  norm_num [sum_insert]
  have h3 := log_ge 3 2 3 (by norm_num) (by norm_num)
  have h5 := log_ge 5 4 9 (by norm_num) (by norm_num)
  have h7 := log_ge 7 4 11 (by norm_num) (by norm_num)
  have h11 := log_ge 11 3 10 (by norm_num) (by norm_num)
  have h13 := log_ge 13 3 11 (by norm_num) (by norm_num)
  have h17 := log_ge 17 1 4 (by norm_num) (by norm_num)
  have h19 := log_ge 19 1 4 (by norm_num) (by norm_num)
  have h23 := log_ge 23 2 9 (by norm_num) (by norm_num)
  have h29 := log_ge 29 4 19 (by norm_num) (by norm_num)
  have h31 := log_ge 31 4 19 (by norm_num) (by norm_num)
  have h37 := log_ge 37 1 5 (by norm_num) (by norm_num)
  have h41 := log_ge 41 3 16 (by norm_num) (by norm_num)
  have h43 := log_ge 43 3 16 (by norm_num) (by norm_num)
  have h47 := log_ge 47 2 11 (by norm_num) (by norm_num)
  have h53 := log_ge 53 3 17 (by norm_num) (by norm_num)
  have h59 := log_ge 59 4 23 (by norm_num) (by norm_num)
  have h61 := log_ge 61 4 23 (by norm_num) (by norm_num)
  norm_num at h3 h5 h7 h11 h13 h17 h19 h23 h29 h31 h37 h41 h43 h47 h53 h59 h61
  have := Real.log_two_gt_d9
  linarith

lemma H64 : Hm 64 ≤ Real.log 3 := by
  have hL : Lm 64 = -Real.log (Qm 64) := by
    rw [Qm_eq_exp, Real.log_exp]; ring
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hℓ : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; norm_num
  have hℓpos : 0 < Real.log 64 := by rw [hℓ]; linarith
  have hS := S64
  have hX : (Real.log 64 + cM - Sm 64) / Real.log 64 ≤ 0.44 - 1/64 := by
    rw [div_le_iff₀ hℓpos]; unfold cM; rw [hℓ]; linarith
  have hE : Real.exp 0.44 ≤ 3 * Real.log 64 * (770527199232000/5855632691117327) := by
    have e : Real.exp (0.44:ℝ) = Real.exp 0.055 ^ 8 := by rw [← Real.exp_nat_mul]; norm_num
    have h1 : Real.exp 0.055 ≤ 1 / (1 - 0.055) :=
      Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
    have h2 : Real.exp 0.055 ^ 8 ≤ (1 / (1 - 0.055)) ^ 8 :=
      pow_le_pow_left₀ (Real.exp_pos _).le h1 8
    rw [e, hℓ]
    norm_num at h2 ⊢
    linarith
  have hlog : (0.44:ℝ) ≤ Real.log 3 + Real.log (Real.log 64)
      + Real.log (770527199232000/5855632691117327) := by
    have := Real.log_le_log (Real.exp_pos _) hE
    rw [Real.log_exp, Real.log_mul (by positivity) (by norm_num),
      Real.log_mul (by norm_num) hℓpos.ne'] at this
    exact this
  unfold Hm
  rw [hL, Q64]
  simp only [Nat.cast_ofNat]
  linarith

lemma big (n : ℕ) (hn : 64 ≤ n) : 1 / (3 * Real.log n) ≤ Qm n := by
  have hH := le_trans (H_le n hn) H64
  have hS := mertens1 n hn
  have hnr : (64:ℝ) ≤ n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log n := Real.log_pos (by linarith)
  have hnn : 0 ≤ (Real.log n + cM - Sm n) / Real.log n := div_nonneg (by linarith) hlogpos.le
  have h1n : 0 ≤ 1 / (n:ℝ) := by positivity
  have hL : Lm n ≤ Real.log 3 + Real.log (Real.log n) := by unfold Hm at hH; linarith
  rw [Qm_eq_exp]
  have e : 1 / (3 * Real.log n) = Real.exp (-(Real.log 3 + Real.log (Real.log n))) := by
    rw [Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hlogpos]
    rw [one_div]
  rw [e]
  exact Real.exp_le_exp.mpr (by linarith)

lemma small (a b : ℕ) (qb r : ℝ) (hQ : Qm b = qb) (hr : r ≤ Real.log a) (hrpos : 0 < r)
    (h : 1 ≤ 3 * r * qb) (n : ℕ) (han : a ≤ n) (hnb : n ≤ b) :
    1 / (3 * Real.log n) ≤ Qm n := by
  have ha : (a:ℝ) ≤ n := by exact_mod_cast han
  have hapos : 0 < (a:ℝ) := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0; simp at hr; linarith
    · exact_mod_cast h0
  have hlog : Real.log a ≤ Real.log n := Real.log_le_log hapos ha
  calc 1 / (3 * Real.log n) ≤ 1 / (3 * r) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
    _ ≤ qb := by rw [div_le_iff₀ (by positivity)]; linarith
    _ = Qm b := hQ.symm
    _ ≤ Qm n := Qm_anti n b hnb

lemma Q4 : Qm 4 = 1/3 := by
  unfold Qm
  rw [show (Finset.range (4+1)).filter Nat.Prime = {2,3} by decide]
  norm_num [prod_insert]

lemma Q10 : Qm 10 = 8/35 := by
  unfold Qm
  rw [show (Finset.range (10+1)).filter Nat.Prime = {2,3,5,7} by decide]
  norm_num [prod_insert]

lemma Q42 : Qm 42 = 19110297600/131710070791 := by
  unfold Qm
  rw [show (Finset.range (42+1)).filter Nat.Prime = {2,3,5,7,11,13,17,19,23,29,31,37,41} by decide]
  norm_num [prod_insert]

lemma main (n : ℕ) (hn : 3 ≤ n) : 1 / (3 * Real.log n) ≤ Qm n := by
  have hl2 := Real.log_two_gt_d9
  rcases le_or_gt n 4 with h4 | h4
  · have := log_ge 3 2 3 (by norm_num) (by norm_num)
    norm_num at this
    exact small 3 4 (1/3) 1.03 Q4 (by push_cast; linarith) (by norm_num) (by norm_num) n hn h4
  rcases le_or_gt n 10 with h10 | h10
  · have := log_ge 5 4 9 (by norm_num) (by norm_num)
    norm_num at this
    exact small 5 10 (8/35) 1.5 Q10 (by push_cast; linarith) (by norm_num) (by norm_num) n
      (by omega) h10
  rcases le_or_gt n 42 with h42 | h42
  · have := log_ge 11 3 10 (by norm_num) (by norm_num)
    norm_num at this
    exact small 11 42 _ 2.3 Q42 (by push_cast; linarith) (by norm_num) (by norm_num) n
      (by omega) h42
  rcases le_or_gt n 64 with h64 | h64
  · have := log_ge 43 3 16 (by norm_num) (by norm_num)
    norm_num at this
    exact small 43 64 _ 3 Q64 (by push_cast; linarith) (by norm_num) (by norm_num) n
      (by omega) h64
  exact big n h64.le

end OMA_M3


theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_iwaniec_R1.H2 := by
  unfold OMA.R_Erdos687_erdos_687_variants_iwaniec_R1.H2
  refine ⟨1 / 3, by norm_num, ?_⟩
  intro x hx
  have key : 1 / (3 * Real.log x) ≤ OMA_M3.Qm x := by
    rcases Nat.lt_or_ge x 3 with h | h
    · have hx2 : x = 2 := by omega
      subst hx2
      have hl2 := Real.log_two_gt_d9
      have hQ : OMA_M3.Qm 2 = 1 / 2 := by
        unfold OMA_M3.Qm
        rw [show (Finset.range (2 + 1)).filter Nat.Prime = {2} by decide]
        norm_num
      rw [hQ]
      push_cast
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    · exact OMA_M3.main x h
  have heq : OMA_M3.Qm x =
      ∏ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 - (p : ℝ)⁻¹) := by
    unfold OMA_M3.Qm
    simp only [one_div]
  rw [← heq]
  calc 1 / 3 / Real.log (x : ℝ) = 1 / (3 * Real.log x) := by rw [div_div]
    _ ≤ OMA_M3.Qm x := key
