import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1

/-! The product of the first m coefficient bounds dominates (18/5)^m m! from m = 26700 on:
the base case is a kernel-checked integer comparison (computed in blocks of 150 factors),
each further factor gains at least 18/5, and exp (51/40) < 18/5. -/

open Finset

namespace OMA930

def Lf (i : ℕ) : ℕ :=
  max i (max ((1260*(i-304)+352)/353) ((41580*(i-1492)+9546)/9547))

/-- The product of `k` consecutive values of `g` starting at `i`. -/
def blk (g : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, i => g i * blk g k (i + 1)

/-- The product of `j` consecutive blocks of 150 values of `g` starting at `i`. -/
def out (g : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | j + 1, i => blk g 150 i * out g j (i + 150)

lemma blk_eq (g : ℕ → ℕ) : ∀ k i, blk g k i = ∏ t ∈ range k, g (i + t) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [blk]
  | succ k ih =>
    intro i
    rw [blk, ih, Finset.prod_range_succ', Nat.add_zero, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    congr 1
    omega

lemma out_eq (g : ℕ → ℕ) : ∀ j i, out g j i = ∏ t ∈ range (150 * j), g (i + t) := by
  intro j
  induction j with
  | zero =>
    intro i
    simp [out]
  | succ j ih =>
    intro i
    rw [out, ih, blk_eq, show 150 * (j + 1) = 150 + 150 * j by ring, Finset.prod_range_add]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Nat.add_assoc]

lemma base : Nat.ble (out (fun i => 18 * (i + 1)) 178 0)
    (out (fun i => 5 * Lf (i + 1)) 178 0) = true := by decide +kernel

lemma Q : ∀ m, 26700 ≤ m →
    ∏ t ∈ range m, 18 * (t + 1) ≤ ∏ t ∈ range m, 5 * Lf (t + 1) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    have h := Nat.le_of_ble_eq_true base
    rw [out_eq, out_eq] at h
    have h150 : 150 * 178 = 26700 := by norm_num
    rw [h150] at h
    simp only [zero_add] at h
    exact h
  | succ m hm ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    refine Nat.mul_le_mul ih ?_
    have h1 : (41580*(m+1-1492)+9546)/9547 ≤ Lf (m+1) :=
      le_max_of_le_right (le_max_right _ _)
    omega

lemma exp_bound : Real.exp (51/40) < 18/5 := by
  have h1 : Real.exp (51/40) ^ 40 = Real.exp 1 ^ 51 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    norm_num
  have h2 : Real.exp 1 ^ 51 < (2.7182818286 : ℝ) ^ 51 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  have h3 : (2.7182818286 : ℝ) ^ 51 ≤ (18/5) ^ 40 := by norm_num
  refine lt_of_pow_lt_pow_left₀ 40 (by norm_num) ?_
  rw [h1]
  exact h2.trans_le h3

theorem main : ∀ m : ℕ, 26700 ≤ m →
    (51:ℝ)/40*m ≤ Real.log ((∏ i ∈ range m, Lf (i+1) : ℕ) : ℝ) -
      Real.log (m.factorial : ℝ) := by
  intro m hm
  have hq := Q m hm
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_range, Finset.prod_range_add_one_eq_factorial] at hq
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = ∏ i ∈ range m, Lf (i+1) := ⟨_, rfl⟩
  rw [← hP] at hq ⊢
  have hqR : (18:ℝ)^m * (m.factorial : ℝ) ≤ 5^m * (P : ℝ) := by exact_mod_cast hq
  have hf : (0:ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  have hl : (0:ℝ) < 18^m * (m.factorial : ℝ) := by positivity
  have hPpos : (0:ℝ) < P := by
    by_contra h
    have h0 : (P:ℝ) = 0 := le_antisymm (not_lt.1 h) (Nat.cast_nonneg _)
    rw [h0, mul_zero] at hqR
    linarith
  have hlog := Real.log_le_log hl hqR
  rw [Real.log_mul (by positivity) hf.ne', Real.log_mul (by positivity) hPpos.ne',
    Real.log_pow, Real.log_pow] at hlog
  have h185 : (51:ℝ)/40 ≤ Real.log 18 - Real.log 5 := by
    rw [← Real.log_div (by norm_num) (by norm_num), Real.le_log_iff_exp_le (by norm_num)]
    exact exp_bound.le
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have h4 := mul_le_mul_of_nonneg_left h185 hm0
  linarith

end OMA930

theorem OMA.solution : OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1.H3 :=
  OMA930.main
