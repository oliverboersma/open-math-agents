import OMAReductions.R_Erdos542_erdos_542_variants_only_two_R1

-- Step Erdos542.erdos_542.variants.only_two.R1.H1
-- Credit: @caa1982

namespace Erdos542H1

private lemma inv_le_log_sub_log {m : ℕ} (hm : 2 ≤ m) :
    (1 : ℝ) / (m : ℝ) ≤ Real.log (m : ℝ) - Real.log ((m : ℝ) - 1) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hdiv_pos : (0 : ℝ) < (m : ℝ) / ((m : ℝ) - 1) := div_pos hm_pos hm1_pos
  have hlog := Real.one_sub_inv_le_log_of_pos hdiv_pos
  rw [inv_div, Real.log_div hm_pos.ne' hm1_pos.ne'] at hlog
  have heq : 1 - ((m : ℝ) - 1) / (m : ℝ) = 1 / (m : ℝ) := by
    field_simp [hm_pos.ne']
    ring
  linarith

private lemma block_le_log {k : ℕ} (hk : 1 ≤ k) :
    (1 : ℝ) / (3 * k + 1 : ℕ) + (1 : ℝ) / (3 * k + 2 : ℕ) ≤
      (2 / 3 : ℝ) * (Real.log ((3 * (k + 1) - 1 : ℕ) : ℝ) - Real.log ((3 * k - 1 : ℕ) : ℝ)) := by
  have h1 : (1 : ℝ) / (3 * k + 1 : ℕ) + (1 : ℝ) / (3 * k + 2 : ℕ) ≤
      (2 / 3 : ℝ) * ((1 : ℝ) / (3 * k : ℕ) + (1 : ℝ) / (3 * k + 1 : ℕ) + (1 : ℝ) / (3 * k + 2 : ℕ)) := by
    have hk_pos : (0 : ℝ) < (3 * k : ℕ) := by positivity
    have h1_pos : (0 : ℝ) < (3 * k + 1 : ℕ) := by positivity
    have h2_pos : (0 : ℝ) < (3 * k + 2 : ℕ) := by positivity
    have hle1 : (1 : ℝ) / (3 * k + 1 : ℕ) ≤ (1 : ℝ) / (3 * k : ℕ) :=
      one_div_le_one_div_of_le hk_pos (by exact_mod_cast Nat.le_succ (3 * k))
    have hle2 : (1 : ℝ) / (3 * k + 2 : ℕ) ≤ (1 : ℝ) / (3 * k : ℕ) :=
      one_div_le_one_div_of_le hk_pos (by exact_mod_cast (by omega : 3 * k ≤ 3 * k + 2))
    linarith
  have hl0 := inv_le_log_sub_log (m := 3 * k) (by omega)
  have hl1 := inv_le_log_sub_log (m := 3 * k + 1) (by omega)
  have hl2 := inv_le_log_sub_log (m := 3 * k + 2) (by omega)
  have hc0 : ((3 * k : ℕ) : ℝ) - 1 = ((3 * k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hc1 : ((3 * k + 1 : ℕ) : ℝ) - 1 = ((3 * k : ℕ) : ℝ) := by push_cast; ring
  have hc2 : ((3 * k + 2 : ℕ) : ℝ) - 1 = ((3 * k + 1 : ℕ) : ℝ) := by push_cast; ring
  have hc3 : ((3 * (k + 1) - 1 : ℕ) : ℝ) = ((3 * k + 2 : ℕ) : ℝ) := by
    rw [show 3 * (k + 1) - 1 = 3 * k + 2 by omega]
  rw [hc0] at hl0
  rw [hc1] at hl1
  rw [hc2] at hl2
  rw [hc3]
  linarith

private lemma sum_blocks_le_log {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    ∑ k ∈ Finset.Ico A B, ((1 : ℝ) / (3 * k + 1 : ℕ) + (1 : ℝ) / (3 * k + 2 : ℕ)) ≤
      (2 / 3 : ℝ) * (Real.log ((3 * B - 1 : ℕ) : ℝ) - Real.log ((3 * A - 1 : ℕ) : ℝ)) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [Finset.sum_Ico_succ_top hAB]
    have hblk := block_le_log (k := B) (by omega)
    linarith

private lemma sum_non_mult3_le {L R : ℕ} (hL : 3 ≤ L) (hLR : L ≤ R) :
    ∑ m ∈ (Finset.Icc 1 R).filter (fun m => L < m ∧ m % 3 ≠ 0), (1 : ℝ) / m ≤
      (2 / 3 : ℝ) * (Real.log ((3 * (R / 3 + 1) - 1 : ℕ) : ℝ) - Real.log ((3 * (L / 3) - 1 : ℕ) : ℝ)) := by
  let S := (Finset.Icc 1 R).filter (fun m => L < m ∧ m % 3 ≠ 0)
  let K := Finset.Ico (L / 3) (R / 3 + 1)
  let T := K.biUnion (fun k => ({3 * k + 1, 3 * k + 2} : Finset ℕ))
  have hST : S ⊆ T := by
    intro m hm
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hm
    obtain ⟨⟨_, hmR⟩, hLm, hm3⟩ := hm
    rw [Finset.mem_biUnion]
    refine ⟨m / 3, Finset.mem_Ico.mpr ⟨Nat.div_le_div_right (le_of_lt hLm), by omega⟩, ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hdisj : (K : Set ℕ).PairwiseDisjoint (fun k => ({3 * k + 1, 3 * k + 2} : Finset ℕ)) := by
    intro k₁ _ k₂ _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    omega
  have hsumT : ∑ m ∈ T, (1 : ℝ) / m =
      ∑ k ∈ K, ((1 : ℝ) / (3 * k + 1 : ℕ) + (1 : ℝ) / (3 * k + 2 : ℕ)) := by
    rw [Finset.sum_biUnion (fun a ha b hb hne => hdisj ha hb hne)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_pair (by omega)]
  calc ∑ m ∈ S, (1 : ℝ) / m
      ≤ ∑ m ∈ T, (1 : ℝ) / m := Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => by positivity)
    _ = ∑ k ∈ K, ((1 : ℝ) / (3 * k + 1 : ℕ) + (1 : ℝ) / (3 * k + 2 : ℕ)) := hsumT
    _ ≤ (2 / 3 : ℝ) * (Real.log ((3 * (R / 3 + 1) - 1 : ℕ) : ℝ) - Real.log ((3 * (L / 3) - 1 : ℕ) : ℝ)) :=
        sum_blocks_le_log (by omega) (by omega)

private lemma small_cases :
    ∀ n ∈ Finset.Ico 12 210,
      (∑ m ∈ (Finset.Icc 1 n).filter (fun m : ℕ => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℚ) / (m : ℚ)) +
        (∑ b ∈ (Finset.Icc 1 n).filter (fun b : ℕ => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
          (1 : ℚ) / (2 * (b : ℚ))) ≤ (2 : ℚ) / 3 := by
  decide +kernel

end Erdos542H1

theorem OMA.solution : OMA.R_Erdos542_erdos_542_variants_only_two_R1.H1 := by
  intro n hn
  by_cases hlt : n < 210
  · have hq := Erdos542H1.small_cases n (Finset.mem_Ico.mpr ⟨hn, hlt⟩)
    have hr : ((∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℚ) / m +
        ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
          (1 : ℚ) / (2 * b) : ℚ) : ℝ) ≤ ((2 / 3 : ℚ) : ℝ) := by
      exact_mod_cast hq
    push_cast at hr
    exact hr
  · have hn210 : 210 ≤ n := by omega
    have hS1_eq : (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0) =
        (Finset.Icc 1 n).filter (fun m => n / 2 < m ∧ m % 3 ≠ 0) := by
      ext m; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    have hS2_eq : (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0) =
        (Finset.Icc 1 (n / 2)).filter (fun b => n / 3 < b ∧ b % 3 ≠ 0) := by
      ext b; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    have h1 : ∑ m ∈ (Finset.Icc 1 n).filter (fun m => n < 2 * m ∧ m % 3 ≠ 0), (1 : ℝ) / m ≤
        (2 / 3 : ℝ) * (Real.log ((3 * (n / 3 + 1) - 1 : ℕ) : ℝ) -
          Real.log ((3 * (n / 2 / 3) - 1 : ℕ) : ℝ)) := by
      rw [hS1_eq]
      exact Erdos542H1.sum_non_mult3_le (by omega) (by omega)
    have h2 : ∑ b ∈ (Finset.Icc 1 n).filter (fun b => n < 3 * b ∧ 2 * b ≤ n ∧ b % 3 ≠ 0),
        (1 : ℝ) / (2 * b) ≤
        (1 / 3 : ℝ) * (Real.log ((3 * (n / 2 / 3 + 1) - 1 : ℕ) : ℝ) -
          Real.log ((3 * (n / 3 / 3) - 1 : ℕ) : ℝ)) := by
      rw [hS2_eq]
      have hhalf : ∑ b ∈ (Finset.Icc 1 (n / 2)).filter (fun b => n / 3 < b ∧ b % 3 ≠ 0),
          (1 : ℝ) / (2 * b) =
          (1 / 2 : ℝ) * ∑ b ∈ (Finset.Icc 1 (n / 2)).filter (fun b => n / 3 < b ∧ b % 3 ≠ 0),
            (1 : ℝ) / b := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => by ring
      rw [hhalf]
      have hbound := Erdos542H1.sum_non_mult3_le (L := n / 3) (R := n / 2) (by omega) (by omega)
      linarith
    let A1 : ℝ := ((3 * (n / 3 + 1) - 1 : ℕ) : ℝ)
    let B1 : ℝ := ((3 * (n / 2 / 3) - 1 : ℕ) : ℝ)
    let A2 : ℝ := ((3 * (n / 2 / 3 + 1) - 1 : ℕ) : ℝ)
    let B2 : ℝ := ((3 * (n / 3 / 3) - 1 : ℕ) : ℝ)
    have hA1_pos : 0 < A1 := by
      dsimp only [A1]
      have : 0 < 3 * (n / 3 + 1) - 1 := by omega
      exact_mod_cast this
    have hB1_pos : 0 < B1 := by
      dsimp only [B1]
      have : 0 < 3 * (n / 2 / 3) - 1 := by omega
      exact_mod_cast this
    have hA2_pos : 0 < A2 := by
      dsimp only [A2]
      have : 0 < 3 * (n / 2 / 3 + 1) - 1 := by omega
      exact_mod_cast this
    have hB2_pos : 0 < B2 := by
      dsimp only [B2]
      have : 0 < 3 * (n / 3 / 3) - 1 := by omega
      exact_mod_cast this
    have hA1_le : A1 ≤ (n : ℝ) + 2 := by
      dsimp only [A1]
      have : 3 * (n / 3 + 1) - 1 ≤ n + 2 := by omega
      exact_mod_cast this
    have hB1_ge : (n : ℝ) - 8 ≤ 2 * B1 := by
      dsimp only [B1]
      have : n - 8 ≤ 2 * (3 * (n / 2 / 3) - 1) := by omega
      have h1 : ((n - 8 : ℕ) : ℝ) ≤ ((2 * (3 * (n / 2 / 3) - 1) : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h1
      push_cast at h1 ⊢
      linarith
    have hA2_le : 2 * A2 ≤ (n : ℝ) + 4 := by
      dsimp only [A2]
      have : 2 * (3 * (n / 2 / 3 + 1) - 1) ≤ n + 4 := by omega
      exact_mod_cast this
    have hB2_ge : (n : ℝ) - 12 ≤ 3 * B2 := by
      have : n - 12 ≤ 3 * (3 * (n / 3 / 3) - 1) := by omega
      have h1 : ((n - 12 : ℕ) : ℝ) ≤ ((3 * (3 * (n / 3 / 3) - 1) : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by omega)] at h1
      push_cast at h1 ⊢
      linarith
    have hratio : (A1 / B1) ^ 2 * (A2 / B2) ≤ Real.exp 2 := by
      have he1 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have he2 : (7.38 : ℝ) ≤ Real.exp 2 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith
      refine le_trans ?_ he2
      have hnr : (210 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn210
      have h1' : A1 / B1 ≤ ((n : ℝ) + 2) / (((n : ℝ) - 8) / 2) := by
        apply div_le_div₀ (by positivity) hA1_le (by linarith) (by linarith)
      have h2' : A2 / B2 ≤ (((n : ℝ) + 4) / 2) / (((n : ℝ) - 12) / 3) := by
        apply div_le_div₀ (by positivity) (by linarith) (by linarith) (by linarith)
      have h1_num : ((n : ℝ) + 2) / (((n : ℝ) - 8) / 2) ≤ 212 / 101 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith
      have h2_num : (((n : ℝ) + 4) / 2) / (((n : ℝ) - 12) / 3) ≤ 107 / 66 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        nlinarith
      have h1b : A1 / B1 ≤ 212 / 101 := le_trans h1' h1_num
      have h2b : A2 / B2 ≤ 107 / 66 := le_trans h2' h2_num
      have hsq : (A1 / B1) ^ 2 ≤ (212 / 101 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1b 2
      have hprod : (A1 / B1) ^ 2 * (A2 / B2) ≤ (212 / 101 : ℝ) ^ 2 * (107 / 66 : ℝ) :=
        mul_le_mul hsq h2b (by positivity) (by positivity)
      linarith [hprod, show (212 / 101 : ℝ) ^ 2 * (107 / 66 : ℝ) ≤ 7.38 by norm_num]
    have hlog_comb : 2 * (Real.log A1 - Real.log B1) + (Real.log A2 - Real.log B2) ≤ 2 := by
      have hpos_p : 0 < (A1 / B1) ^ 2 * (A2 / B2) := by positivity
      have hl := Real.log_le_log hpos_p hratio
      rw [Real.log_exp, Real.log_mul (by positivity) (by positivity), Real.log_pow,
          Real.log_div hA1_pos.ne' hB1_pos.ne', Real.log_div hA2_pos.ne' hB2_pos.ne'] at hl
      push_cast at hl
      exact hl
    linarith
