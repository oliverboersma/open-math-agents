import OMAReductions.R_Erdos1210_erdos_1210_variants_er80_correction_R1
import Mathlib

-- Step Erdos1210.erdos_1210.variants.er80_correction.R1.H1: hypothesis H1 of reduction Erdos1210.erdos_1210.variants.er80_correction.R1
-- Credit: @ivillar

/-!
For `q > 2 n` we have `1 / (q - n) ≤ 1 / q + 2 n / q ^ 2`. The second terms sum to at most `1`
(telescoping), and the primes in `(2 n, m]` not counted in `[n, m - n)` are at most `n + 1`
integers each larger than `2 n`, contributing at most `1`.
-/
open Finset

namespace F2E1210

theorem sum_inv_sq (N M : ℕ) (hN : 1 ≤ N) :
    ∑ q ∈ Ioc N M, 1 / ((q : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hNM : N ≤ M
  · have key : ∑ q ∈ Ioc N M, 1 / ((q : ℝ) ^ 2) ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by
      induction M, hNM using Nat.le_induction with
      | base => simp
      | succ M hM ih =>
        have hM0 : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le hN hM
        have hx : 1 / ((M : ℝ) + 1) * ((M : ℝ) + 1) = 1 := one_div_mul_cancel (by positivity)
        have hx2 : 1 / ((M : ℝ) + 1) * (1 / ((M : ℝ) + 1)) * ((M : ℝ) + 1) = 1 / ((M : ℝ) + 1) := by
          rw [mul_assoc, hx, mul_one]
        have hstep : 1 / ((M : ℝ) + 1) ^ 2 ≤ 1 / (M : ℝ) - 1 / ((M : ℝ) + 1) := by
          rw [le_sub_iff_add_le, ← one_div_pow, le_div_iff₀ hM0]
          nlinarith [sq_nonneg (1 / ((M : ℝ) + 1)), hx, hx2]
        rw [Finset.sum_Ioc_succ_top hM]
        push_cast
        linarith
    have hMpos : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity

theorem shift : ∀ n m : ℕ, 2 * n ≤ m →
    (∑ q ∈ (Ioc (2 * n) m).filter Nat.Prime, 1 / ((q : ℝ) - n)) ≤
      (∑ q ∈ (Ico n (m - n)).filter Nat.Prime, 1 / (q : ℝ)) + 2 := by
  intro n m hnm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hterm : ∀ q ∈ (Ioc (2 * n) m).filter Nat.Prime,
      1 / ((q : ℝ) - n) ≤ 1 / (q : ℝ) + 2 * n * (1 / (q : ℝ) ^ 2) := by
    intro q hq
    have hq' : 2 * n < q := (mem_Ioc.mp (mem_filter.mp hq).1).1
    have hqr : 2 * (n : ℝ) < q := by exact_mod_cast hq'
    have hqpos : (0 : ℝ) < q := by linarith
    have hd : (0 : ℝ) < (q : ℝ) - n := by linarith
    rw [div_le_iff₀ hd]
    have e : (1 / (q : ℝ) + 2 * n * (1 / (q : ℝ) ^ 2)) * ((q : ℝ) - n) =
        1 + (n / q) * (1 - 2 * n / q) := by
      field_simp
      ring
    rw [e]
    have h2 : 0 ≤ (n : ℝ) / q * (1 - 2 * n / q) :=
      mul_nonneg (div_nonneg hn0 hqpos.le) (by rw [sub_nonneg, div_le_one hqpos]; linarith)
    linarith
  have h1 : ∑ q ∈ (Ioc (2 * n) m).filter Nat.Prime, 1 / ((q : ℝ) - n) ≤
      ∑ q ∈ (Ioc (2 * n) m).filter Nat.Prime, 1 / (q : ℝ) +
        2 * n * ∑ q ∈ (Ioc (2 * n) m).filter Nat.Prime, 1 / (q : ℝ) ^ 2 := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_le_sum hterm
  have hA : 2 * (n : ℝ) * ∑ q ∈ (Ioc (2 * n) m).filter Nat.Prime, 1 / (q : ℝ) ^ 2 ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hsub : ∑ q ∈ (Ioc (2 * n) m).filter Nat.Prime, 1 / (q : ℝ) ^ 2 ≤
          ∑ q ∈ Ioc (2 * n) m, 1 / (q : ℝ) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      have hs := sum_inv_sq (2 * n) m (by omega)
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      calc 2 * (n : ℝ) * ∑ q ∈ (Ioc (2 * n) m).filter Nat.Prime, 1 / (q : ℝ) ^ 2
          ≤ 2 * n * (1 / ((2 * n : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hsub.trans hs) (by positivity)
        _ = 1 := by
            push_cast
            field_simp
  have hB : ∑ q ∈ (Ioc (2 * n) m).filter Nat.Prime, 1 / (q : ℝ) ≤
      ∑ q ∈ (Ico n (m - n)).filter Nat.Prime, 1 / (q : ℝ) + 1 := by
    rw [← sum_filter_add_sum_filter_not ((Ioc (2 * n) m).filter Nat.Prime) (fun q => q < m - n)]
    apply add_le_add
    · apply sum_le_sum_of_subset_of_nonneg
      · intro q hq
        simp only [mem_filter, mem_Ioc] at hq
        simp only [mem_filter, mem_Ico]
        exact ⟨⟨by omega, hq.2⟩, hq.1.2⟩
      · intro _ _ _
        positivity
    · have hcard : (((Ioc (2 * n) m).filter Nat.Prime).filter (fun q => ¬ q < m - n)).card ≤
          n + 1 := by
        calc (((Ioc (2 * n) m).filter Nat.Prime).filter (fun q => ¬ q < m - n)).card
            ≤ (Icc (m - n) m).card := card_le_card (fun q hq => by
              simp only [mem_filter, mem_Ioc, not_lt] at hq
              exact mem_Icc.mpr ⟨hq.2, hq.1.1.2⟩)
          _ = n + 1 := by
              rw [Nat.card_Icc]
              omega
      have hterm2 : ∀ q ∈ ((Ioc (2 * n) m).filter Nat.Prime).filter (fun q => ¬ q < m - n),
          1 / (q : ℝ) ≤ 1 / ((2 * n + 1 : ℕ) : ℝ) := by
        intro q hq
        have h : 2 * n + 1 ≤ q := by
          simp only [mem_filter, mem_Ioc] at hq
          omega
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast h)
      calc ∑ q ∈ ((Ioc (2 * n) m).filter Nat.Prime).filter (fun q => ¬ q < m - n), 1 / (q : ℝ)
          ≤ (((Ioc (2 * n) m).filter Nat.Prime).filter (fun q => ¬ q < m - n)).card •
              (1 / ((2 * n + 1 : ℕ) : ℝ)) := sum_le_card_nsmul _ _ _ hterm2
        _ ≤ (n + 1) • (1 / ((2 * n + 1 : ℕ) : ℝ)) :=
            nsmul_le_nsmul_left (by positivity) hcard
        _ ≤ 1 := by
            rw [nsmul_eq_mul, mul_one_div, div_le_one (by positivity)]
            push_cast
            linarith
  linarith

end F2E1210

theorem OMA.solution : OMA.R_Erdos1210_erdos_1210_variants_er80_correction_R1.H1 :=
  F2E1210.shift
