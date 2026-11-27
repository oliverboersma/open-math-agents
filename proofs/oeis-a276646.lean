import OMAStatements.S_oeis_a276646
import Mathlib.Tactic

-- Problem: A276646, the mean of the decimal fractions 0.1, 0.2, ...
-- Credit: @yuka30240

open Finset OMA.S_oeis_a276646

private lemma sum_offsets (a : ℚ) (m : ℕ) :
    (∑ j ∈ range m, (a + j)) = m * (2 * a + m - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

-- A block starting at b = 10^d contains at most 9b terms.
private lemma block_bound (d m : ℕ) (hm : m ≤ 9 * 10 ^ d) :
    (∑ j ∈ range m, decimalFraction (10 ^ d + j)) ≤ (11 / 20 : ℚ) * m := by
  let b : ℕ := 10 ^ d
  have hb : 0 < (b : ℚ) := by dsimp [b]; positivity
  have hsize : (m : ℚ) ≤ 9 * b := by exact_mod_cast hm
  have hterm (j : ℕ) (hj : j ∈ range m) :
      decimalFraction (b + j) = ((b : ℚ) + j) / (b * 10) := by
    have hj' := mem_range.mp hj
    have hlog : Nat.log 10 (b + j) = d := by
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · exact Nat.le_add_right _ _
      · rw [pow_succ]
        change b + j < b * 10
        change m ≤ 9 * b at hm
        omega
    simp [decimalFraction, hlog, pow_succ, b]
  change (∑ j ∈ range m, decimalFraction (b + j)) ≤ _
  rw [sum_congr rfl hterm, ← sum_div, sum_offsets]
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < b * 10)).2
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) m) (sub_nonneg.mpr hsize)]

private lemma prefix_bound (n : ℕ) :
    (∑ i ∈ range n, decimalFraction (i + 1)) ≤ (11 / 20 : ℚ) * n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain rfl | hn := Nat.eq_zero_or_pos n
    · simp
    let d := Nat.log 10 n
    let b : ℕ := 10 ^ d
    have hb : 0 < b := by dsimp [b]; positivity
    have hlow : b ≤ n := Nat.pow_log_le_self 10 hn.ne'
    have hhigh := Nat.lt_pow_succ_log_self (b := 10) (by decide) n
    rw [pow_succ] at hhigh
    change n < b * 10 at hhigh
    let m := n + 1 - b
    have hsplit : b - 1 + m = n := by dsimp [m]; omega
    have hblock := block_bound d m (by change m ≤ 9 * b; dsimp [m]; omega)
    have hprev := ih (b - 1) (by omega)
    calc
      _ = (∑ i ∈ range (b - 1), decimalFraction (i + 1)) +
          ∑ j ∈ range m, decimalFraction (b + j) := by
            conv_lhs => rw [← hsplit, sum_range_add]
            congr 1
            apply sum_congr rfl
            intro j _
            congr 1
            omega
      _ ≤ (11 / 20 : ℚ) * (b - 1 : ℕ) + (11 / 20 : ℚ) * m := add_le_add hprev hblock
      _ = _ := by rw [← mul_add, ← Nat.cast_add, hsplit]

theorem OMA.solution : type_of% @OMA.S_oeis_a276646.main := by
  intro n hn
  exact (div_le_iff₀ (by exact_mod_cast hn : 0 < (n : ℚ))).2 (prefix_bound n)
