import OMAReductions.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1
import Mathlib

-- Step Erdos420.erdos_420.variants.log_frequently_lt_two.R1.H2: hypothesis H2 of reduction
-- Erdos420.erdos_420.variants.log_frequently_lt_two.R1
-- Credit: @ivillar

/-!
If `f n ≤ g n` then `⌊f n⌋₊ ≤ ⌊g n⌋₊`, so `(n + ⌊f n⌋₊)!` divides `(n + ⌊g n⌋₊)!` and its
number of divisors is at most that of the latter; divide by `d(n!) > 0`.
-/

theorem OMA.solution : OMA.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1.H2 := by
  unfold OMA.R_Erdos420_erdos_420_variants_log_frequently_lt_two_R1.H2
  intro f g n hfg
  unfold Erdos420.F
  have hfl : ⌊f n⌋₊ ≤ ⌊g n⌋₊ := Nat.floor_le_floor hfg
  have hdvd : (n + ⌊f n⌋₊).factorial ∣ (n + ⌊g n⌋₊).factorial :=
    Nat.factorial_dvd_factorial (by omega)
  have hle : ArithmeticFunction.sigma 0 (n + ⌊f n⌋₊).factorial ≤
      ArithmeticFunction.sigma 0 (n + ⌊g n⌋₊).factorial := by
    rw [ArithmeticFunction.sigma_zero_apply, ArithmeticFunction.sigma_zero_apply]
    exact Finset.card_le_card (Nat.divisors_subset_of_dvd (Nat.factorial_ne_zero _) hdvd)
  have hpos : (0 : ℝ) < ArithmeticFunction.sigma 0 n.factorial := by
    exact_mod_cast ArithmeticFunction.sigma_pos 0 _ (Nat.factorial_ne_zero n)
  apply div_le_div_of_nonneg_right _ hpos.le
  exact_mod_cast hle
