import OMAReductions.R_OeisA259667_conjecture_1_R1
import Mathlib

-- Step OeisA259667.conjecture_1.R1.H1: hypothesis H1 of reduction OeisA259667.conjecture_1.R1
-- Credit: @ivillar (original proof).
-- Strategy. Write catalan n = (2n)! / (n! n!) / (n+1) and evaluate at n = 0, 1, 31 with norm_num.

theorem OMA.solution : OMA.R_OeisA259667_conjecture_1_R1.H1 := by
  have key : ∀ n : ℕ, n ≤ 31 → OeisA259667.a n =
      (2 * n).factorial / (n.factorial * (2 * n - n).factorial) / (n + 1) % 6 := by
    intro n _
    rw [OeisA259667.a, catalan_eq_centralBinom_div, Nat.centralBinom,
      Nat.choose_eq_factorial_div_factorial (by omega)]
  intro k hk
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · rw [key _ (by norm_num)]
    norm_num [Nat.factorial]
  · rw [key _ (by norm_num)]
    norm_num [Nat.factorial]
  · rw [key _ (by norm_num)]
    norm_num [Nat.factorial]
