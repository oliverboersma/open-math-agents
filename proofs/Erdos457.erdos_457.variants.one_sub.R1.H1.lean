import OMAReductions.R_Erdos457_erdos_457_variants_one_sub_R1
import Mathlib

-- Step Erdos457.erdos_457.variants.one_sub.R1.H1: hypothesis H1 of reduction Erdos457.erdos_457.variants.one_sub.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Induction on k, using (n + k + 1) * C(n + k, k) = C(n + k + 1, k + 1) * (k + 1). -/

open Finset

theorem OMA.solution : OMA.R_Erdos457_erdos_457_variants_one_sub_R1.H1 := by
  intro n k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
    have h := Nat.add_one_mul_choose_eq (n + k) k
    rw [show n + (k + 1) = n + k + 1 by ring]
    nlinarith [h]

