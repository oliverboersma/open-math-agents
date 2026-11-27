import OMAReductions.R_Erdos52_erdos_52_R1
import Mathlib

-- Step Erdos52.erdos_52.R1.H1: hypothesis H1 of reduction Erdos52.erdos_52.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Cauchy–Schwarz in the form |S|^2 |S|^2 ≤ |S + S| E+(S) and |S|^2 |S|^2 ≤ |S S| E×(S)
(Mathlib's le_card_add_mul_addEnergy and le_card_mul_mul_mulEnergy), then compare with the max and min. -/

open Finset
open scoped Pointwise

theorem OMA.solution : OMA.R_Erdos52_erdos_52_R1.H1 := by
  intro S
  have h1 := Finset.le_card_add_mul_addEnergy S S
  have h2 := Finset.le_card_mul_mul_mulEnergy S S
  have e : S.card ^ 4 = S.card ^ 2 * S.card ^ 2 := by ring
  rcases le_total (addEnergy S S) (mulEnergy S S) with h | h
  · rw [min_eq_left h, e]
    exact h1.trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  · rw [min_eq_right h, e]
    exact h2.trans (Nat.mul_le_mul_right _ (le_max_right _ _))
