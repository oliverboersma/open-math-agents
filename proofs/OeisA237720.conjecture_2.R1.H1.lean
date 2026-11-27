import OMAReductions.R_OeisA237720_conjecture_2_R1
import Mathlib

-- Step OeisA237720.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA237720.conjecture_2.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! Each listed value is checked by kernel evaluation of the defining finite sum. -/

theorem OMA.solution : OMA.R_OeisA237720_conjecture_2_R1.H1 := by
  rintro n (rfl | rfl | rfl | ⟨h1, h2⟩)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · interval_cases n <;> decide +kernel
