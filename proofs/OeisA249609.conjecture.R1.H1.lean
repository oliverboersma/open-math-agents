import OMAReductions.R_OeisA249609_conjecture_R1

-- Step OeisA249609.conjecture.R1.H1: hypothesis H1 of reduction OeisA249609.conjecture.R1
-- Credit: @anmolspace
-- Proof: the five values a 0, a 1, a 2, a 7, a 8 are computed by decide.

theorem OMA.solution : OMA.R_OeisA249609_conjecture_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl <;> decide
