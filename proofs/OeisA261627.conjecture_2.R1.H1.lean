import OMAReductions.R_OeisA261627_conjecture_2_R1

-- Step OeisA261627.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA261627.conjecture_2.R1
-- Credit: @luciusacarr

theorem OMA.solution : OMA.R_OeisA261627_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel
