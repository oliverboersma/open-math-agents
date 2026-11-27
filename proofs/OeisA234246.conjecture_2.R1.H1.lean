import OMAReductions.R_OeisA234246_conjecture_2_R1

-- Step OeisA234246.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA234246.conjecture_2.R1
-- Credit: @hayalows
--
-- The finite direction of conjecture (i): at each of the nine listed indices the count of
-- k with k * phi (n - k) + 1 a square is one. Each value is a direct kernel computation of
-- the defining sum over totients and squares, so the whole step is discharged by
-- `decide +kernel` after splitting the membership hypothesis.

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem OMA.solution : OMA.R_OeisA234246_conjecture_2_R1.H1 := by
  intro n hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
