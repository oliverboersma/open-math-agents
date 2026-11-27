import OMAReductions.R_OeisA237578_conjecture_2_R1

-- Step OeisA237578.conjecture_2.R1.H1: hypothesis H1 of reduction OeisA237578.conjecture_2.R1
-- Credit: @hayalows
--
-- The finite direction of the conjecture: at each of the three listed indices the count of
-- k with pi (k * n) prime is one. Each value is a direct kernel computation of the prime
-- counting function, so the whole step is discharged by `decide +kernel` after splitting
-- the disjunctive hypothesis.

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem OMA.solution : OMA.R_OeisA237578_conjecture_2_R1.H1 := by
  intro n hn
  rcases hn with rfl | rfl | rfl <;> decide +kernel
