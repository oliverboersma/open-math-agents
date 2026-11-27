import OMAReductions.R_OeisA24356_conjecture_R1

-- Step OeisA24356.conjecture.R1.H1: hypothesis H1 of reduction OeisA24356.conjecture.R1
-- Credit: @anmolspace
-- Proof: H1 is the value a(4) = 0, already established upstream as OeisA24356.a_4
-- (an explicit kernel vector (6, -3, -2, 1) of the 4x4 Hankel matrix of primes).

theorem OMA.solution : OMA.R_OeisA24356_conjecture_R1.H1 := by
  exact OeisA24356.a_4
