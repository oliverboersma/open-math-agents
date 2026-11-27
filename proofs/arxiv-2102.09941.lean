import OMAStatements.S_arxiv_2102_09941

-- Problem: arxiv-2102.09941, the periodicity conjecture for the iterated sum of divisors.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- The statement fails at n = 6 itself: the first clause of `conditions 6` asks that 6 divides
-- the k-th iterate of the divisor sum at 6 for every odd k, but the iterates are
-- 12, 28, 56, and 6 does not divide 56 (k = 3).

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2102_09941.main) := by
  intro h
  have h6 := (h 6 (by norm_num)).mpr rfl
  have h3 := h6.1 3 (by norm_num) (by decide)
  have e : (OMA.S_arxiv_2102_09941.divisorSum^[3]) 6 = 56 := by decide
  rw [e] at h3
  omega
