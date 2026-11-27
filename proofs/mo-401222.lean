import OMAStatements.S_mo_401222
import Mathlib

-- Problem: mo-401222, can binomial(2n, n) be divisible by 2n + 1 for a positive integer n?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Yes: the smallest example is n = 97, where 2n + 1 = 195 = 3 * 5 * 13 divides
-- binomial(194, 97). The binomial coefficient is evaluated through factorials.

theorem OMA.solution : type_of% @OMA.S_mo_401222.main := by
  refine ⟨97, by norm_num, ?_⟩
  rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
  decide +kernel
