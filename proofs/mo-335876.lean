import OMAStatements.S_mo_335876
import Mathlib

-- Problem: mo-335876, is a one-sided directional derivative at a local minimum always zero?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. The absolute value on the real line has a local (even global) minimum at 0, and its
-- one-sided directional derivative at 0 in the direction 1 equals 1.

open Filter Topology

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_335876.main) := by
  intro h
  have hmin : IsLocalMin (fun x : ℝ => |x|) 0 := by
    apply Filter.Eventually.of_forall
    intro y
    simp
  have hd : OMA.S_mo_335876.hasDirectionalDerivative (fun x : ℝ => |x|) 0 1 1 := by
    unfold OMA.S_mo_335876.hasDirectionalDerivative
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    show (1 : ℝ) = (|0 + t • (1 : ℝ)| - |(0 : ℝ)|) / t
    rw [zero_add, smul_eq_mul, mul_one, abs_zero, sub_zero, abs_of_pos ht', div_self ht'.ne']
  have h1 := h ℝ (fun x : ℝ => |x|) 0 hmin 1 1 hd
  norm_num at h1
