import OMAStatements.S_arxiv_2205_09212

-- Problem: arxiv-2205.09212, the Primal Conjecture in the modulo-nine matrix.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- Counterexample: addition with columns a = 5, b = 6, c = 2 and output z = 2.
-- 5 + 6 = 11 is congruent to 2 modulo 9 and the signs are compatible (1 + 1 = 2), but any
-- positive x, y with x + y = 2 are x = y = 1, and 1 is not congruent to 5 modulo 9.

open OMA.S_arxiv_2205_09212 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2205_09212.main) := by
  intro h
  have hc : compatible .add 5 6 2 := by
    show (5 + 6 : ℤ) ≡ 2 [ZMOD 9]
    decide
  have hs : signsCompatible .add 5 6 2 := by
    refine ⟨1, 1, 2, by decide, by decide, by decide, ?_⟩
    show (1 : ℤ) + 1 = 2
    norm_num
  have hz : inColumn 2 2 := ⟨rfl, Int.ModEq.refl _⟩
  have hl5 : label 5 := by unfold label; norm_num
  have hl6 : label 6 := by unfold label; norm_num
  have hl2 : label 2 := by unfold label; norm_num
  obtain ⟨x, y, hx, hy, hxy⟩ := h .add 5 6 2 2 hl5 hl6 hl2 hc hs hz
  have hxy' : x + y = 2 := hxy
  have hx1 : 0 < x := by
    have h1 := hx.1
    rw [show (5 : ℤ).sign = 1 by decide] at h1
    exact Int.sign_eq_one_iff_pos.mp h1
  have hy1 : 0 < y := by
    have h1 := hy.1
    rw [show (6 : ℤ).sign = 1 by decide] at h1
    exact Int.sign_eq_one_iff_pos.mp h1
  have hxm := hx.2
  unfold Int.ModEq at hxm
  omega
