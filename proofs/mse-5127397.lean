import OMAStatements.S_mse_5127397
import Mathlib

open Filter Topology

abbrev OMA_E := WithLp 1 (ℚ_[2] × ℚ_[2])

theorem OMA_hyp : ∀ u : ℕ → OMA_E,
    OMA.S_mse_5127397.SeriesConverges u ↔ Tendsto u atTop (nhds 0) := by
  intro u
  constructor
  · rintro ⟨s, hs⟩
    have h1 := hs.comp (tendsto_add_atTop_nat 1)
    have h2 := h1.sub hs
    simp only [Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left, sub_self] at h2
    exact h2
  · intro hu
    let e := WithLp.prodContinuousLinearEquiv 1 ℚ_[2] ℚ_[2] ℚ_[2]
    have hv : Tendsto (fun n => e (u n)) atTop (nhds 0) := by
      have := e.continuous.tendsto 0
      rw [map_zero] at this
      exact this.comp hu
    have hs : Summable (fun n => e (u n)) :=
      NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by simpa [Nat.cofinite_eq_atTop] using hv)
    have ht := hs.hasSum.tendsto_sum_nat
    have h3 := e.symm.continuous.tendsto _ |>.comp ht
    refine ⟨e.symm (∑' n, e (u n)), ?_⟩
    refine h3.congr (fun N => ?_)
    simp [map_sum]

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_5127397.main) := by
  intro h
  have := (h ℚ_[2] OMA_E OMA_hyp).2
  let x : OMA_E := WithLp.toLp 1 ((1 : ℚ_[2]), (0 : ℚ_[2]))
  let y : OMA_E := WithLp.toLp 1 ((0 : ℚ_[2]), (1 : ℚ_[2]))
  have hx : ‖x‖ = 1 := by
    rw [WithLp.prod_norm_eq_add (by simp)]; simp [x]
  have hy : ‖y‖ = 1 := by
    rw [WithLp.prod_norm_eq_add (by simp)]; simp [y]
  have hxy : ‖x + y‖ = 2 := by
    have : x + y = WithLp.toLp 1 ((1 : ℚ_[2]), (1 : ℚ_[2])) := by
      apply WithLp.ofLp_injective 1
      simp [x, y]
    rw [this, WithLp.prod_norm_eq_add (by simp)]; norm_num
  have := this x y
  rw [hx, hy, hxy] at this
  norm_num at this
