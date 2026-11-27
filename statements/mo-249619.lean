import Mathlib

/-!
# MathOverflow 249619

Source: https://mathoverflow.net/questions/249619
-/

namespace OMA.S_mo_249619

open Set Filter Topology

noncomputable def bump (x : ℝ) : ℝ :=
  if x ∈ Icc (-1 : ℝ) 1 then Real.cos (Real.pi * x / 2) else 0

theorem main : ∀ r : ℕ ≃ Icc (0 : ℚ) 1,
    ∃ k : ℕ → ℤ, StrictMono k ∧ ∃ y ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => bump (k n * (y - ((r n).val : ℝ)))) atTop (𝓝 0) := by
  sorry

end OMA.S_mo_249619
