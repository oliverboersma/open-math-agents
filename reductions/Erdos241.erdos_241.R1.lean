import FormalConjectures.ErdosProblems.«241»
import Mathlib

/-! The conjecture f(N) ~ N^(1/3) for the largest subset of {1, ..., N} with distinct sums of
three elements has two halves. The asymptotic lower bound (1 + o(1)) N^(1/3) <= f(N) is the
theorem of Bose and Chowla (Theorems in the additive theory of numbers, Comment. Math. Helv.
1962); it is the catalogue's solved variant Erdos241.erdos_241.variants.lower_bound. The
matching asymptotic upper bound is the open part: the best known constants are those of Green
and of White (Erdos241.erdos_241.variants.upper_bound and upper_bound_white). -/

namespace OMA.R_Erdos241_erdos_241_R1

open Filter Asymptotics

/-- Bose and Chowla: f(N) is at least (1 + o(1)) N^(1/3). -/
def H1 : Prop :=
  ∃ ε : ℕ → ℝ, ε =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ᶠ N in atTop, (1 + ε N) * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (Erdos241.f N 3 : ℝ)

/-- The open upper bound: f(N) is at most (1 + o(1)) N^(1/3). -/
def H2 : Prop :=
  ∃ ε : ℕ → ℝ, ε =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ᶠ N in atTop, (Erdos241.f N 3 : ℝ) ≤ (1 + ε N) * (N : ℝ) ^ ((1 : ℝ) / 3)

theorem main : H1 → H2 → type_of% @Erdos241.erdos_241 := by
  rintro ⟨ε₁, h1o, h1⟩ ⟨ε₂, h2o, h2⟩
  refine Asymptotics.isLittleO_iff.mpr ?_
  intro c hc
  filter_upwards [Asymptotics.isLittleO_iff.mp h1o hc, Asymptotics.isLittleO_iff.mp h2o hc,
    h1, h2] with N e1 e2 hl hu
  have hP : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [norm_one, mul_one, Real.norm_eq_abs] at e1 e2
  have e1' := abs_le.mp e1
  have e2' := abs_le.mp e2
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_of_nonneg hP, abs_le]
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ε₁ N + c) hP]
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ c - ε₂ N) hP]

end OMA.R_Erdos241_erdos_241_R1
