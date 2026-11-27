import FormalConjectures.ErdosProblems.«573»
import Mathlib

/-! Erdős and Simonovits ask whether ex(n; {C_3, C_4}) ~ (n/2)^(3/2). The asymptotic lower bound
is known: forbidding C_4 and all odd cycles is more restrictive than forbidding C_3 and C_4, and
that extremal number is ~ (n/2)^(3/2) by Kővári, Sós and Turán and the finite-geometry
constructions (the catalogue's solved variant Erdos573.erdos_573.variants.kst). The matching
asymptotic upper bound is the open part. -/

namespace OMA.R_Erdos573_erdos_573_R1

open Filter Asymptotics

/-- The known asymptotic lower bound. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (1 - ε) * ((n : ℝ) / 2) ^ (3 / 2 : ℝ) ≤ (Erdos573.cycleExtremalNumber {3, 4} n : ℝ)

/-- The open asymptotic upper bound. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (Erdos573.cycleExtremalNumber {3, 4} n : ℝ) ≤ (1 + ε) * ((n : ℝ) / 2) ^ (3 / 2 : ℝ)

theorem main : H1 → H2 → type_of% @Erdos573.erdos_573 := by
  intro h1 h2
  refine Asymptotics.isLittleO_iff.mpr ?_
  intro c hc
  filter_upwards [h1 c hc, h2 c hc] with n hl hu
  have hs : (0 : ℝ) ≤ ((n : ℝ) / 2) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_of_nonneg hs, abs_le]
  constructor <;> nlinarith

end OMA.R_Erdos573_erdos_573_R1
