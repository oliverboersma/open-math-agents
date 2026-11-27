import FormalConjectures.ErdosProblems.«133»
import Mathlib

/-! The conjecture f(n) ~ sqrt n for the minimal maximum degree of a triangle-free graph of
diameter 2 has two halves. The asymptotic lower bound (1 - eps) sqrt n <= f(n) is known; it is
the catalogue's solved variant Erdos133.erdos_133.variants.lower_bound. The matching asymptotic
upper bound is the open part: the best known constant is 2 / sqrt 3 (Füredi and Seress, see
Erdos133.erdos_133.variants.furedi_seress). -/

namespace OMA.R_Erdos133_erdos_133_variants_asymptotic_R1

open Filter Asymptotics

/-- The known asymptotic lower bound. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (1 - ε) * Real.sqrt (n : ℝ) ≤ (Erdos133.f n : ℝ)

/-- The open asymptotic upper bound. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (Erdos133.f n : ℝ) ≤ (1 + ε) * Real.sqrt (n : ℝ)

theorem main : H1 → H2 → type_of% @Erdos133.erdos_133.variants.asymptotic := by
  intro h1 h2
  refine Asymptotics.isLittleO_iff.mpr ?_
  intro c hc
  filter_upwards [h1 c hc, h2 c hc] with n hl hu
  have hs : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_of_nonneg hs, abs_le]
  constructor <;> nlinarith

end OMA.R_Erdos133_erdos_133_variants_asymptotic_R1
