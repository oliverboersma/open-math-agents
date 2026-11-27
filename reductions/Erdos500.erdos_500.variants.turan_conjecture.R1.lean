import FormalConjectures.ErdosProblems.«500»
import Mathlib

/-! Turán's conjecture says that the largest number of triples on n vertices with no complete
3-graph on 4 vertices is asymptotic to (5/9) (n choose 3). The asymptotic lower bound is known:
it is Turán's construction, the catalogue's solved variant
Erdos500.erdos_500.variants.lower_bound. The matching asymptotic upper bound is the open part
(the best known constant is 0.561666, see Erdos500.erdos_500.variants.upper_bound). -/

namespace OMA.R_Erdos500_erdos_500_variants_turan_conjecture_R1

open Filter Asymptotics

/-- Turán's construction: the extremal number is at least (5/9 - eps) (n choose 3). -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (5 / 9 - ε) * (n.choose 3 : ℝ) ≤ Hypergraph.cliqueExtremalNumber n 3 4

/-- The open upper bound: the extremal number is at most (5/9 + eps) (n choose 3). -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    (Hypergraph.cliqueExtremalNumber n 3 4 : ℝ) ≤ (5 / 9 + ε) * (n.choose 3 : ℝ)

theorem main : H1 → H2 → type_of% @Erdos500.erdos_500.variants.turan_conjecture := by
  intro h1 h2
  refine Asymptotics.isLittleO_iff.mpr ?_
  intro c hc
  have hε : 0 < c * (5 / 9) := by positivity
  filter_upwards [h1 (c * (5 / 9)) hε, h2 (c * (5 / 9)) hε] with n hl hu
  have hC : (0 : ℝ) ≤ (n.choose 3 : ℝ) := Nat.cast_nonneg _
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), abs_le]
  constructor <;> nlinarith

end OMA.R_Erdos500_erdos_500_variants_turan_conjecture_R1
