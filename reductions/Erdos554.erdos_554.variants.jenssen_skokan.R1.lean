import FormalConjectures.ErdosProblems.«554»
import Mathlib

/-! The multicolour Ramsey number of a long odd cycle, R_k(C_(2n+1)) = n 2^k + 1 for large n,
split into its two halves. The upper bound is the theorem of Jenssen and Skokan, Exact Ramsey
numbers of odd cycles via nonlinear optimisation, Adv. Math. 376 (2021). The lower bound holds
for all n and k and comes from the classical colouring by binary labels on blocks of 2n
vertices; it is the catalogue's Erdos554.erdos_554.variants.lower_bound. -/

namespace OMA.R_Erdos554_erdos_554_variants_jenssen_skokan_R1
open Filter SimpleGraph

/-- Jenssen and Skokan: the upper bound for large n. -/
def H1 : Prop := ∀ k : ℕ, 2 ≤ k → ∀ᶠ n : ℕ in atTop,
  multicolourGraphRamsey k (cycleGraph (2 * n + 1)) ≤ n * 2 ^ k + 1

/-- The classical lower bound, for all n and k. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k →
  n * 2 ^ k + 1 ≤ multicolourGraphRamsey k (cycleGraph (2 * n + 1))

theorem main : H1 → H2 → type_of% @Erdos554.erdos_554.variants.jenssen_skokan := by
  intro h1 h2 k hk
  filter_upwards [h1 k hk, eventually_ge_atTop 1] with n hn hn1
  exact le_antisymm hn (h2 n hn1 k (by omega))

end OMA.R_Erdos554_erdos_554_variants_jenssen_skokan_R1
