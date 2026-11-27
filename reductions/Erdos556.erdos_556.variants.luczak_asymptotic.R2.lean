import FormalConjectures.ErdosProblems.«556»

-- Reduction Erdos556.erdos_556.variants.luczak_asymptotic.R2 of Erdős Problem 556 — luczak asymptotic
-- Credit: @PanPapag
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos556_erdos_556_variants_luczak_asymptotic_R2

-- The merged even-cycle proof gives H1 by specializing its slack to one.
-- Hanan Beer's odd-cycle formalization in PR 7648 gives H2 from the sharper
-- equality 4*n-3 of Kohayakawa, Simonovits and Skokan.
open Filter SimpleGraph

def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, Even n → multicolourRamsey (cycleGraph n) 3 ≤ 4*n

def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, Odd n → multicolourRamsey (cycleGraph n) 3 ≤ 4*n

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.luczak_asymptotic := by
  intro he ho ε hε
  unfold H1 at he
  unfold H2 at ho
  filter_upwards [he, ho] with n hn₁ hn₂
  have hn := (Nat.even_or_odd n).elim hn₁ hn₂
  calc
    _ ≤ ((4*n : ℕ) : ℝ) := by exact_mod_cast hn
    _ ≤ (4+ε)*n := by push_cast; nlinarith [mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) n)]

end OMA.R_Erdos556_erdos_556_variants_luczak_asymptotic_R2
