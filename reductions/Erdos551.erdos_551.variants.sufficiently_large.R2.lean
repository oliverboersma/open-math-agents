import FormalConjectures.ErdosProblems.«551»

-- Reduction Erdos551.erdos_551.variants.sufficiently_large.R2 of Erdős Problem 551 — sufficiently large
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The identity `R(C_k, K_n) = (k-1)(n-1)+1` is an equality of natural numbers, so it splits into
-- the two inequalities. The lower bound is elementary: in a graph on fewer than `(k-1)(n-1)+1`
-- vertices, `n-1` disjoint cliques of size `k-1` contain no `C_k`, while their complement is
-- `(k-1)`-partite and so contains no `K_n`. The upper bound is the content of the theorem: every
-- graph on `(k-1)(n-1)+1` vertices has a `C_k` or its complement has a `K_n`.

namespace OMA.R_Erdos551_erdos_551_variants_sufficiently_large_R2

open SimpleGraph Filter

/-- The lower bound: `(k-1)(n-1)+1 ≤ R(C_k, K_n)` for all `k ≥ n`. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, n ≤ k →
    (k - 1) * (n - 1) + 1 ≤
      graphRamsey (cycleGraph k) (completeGraph (Fin n))

/-- The upper bound: every graph on `(k-1)(n-1)+1` vertices contains a `C_k` or its complement
contains a `K_n`, for all `k ≥ n` and all large `n`. -/
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, n ≤ k →
    graphRamsey (cycleGraph k) (completeGraph (Fin n)) ≤
      (k - 1) * (n - 1) + 1

theorem main : H1 → H2 → type_of% @Erdos551.erdos_551.variants.sufficiently_large := by
  intro h1 h2
  filter_upwards [h1, h2] with n hn₁ hn₂
  intro k hk
  exact le_antisymm (hn₂ k hk) (hn₁ k hk)

end OMA.R_Erdos551_erdos_551_variants_sufficiently_large_R2
