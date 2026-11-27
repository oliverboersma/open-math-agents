import FormalConjectures.Wikipedia.VizingConjecture

-- Reduction VizingConjecture.vizing_conjecture.R1 of Vizing's conjecture
-- Credit: @marcusbuffett

/-!
# Vizing's conjecture: a factor with domination number at most one, and the open rest

Vizing's conjecture says that the domination number of a Cartesian product of two finite graphs
is at least the product of the domination numbers.

* `H1`: the conjecture when one of the two graphs has domination number at most one. Projecting
  a dominating set of the product to a factor gives a dominating set of that factor, so the
  domination number of the product is at least that of each (nonempty) factor.
* `H2`: the conjecture when both domination numbers are at least two. This is open (it is known
  when one of them is at most three, by Barcalkin and German for two and Sun for three, but
  those proofs are not formalized here).
-/

open SimpleGraph

namespace OMA.R_VizingConjecture_vizing_conjecture_R1

/-- One of the two domination numbers is at most one. -/
def H1 : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β),
    G.dominationNumber ≤ 1 ∨ H.dominationNumber ≤ 1 →
    G.dominationNumber * H.dominationNumber ≤ (G □ H).dominationNumber

/-- The open part: both domination numbers are at least two. -/
def H2 : Prop :=
  ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β),
    2 ≤ G.dominationNumber → 2 ≤ H.dominationNumber →
    G.dominationNumber * H.dominationNumber ≤ (G □ H).dominationNumber

theorem main : H1 → H2 → type_of% @VizingConjecture.vizing_conjecture := by
  intro h1 h2 α β _ _ _ _ G H
  by_cases h : G.dominationNumber ≤ 1 ∨ H.dominationNumber ≤ 1
  · exact h1 G H h
  · exact h2 G H (by omega) (by omega)

end OMA.R_VizingConjecture_vizing_conjecture_R1

