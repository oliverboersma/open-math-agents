import Mathlib

/-!
# Lovász Path Removal Conjecture

Source: https://www.openproblemgarden.org/op/lovasz_path_removal_conjecture
Credit: @LAPRAI

Conjecture (Lovász): there is an integer-valued function `f(k)` such that if `G` is any
`f(k)`-connected graph and `x` and `y` are any two vertices of `G`, then there exists an induced
path `P` with ends `x` and `y` such that `G - V(P)` is `k`-connected.

## Encoding

* Graphs are finite Mathlib `SimpleGraph`s; `x ≠ y` (two vertices).
* `k`-connected (standard definition): more than `k` vertices, and deleting any set of fewer than
  `k` vertices leaves a connected graph. Mathlib has no vertex-connectivity notion, so it is
  defined here (with `Nat.card`, so that it applies directly to induced subgraphs).
* An induced path from `x` to `y` is a path `p` (a walk with `p.IsPath`) such that every edge of
  `G` between two vertices of `p` is an edge of `p`.
* `G - V(P)` is the subgraph induced on the vertices not on `p`.
-/

namespace OMA.S_opg_lovasz_path_removal_conjecture

/-- `G` is `k`-connected: it has more than `k` vertices and stays connected after deleting any
set of fewer than `k` vertices. -/
def IsKConnected {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Nat.card V ∧ ∀ S : Finset V, S.card < k → (G.induce (↑S : Set V)ᶜ).Connected

/-- `p` is an induced path of `G`. -/
def IsInducedPath {V : Type} {G : SimpleGraph V} {x y : V} (p : G.Walk x y) : Prop :=
  p.IsPath ∧ ∀ u ∈ p.support, ∀ v ∈ p.support, G.Adj u v → s(u, v) ∈ p.edges

/-- **Lovász path removal conjecture.** -/
theorem main : ∃ f : ℕ → ℕ, ∀ (k : ℕ) (V : Type) [Fintype V] (G : SimpleGraph V),
    IsKConnected G (f k) → ∀ x y : V, x ≠ y →
    ∃ p : G.Walk x y, IsInducedPath p ∧ IsKConnected (G.induce {v | v ∉ p.support}) k := by
  sorry

end OMA.S_opg_lovasz_path_removal_conjecture
