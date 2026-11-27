import Mathlib

/-!
# Decomposing an even tournament in directed paths

Source: https://www.openproblemgarden.org/op/decomposing_an_even_tournament_in_directed_paths
Credit: @LAPRAI

Conjecture (Alspach, Mason, Pullman): every tournament `D` on an even number of vertices can be
decomposed into `∑_{v ∈ V} max {0, d⁺(v) - d⁻(v)}` directed paths.

## Encoding

* A tournament is a Mathlib `Digraph` on a finite vertex type with no loops and, for any two
  distinct vertices, exactly one of the two arcs between them.
* `d⁺(v)`, `d⁻(v)` are the numbers of out- and in-neighbours of `v`; `max {0, d⁺ - d⁻}` is the
  truncated subtraction `d⁺ - d⁻` in `ℕ`.
* A directed path with `ℓ ≥ 1` arcs is an injective sequence `p 0, …, p ℓ` of vertices with an
  arc `p i → p (i + 1)` for each `i < ℓ`; its arcs are these `ℓ` pairs.
* A decomposition into `N` directed paths is a family of `N` directed paths such that every arc
  of `D` lies on exactly one of them.
-/

namespace OMA.S_opg_decomposing_an_even_tournament_in_directed_paths

/-- `D` is a tournament. -/
def IsTournament {V : Type} (D : Digraph V) : Prop :=
  (∀ v, ¬ D.Adj v v) ∧ ∀ u v, u ≠ v → (D.Adj u v ↔ ¬ D.Adj v u)

/-- `p` is a directed path of `D` with `ℓ ≥ 1` arcs. -/
def IsDirectedPath {V : Type} (D : Digraph V) {ℓ : ℕ} (p : Fin (ℓ + 1) → V) : Prop :=
  1 ≤ ℓ ∧ Function.Injective p ∧ ∀ i : Fin ℓ, D.Adj (p i.castSucc) (p i.succ)

/-- The arc `(u, v)` is an arc of the path `p`. -/
def OnPath {V : Type} {ℓ : ℕ} (p : Fin (ℓ + 1) → V) (u v : V) : Prop :=
  ∃ i : Fin ℓ, p i.castSucc = u ∧ p i.succ = v

/-- **Alspach–Mason–Pullman conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj],
    IsTournament D → Even (Fintype.card V) →
    ∃ (len : Fin (∑ v : V, ((Finset.univ.filter (fun w => D.Adj v w)).card -
          (Finset.univ.filter (fun w => D.Adj w v)).card)) → ℕ)
      (path : ∀ j, Fin (len j + 1) → V),
      (∀ j, IsDirectedPath D (path j)) ∧
      ∀ u v, D.Adj u v → ∃! j, OnPath (path j) u v := by
  sorry

end OMA.S_opg_decomposing_an_even_tournament_in_directed_paths
