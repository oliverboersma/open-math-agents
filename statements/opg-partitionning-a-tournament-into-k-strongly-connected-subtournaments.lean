import Mathlib

/-!
# Partitionning a tournament into k-strongly connected subtournaments.

Source: https://www.openproblemgarden.org/op/partitionning_a_tournament_into_k_strongly_connected_subtournaments
Credit: @LAPRAI

Problem: let `k₁, …, k_p` be positive integers. Does there exist an integer `g(k₁, …, k_p)` such
that every `g(k₁, …, k_p)`-strong tournament `T` admits a partition `(V₁, …, V_p)` of its vertex
set such that the subtournament induced by `Vᵢ` is a non-trivial `kᵢ`-strong for all `i`?

## Encoding

* A tournament is a finite Mathlib `Digraph V` with no loops in which, for any two distinct
  vertices `u, v`, exactly one of the arcs `u → v`, `v → u` is present.
* For a vertex set `S`, the subdigraph induced by `S` is *strong* if any two vertices of `S` are
  joined by a directed walk staying inside `S`.
* `S` induces a *`k`-strong* subdigraph (standard definition): `|S| > k`, and deleting any set
  `X` of fewer than `k` vertices leaves `S \ X` strong. *Non-trivial*: at least two vertices.
  The whole tournament is `k`-strong when `S = univ`.
* A partition `(V₁, …, V_p)` is a map `part : V → Fin p` with `Vᵢ = part⁻¹(i)`; `p ≥ 1` (a
  partition into no parts only exists for the empty tournament).
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer no.
-/

namespace OMA.S_opg_partitionning_a_tournament_into_k_strongly_connected_subtournaments

/-- `G` is a tournament. -/
def IsTournament {V : Type} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ ∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u)

/-- The subdigraph of `G` induced by `S` is strong. -/
def IsStrongOn {V : Type} (G : Digraph V) (S : Set V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ G.Adj x y) u v

/-- The subdigraph of `G` induced by `S` is `k`-strong. -/
def IsKStrongOn {V : Type} (G : Digraph V) (S : Set V) (k : ℕ) : Prop :=
  k < S.ncard ∧ ∀ X : Finset V, X.card < k → IsStrongOn G (S \ ↑X)

/-- For all positive `k₁, …, k_p` there is `g` such that every `g`-strong tournament splits into
non-trivial `kᵢ`-strong subtournaments `V₁, …, V_p`. -/
theorem main : ∀ (p : ℕ) (k : Fin p → ℕ), 1 ≤ p → (∀ i, 1 ≤ k i) → ∃ g : ℕ,
    ∀ (V : Type) [Fintype V] (G : Digraph V), IsTournament G → IsKStrongOn G Set.univ g →
      ∃ part : V → Fin p, ∀ i, 2 ≤ (part ⁻¹' {i}).ncard ∧ IsKStrongOn G (part ⁻¹' {i}) (k i) := by
  sorry

end OMA.S_opg_partitionning_a_tournament_into_k_strongly_connected_subtournaments
