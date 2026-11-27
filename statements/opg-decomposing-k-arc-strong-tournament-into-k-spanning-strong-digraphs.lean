import Mathlib

/-!
# Decomposing k-arc-strong tournament into k spanning strong digraphs

Source: https://www.openproblemgarden.org/op/decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs
Credit: @LAPRAI

Conjecture (Bang-Jensen and Yeo): every `k`-arc-strong tournament decomposes into `k` spanning
strong digraphs.

## Encoding

* A tournament is a finite Mathlib `Digraph V` with no loops in which, for any two distinct
  vertices `u, v`, exactly one of the arcs `u → v`, `v → u` is present.
* *Strong*: every vertex reaches every vertex along arcs.
* *`k`-arc-strong* (standard definition): deleting any set of fewer than `k` arcs leaves a strong
  digraph. `k ≥ 1` (for `k = 0` there is nothing to decompose into).
* *Decomposes into `k` spanning strong digraphs*: the arc set is split into `k` classes (a
  labelling `col u v : Fin k` of each arc `u → v`) such that, for each class `i`, the digraph on
  all of `V` formed by the arcs of class `i` is strong.
-/

namespace OMA.S_opg_decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs

/-- `G` is a tournament. -/
def IsTournament {V : Type} (G : Digraph V) : Prop :=
  (∀ v, ¬ G.Adj v v) ∧ ∀ u v, u ≠ v → (G.Adj u v ↔ ¬ G.Adj v u)

/-- `G` is strong (strongly connected). -/
def IsStrong {V : Type} (G : Digraph V) : Prop :=
  ∀ u v, Relation.ReflTransGen G.Adj u v

/-- `G` minus the arcs in `F`. -/
def deleteArcs {V : Type} (G : Digraph V) (F : Finset (V × V)) : Digraph V where
  Adj u v := G.Adj u v ∧ (u, v) ∉ F

/-- `G` is `k`-arc-strong: deleting fewer than `k` arcs leaves it strong. -/
def IsKArcStrong {V : Type} (G : Digraph V) (k : ℕ) : Prop :=
  ∀ F : Finset (V × V), F.card < k → IsStrong (deleteArcs G F)

/-- **Bang-Jensen–Yeo conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] (G : Digraph V) (k : ℕ), 1 ≤ k → IsTournament G →
    IsKArcStrong G k →
    ∃ col : V → V → Fin k, ∀ i : Fin k,
      IsStrong ({ Adj := fun u v => G.Adj u v ∧ col u v = i } : Digraph V) := by
  sorry

end OMA.S_opg_decomposing_k_arc_strong_tournament_into_k_spanning_strong_digraphs
