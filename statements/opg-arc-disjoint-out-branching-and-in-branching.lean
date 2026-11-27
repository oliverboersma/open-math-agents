import Mathlib

/-!
# Arc-disjoint out-branching and in-branching

Source: https://www.openproblemgarden.org/op/arc_disjoint_out_branching_and_in_branching
Credit: @LAPRAI

Conjecture (Thomassen): there exists an integer `k` such that every `k`-arc-strong digraph `D`
with specified vertices `u` and `v` contains an out-branching rooted at `u` and an in-branching
rooted at `v` which are arc-disjoint.

## Encoding

* `D` is a Mathlib `Digraph` on a finite vertex type; arcs are ordered pairs `(a, b)` with
  `D.Adj a b`, and a set of arcs is a `Set (V × V)`.
* `D` is strongly connected if every vertex reaches every other one by a directed walk
  (`Relation.ReflTransGen`). `D` is `k`-arc-strong if it stays strongly connected after deleting
  any set of fewer than `k` arcs.
* An out-branching rooted at `u` is a set `B` of arcs of `D` such that `u` has no in-arc in `B`,
  every other vertex has exactly one in-arc in `B`, and every vertex is reachable from `u` using
  arcs of `B` (a spanning arborescence directed away from `u`). An in-branching rooted at `v` is
  the same with all arcs reversed.
-/

namespace OMA.S_opg_arc_disjoint_out_branching_and_in_branching

/-- `D` with the arcs of `X` deleted is strongly connected. -/
def StronglyConnectedWithout {V : Type} (D : Digraph V) (X : Set (V × V)) : Prop :=
  ∀ a b, Relation.ReflTransGen (fun x y => D.Adj x y ∧ (x, y) ∉ X) a b

/-- `D` is `k`-arc-strong. -/
def IsArcStrong {V : Type} (D : Digraph V) (k : ℕ) : Prop :=
  ∀ X : Finset (V × V), X.card < k → StronglyConnectedWithout D ↑X

/-- `B` is an out-branching of `D` rooted at `u`. -/
def IsOutBranching {V : Type} (D : Digraph V) (u : V) (B : Set (V × V)) : Prop :=
  (∀ p ∈ B, D.Adj p.1 p.2) ∧ (∀ a, (a, u) ∉ B) ∧
    (∀ w, w ≠ u → ∃! a, (a, w) ∈ B) ∧
    ∀ w, Relation.ReflTransGen (fun x y => (x, y) ∈ B) u w

/-- `B` is an in-branching of `D` rooted at `v`. -/
def IsInBranching {V : Type} (D : Digraph V) (v : V) (B : Set (V × V)) : Prop :=
  (∀ p ∈ B, D.Adj p.1 p.2) ∧ (∀ b, (v, b) ∉ B) ∧
    (∀ w, w ≠ v → ∃! b, (w, b) ∈ B) ∧
    ∀ w, Relation.ReflTransGen (fun x y => (x, y) ∈ B) w v

/-- **Thomassen's conjecture.** -/
theorem main : ∃ k : ℕ, ∀ (V : Type) [Fintype V] (D : Digraph V), IsArcStrong D k →
    ∀ u v : V, ∃ B₁ B₂ : Set (V × V),
      IsOutBranching D u B₁ ∧ IsInBranching D v B₂ ∧ Disjoint B₁ B₂ := by
  sorry

end OMA.S_opg_arc_disjoint_out_branching_and_in_branching
