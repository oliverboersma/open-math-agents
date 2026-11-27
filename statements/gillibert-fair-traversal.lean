import Mathlib

/-!
# Fair traversal conjecture (Hamiltonian paths in vertex-transitive graphs)

Source: https://github.com/Gillibert/ConjecturesGillibert/blob/main/fair_traversal_conjecture.tex
Credit: @Gillibert

Every finite connected vertex-transitive graph with at least two vertices admits a nonempty
finite multiset of Hamiltonian paths in which every edge occurs equally often.

Explicit form used here (from the source): there are positive integers `r, k` and Hamiltonian
paths `P 0, …, P (r - 1)`, not necessarily distinct, such that every edge `e` of `G` lies on
exactly `k` of them.

Translation notes:
* The multiset is an indexed family `P : ∀ i : Fin r, G.Walk (a i) (b i)`; repetitions are
  allowed, so this is exactly a finite multiset of Hamiltonian paths.
* `Walk.IsHamiltonian` (Mathlib) means every vertex occurs exactly once in the walk.
* A path and its reverse have the same edges, so orienting each path changes nothing.
* `IsVertexTransitive` is the same definition as `LovaszConjecture.IsVertexTransitive`
  in formal-conjectures. Taking `P 0` recovers `LovaszConjecture.HasHamiltonianPath`.
-/

namespace OMA.S_gillibert_fair_traversal

open SimpleGraph

/-- A graph is vertex-transitive if any vertex can be mapped to any other by an automorphism. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, ∃ φ : G ≃g G, φ u = v

theorem main :
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.Connected → IsVertexTransitive G → 2 ≤ Fintype.card V →
      ∃ (r k : ℕ), 0 < r ∧ 0 < k ∧
        ∃ (a b : Fin r → V) (P : ∀ i, G.Walk (a i) (b i)),
          (∀ i, (P i).IsHamiltonian) ∧
          ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (P i).edges).card = k := by
  sorry

end OMA.S_gillibert_fair_traversal
