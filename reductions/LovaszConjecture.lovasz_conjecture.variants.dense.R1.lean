import FormalConjectures.Wikipedia.LovaszConjecture
import Mathlib

/-! The Hamiltonian path corollary from the Hamiltonian cycle theorem. Christofides, Hladký
and Máthé, Hamilton cycles in dense vertex-transitive graphs, J. Combin. Theory Ser. B 109
(2014), Theorem 2: for every ε > 0 there is n₀ such that every connected vertex-transitive
graph on n ≥ n₀ vertices with degree at least ε n has a Hamiltonian cycle. Removing the
first edge of a Hamiltonian cycle leaves a Hamiltonian path. -/

namespace OMA.R_LovaszConjecture_lovasz_conjecture_variants_dense_R1
open SimpleGraph

/-- The Hamiltonian cycle theorem of Christofides, Hladký and Máthé. -/
def H1 : Prop := ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
    G.Connected → LovaszConjecture.IsVertexTransitive G → ε * Fintype.card V ≤ G.minDegree →
    ∃ (v : V) (c : G.Walk v v), c.IsHamiltonianCycle

/-- A graph with a Hamiltonian cycle has a Hamiltonian path. -/
def H2 : Prop := ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V)
    (c : G.Walk v v), c.IsHamiltonianCycle → LovaszConjecture.HasHamiltonianPath G

theorem main : H1 → H2 →
    type_of% @LovaszConjecture.lovasz_conjecture.variants.dense := by
  intro hchm hpath ε hε
  obtain ⟨n₀, h⟩ := hchm ε hε
  refine ⟨n₀, ?_⟩
  intro V _ _ G _ hn hconn htrans hdeg
  obtain ⟨v, c, hc⟩ := h G hn hconn htrans hdeg
  exact hpath G v c hc

end OMA.R_LovaszConjecture_lovasz_conjecture_variants_dense_R1
