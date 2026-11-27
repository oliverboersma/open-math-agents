import Mathlib

/-!
# Is there a non-bipartite hamiltonian cubic graph on $n$ vertices with no $(n-1)$-cycle?

Source: https://mathoverflow.net/questions/263706
Credit: @zarnab222-dev

The question asks whether there is a cubic (3-regular) graph `G` on `n` vertices that is
hamiltonian, has no cycle of length `n - 1`, and is not bipartite. The affirmative claim is stated.

Translation choices:
* a graph on `n` vertices is a `SimpleGraph (Fin n)` (simple, as usual for cubic graphs), with `n`
  existentially quantified;
* cubic: every vertex has exactly three neighbours, `(G.neighborSet v).ncard = 3` (`Fin n` is
  finite, so `Set.ncard` is the true cardinality; this needs no decidability instance on `G`);
* hamiltonian: Mathlib's `SimpleGraph.IsHamiltonian` (a hamiltonian cycle exists; its convention
  that a one-vertex graph is hamiltonian is irrelevant, since a cubic graph has at least 4 vertices);
* an `(n-1)`-cycle is a closed walk `p` with `p.IsCycle` (no repeated edge or vertex) of length
  `n - 1`; cubic forces `n ≥ 4`, so the truncated subtraction is the ordinary one;
* not bipartite: `¬ G.IsBipartite`, where `IsBipartite` is 2-colourability.
-/

namespace OMA.S_mo_263706

theorem main :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ v : Fin n, (G.neighborSet v).ncard = 3) ∧
      G.IsHamiltonian ∧
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → p.length ≠ n - 1) ∧
      ¬ G.IsBipartite := by
  sorry

end OMA.S_mo_263706
