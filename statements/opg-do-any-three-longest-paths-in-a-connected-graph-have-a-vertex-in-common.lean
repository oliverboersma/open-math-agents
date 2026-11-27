import Mathlib

/-!
# Do any three longest paths in a connected graph have a vertex in common?

Source: https://www.openproblemgarden.org/op/do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common
Credit: @LAPRAI

*Reference:* T. Gallai, Problem 6, in: Theory of Graphs (Proc. Colloq., Tihany, 1966), Academic
Press, 1968, p. 362.

Question: do any three longest paths in a connected graph have a vertex in common? (Any two
always do; Skupień found connected graphs where seven longest paths share no vertex.)

## Encoding

* Graphs are finite, connected Mathlib `SimpleGraph`s.
* A path is a walk `p` with `p.IsPath`; it is *longest* if no path of `G` is longer.
* The three longest paths need not be distinct; they have a vertex in common if some vertex lies
  on all three.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer no.
-/

namespace OMA.S_opg_do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common

/-- `p` is a longest path of `G`. -/
def IsLongestPath {V : Type} {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Prop :=
  p.IsPath ∧ ∀ (c d : V) (q : G.Walk c d), q.IsPath → q.length ≤ p.length

/-- Any three longest paths of a finite connected graph share a vertex. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected →
    ∀ (a₁ b₁ a₂ b₂ a₃ b₃ : V) (p₁ : G.Walk a₁ b₁) (p₂ : G.Walk a₂ b₂) (p₃ : G.Walk a₃ b₃),
      IsLongestPath p₁ → IsLongestPath p₂ → IsLongestPath p₃ →
      ∃ v, v ∈ p₁.support ∧ v ∈ p₂.support ∧ v ∈ p₃.support := by
  sorry

end OMA.S_opg_do_any_three_longest_paths_in_a_connected_graph_have_a_vertex_in_common
