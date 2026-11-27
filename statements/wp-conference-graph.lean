import Mathlib

/-!
# Existence of conference graphs

Source: https://en.wikipedia.org/wiki/conference_graph
Credit: @prophetlabs

Source statement (Wikipedia, *List of unsolved problems in mathematics*): does there exist a
conference graph for every number of vertices `v > 1` where `v ≡ 1 mod 4` and `v` is an odd sum
of two squares?

A conference graph on `v` vertices is a strongly regular graph with parameters
`(v, (v - 1)/2, (v - 5)/4, (v - 1)/4)`. The condition `v ≡ 1 mod 4` already makes `v` odd and
makes these parameters integers. The question is stated here in its positive form.
-/

namespace OMA.S_wp_conference_graph

open SimpleGraph

open scoped Classical in
theorem main :
    ∀ v : ℕ, 1 < v → v % 4 = 1 → (∃ a b : ℕ, v = a ^ 2 + b ^ 2) →
      ∃ G : SimpleGraph (Fin v), G.IsSRGWith v ((v - 1) / 2) ((v - 5) / 4) ((v - 1) / 4) := by
  sorry

end OMA.S_wp_conference_graph
