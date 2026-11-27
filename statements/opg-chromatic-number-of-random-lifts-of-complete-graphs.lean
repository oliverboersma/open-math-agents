import Mathlib

/-!
# Chromatic number of random lifts of complete graphs

Source: https://www.openproblemgarden.org/op/chromatic_number_of_random_lifts_of_complete_graphs
Credit: @lzvxck

The source: is the chromatic number of a random lift of `K_5` concentrated on a single value?
An `h`-lift `H` of `G = (V, E)` is a graph with vertex set `V × {1, ..., h}` such that
`(u, k)` and `(v, l)` may only be adjacent if `uv ∈ E`, and for each `uv ∈ E` the edges between
`{u} × {1, ..., h}` and `{v} × {1, ..., h}` form a perfect matching. A random `h`-lift is drawn
uniformly from all `h`-lifts, which amounts to choosing, independently at random, a perfect
matching for each edge of `G`. The question asks whether the chromatic number of a random
`h`-lift of `K_5` is asymptotically almost surely a single number (it is `3` or `4`).

This file states the affirmative answer to the `K_5` question (the page's more general question
for `K_n` is not part of it). Conventions: the vertices of `K_5` are `Fin 5` and its edges are
the pairs `(u, v)` with `u < v`. An `h`-lift is given by a permutation `σ (u, v)` of `Fin h` for
each edge, the matching between `{u} × Fin h` and `{v} × Fin h` joining `(u, a)` to
`(v, σ (u, v) a)`; this is a bijection between such families and `h`-lifts, so the uniform
random lift is the uniform random family. "Asymptotically almost surely `k`" means the
proportion of families whose lift has chromatic number `k` tends to `1` as `h → ∞`.
-/

namespace OMA.S_opg_chromatic_number_of_random_lifts_of_complete_graphs

/-- The edges of `K_5`, as pairs `(u, v)` with `u < v`. -/
abbrev K5Edge := {p : Fin 5 × Fin 5 // p.1 < p.2}

/-- The `h`-lift of `K_5` given by the permutations `σ`. -/
def lift {h : ℕ} (σ : K5Edge → Equiv.Perm (Fin h)) : SimpleGraph (Fin 5 × Fin h) :=
  SimpleGraph.fromRel fun x y => ∃ hlt : x.1 < y.1, y.2 = σ ⟨(x.1, y.1), hlt⟩ x.2

open Classical in
/-- The probability that a uniformly random `h`-lift of `K_5` has chromatic number `k`. -/
noncomputable def probChromatic (h : ℕ) (k : ℕ∞) : ℝ :=
  ((Finset.univ.filter fun σ : K5Edge → Equiv.Perm (Fin h) =>
      (lift σ).chromaticNumber = k).card : ℝ) /
    Fintype.card (K5Edge → Equiv.Perm (Fin h))

/-- **Chromatic number of random lifts of `K_5` (Amit, Linial, Matoušek).** The chromatic number
of a random `h`-lift of `K_5` is asymptotically almost surely a single value `k`. -/
theorem main : ∃ k : ℕ∞, Filter.Tendsto (fun h : ℕ => probChromatic h k) Filter.atTop
    (nhds 1) := by
  sorry

end OMA.S_opg_chromatic_number_of_random_lifts_of_complete_graphs
