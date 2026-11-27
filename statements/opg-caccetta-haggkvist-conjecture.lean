import Mathlib

/-!
# Caccetta-Häggkvist Conjecture

Source: https://www.openproblemgarden.org/op/caccetta_haggkvist_conjecture
Credit: @LAPRAI

*Reference:* L. Caccetta and R. Häggkvist, On minimal digraphs with given girth, Congress.
Numer. 21 (1978).

Every simple digraph of order `n` with minimum outdegree at least `r ≥ 1` has a (directed) cycle
of length at most `⌈n / r⌉`.

## Encoding

* A digraph is Mathlib's `Digraph V` on a finite nonempty vertex type `V` (order `n = |V| ≥ 1`;
  for the empty digraph the hypothesis on outdegrees is vacuous and there is no cycle).
* *Simple*: no loops. A `Digraph` has at most one arc from `u` to `v`, so there are no parallel
  arcs; opposite arcs `u → v`, `v → u` are allowed, as in the source's simple digraphs.
* The outdegree of `v` is the number of `w` with an arc `v → w`.
* A directed cycle of length `k ≥ 2` is an injective sequence `c 0, …, c (k-1)` of vertices with
  an arc from each `c i` to `c (i + 1 mod k)`.
-/

namespace OMA.S_opg_caccetta_haggkvist_conjecture

/-- The outdegree of `v` in `G`. -/
def outdegree {V : Type} [Fintype V] (G : Digraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w)).card

/-- `G` has a directed cycle of length exactly `k` (with `k ≥ 2`). -/
def HasDirectedCycleOfLength {V : Type} (G : Digraph V) (k : ℕ) : Prop :=
  2 ≤ k ∧ ∃ c : Fin k → V, Function.Injective c ∧ ∀ i : Fin k, G.Adj (c i) (c (finRotate k i))

/-- **Caccetta–Häggkvist conjecture.** -/
theorem main : ∀ (V : Type) [Fintype V] [Nonempty V] (G : Digraph V) [DecidableRel G.Adj] (r : ℕ),
    1 ≤ r → (∀ v, ¬ G.Adj v v) → (∀ v, r ≤ outdegree G v) →
    ∃ k, k ≤ ⌈(Fintype.card V : ℚ) / r⌉₊ ∧ HasDirectedCycleOfLength G k := by
  sorry

end OMA.S_opg_caccetta_haggkvist_conjecture
