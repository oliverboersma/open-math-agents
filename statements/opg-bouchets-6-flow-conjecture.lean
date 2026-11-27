import Mathlib

/-!
# Bouchet's 6-flow conjecture

Source: https://www.openproblemgarden.org/op/bouchets_6_flow_conjecture
Credit: @lzvxck

The source: every bidirected graph with a nowhere-zero `k`-flow for some `k` has a
nowhere-zero `6`-flow. A bidirected graph is a graph in which every edge has two arrowheads,
one next to each endpoint, each pointing toward or away from that endpoint. A `k`-flow is a map
`φ : E(G) → {-(k-1), ..., k-1}` such that at every vertex, the sum of `φ` on the edges whose
ends at `v` are directed into `v` equals the sum of `φ` on the edges whose ends at `v` are
directed out of `v`; it is nowhere-zero if `φ(e) ≠ 0` for every edge.

Conventions: graphs are finite multigraphs (parallel edges and loops allowed): a finite vertex
type `V`, a finite edge type `E`, and for each edge `e` two ends `src e` and `tgt e`, with
`inSrc e` (resp. `inTgt e`) true when the arrowhead next to `src e` (resp. `tgt e`) points
toward that end. A loop has both of its ends at the same vertex and contributes both. The
conservation law "in = out" at `v` is written as: the signed sum over the ends at `v`
(`+φ e` for an end directed into `v`, `-φ e` for an end directed out of `v`) is zero.
-/

namespace OMA.S_opg_bouchets_6_flow_conjecture

/-- `+1` for an end directed into its vertex, `-1` for an end directed out of it. -/
def sgn (b : Bool) : ℤ := if b then 1 else -1

/-- `φ` is a nowhere-zero `k`-flow on the bidirected multigraph `(V, E, src, tgt, inSrc, inTgt)`:
values are nonzero integers of absolute value below `k`, and at every vertex the flow directed
in equals the flow directed out. -/
def IsNowhereZeroFlow {V E : Type*} [Fintype E] [DecidableEq V] (src tgt : E → V)
    (inSrc inTgt : E → Bool) (k : ℕ) (φ : E → ℤ) : Prop :=
  (∀ e, φ e ≠ 0 ∧ |φ e| < k) ∧
  ∀ v, (∑ e ∈ Finset.univ.filter (fun e => src e = v), sgn (inSrc e) * φ e) +
      (∑ e ∈ Finset.univ.filter (fun e => tgt e = v), sgn (inTgt e) * φ e) = 0

/-- **Bouchet's 6-flow conjecture.** A finite bidirected multigraph that has a nowhere-zero
`k`-flow for some `k` has a nowhere-zero `6`-flow. -/
theorem main : ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] (src tgt : E → V)
    (inSrc inTgt : E → Bool),
    (∃ (k : ℕ) (φ : E → ℤ), IsNowhereZeroFlow src tgt inSrc inTgt k φ) →
      ∃ φ : E → ℤ, IsNowhereZeroFlow src tgt inSrc inTgt 6 φ := by
  sorry

end OMA.S_opg_bouchets_6_flow_conjecture
