import Mathlib

/-!
# Disproportionate division

Source: https://arxiv.org/abs/1909.07141 (Crew, Narayanan, Spirkl; Bull. London Math. Soc. 52 (2020)).
Credit: @tatashbar

Setting of the source (Section 1). The cake is `[0,1]`. There are `n ≥ 2` agents with non-atomic
Borel probability measures `μ 1, …, μ n` on `[0,1]` and non-negative demands `α 1, …, α n` summing
to `1`. A disproportionate division is a partition `X 1 ∪ ⋯ ∪ X n` of `[0,1]` with
`μ i (X i) ≥ α i` for all `i`. `f(n)` is the maximum number of cuts needed, over all measures and
demands.

What is known. Theorem 1.1 of the source: `3n - 4` cuts always suffice. Section 3 of the source
(construction from Segal-Halevi, arXiv 1803.05470): `2n - 2` cuts may be necessary. So
`2n - 2 ≤ f(n) ≤ 3n - 4`, and `f(2) = 2`.

The open statement. The source says: "We suspect that the above construction reflects the truth
and that `f(n) = 2n - 2` for all `n ≥ 2`", and its abstract says that it offers a conjecture that
implies that `2n - 2` cuts suffice in general. `main` below is this claim: `2n - 2` cuts always
suffice. (The lower bound is known, so `main` is equivalent to `f(n) = 2n - 2`.) The same statement
is the conjecture of Segal-Halevi, arXiv 1803.05470. It is open for every `n ≥ 3`.

Relation to Conjecture 3.1 of the source. Conjecture 3.1 is a measure partitioning statement on
the circle: for `n ≥ 2` non-atomic probability measures on `S¹` and demands as above there are a
partition of the agents into two nonempty sets `P`, `Q` and a partition of the circle into two
arcs `X`, `Xᶜ` with `min_{i ∈ P} μ i X = ∑_{j ∈ P} α j` and `min_{i ∈ Q} μ i Xᶜ = ∑_{j ∈ Q} α j`.
The source states that Conjecture 3.1 implies `main` by induction, and that Conjecture 3.1 is open
already for three measures. `main` does not obviously imply Conjecture 3.1, so `main` is the weaker
statement; it is the one that the abstract and both papers single out.

Formalization choices. The measures live on `ℝ` and give mass `1` to `[0,1]`. A division with at
most `k` cuts is given by points `0 = c 0 ≤ c 1 ≤ ⋯ ≤ c (k+1) = 1` (the `k` interior points are
the cuts; equal consecutive points mean that fewer cuts are used) and an owner for each of the
`k + 1` closed intervals `[c j, c (j+1)]`. Agent `i` receives the union of its intervals. The
intervals overlap only in the cut points, which have measure zero because the measures have no
atoms, so this agrees with a partition of `[0,1]` into pieces that are finite unions of intervals.
-/

namespace OMA.S_arxiv_1909_07141

open MeasureTheory

/-- There is a division of the cake `[0,1]` with at most `k` cuts in which every agent `i`
receives a piece of `μ i`-measure at least `α i`. The cut points are `c 1, …, c k`; interval `j`
is `[c j, c (j+1)]` and goes to agent `owner j`. -/
def DivisionWithCuts {n : ℕ} (μ : Fin n → Measure ℝ) (α : Fin n → ℝ) (k : ℕ) : Prop :=
  ∃ (c : Fin (k + 2) → ℝ) (owner : Fin (k + 1) → Fin n),
    Monotone c ∧ c 0 = 0 ∧ c (Fin.last (k + 1)) = 1 ∧
      ∀ i : Fin n, ENNReal.ofReal (α i) ≤
        μ i (⋃ j ∈ {j : Fin (k + 1) | owner j = i}, Set.Icc (c j.castSucc) (c j.succ))

theorem main : ∀ n : ℕ, 2 ≤ n →
    ∀ μ : Fin n → Measure ℝ, (∀ i, IsProbabilityMeasure (μ i)) → (∀ i, NoAtoms (μ i)) →
      (∀ i, μ i (Set.Icc 0 1) = 1) →
    ∀ α : Fin n → ℝ, (∀ i, 0 ≤ α i) → ∑ i, α i = 1 →
      DivisionWithCuts μ α (2 * n - 2) := by
  sorry

end OMA.S_arxiv_1909_07141
