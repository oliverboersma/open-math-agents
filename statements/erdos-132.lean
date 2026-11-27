import Mathlib

/-!
# Erdős Problem 132

Source: https://www.erdosproblems.com/132
Credit: @YourFriendPollux

## The problem

Let $A \subset \mathbb{R}^2$ be a set of $n$ points. Must there be two distances which
occur at least once but between at most $n$ pairs of points? Must the number of such
distances $\to \infty$ as $n \to \infty$?

Asked by Erdős and Pach. Hopf and Pannowitz proved that the largest distance between
points of $A$ occurs at most $n$ times, but it is unknown whether a second such distance
must occur. Erdős believed that for $n \ge 5$ there must always exist at least two such
distances; this is false for $n = 4$.

## Formalization notes

* A "distance which occurs between at most $n$ pairs of points" is a real number `d` that
  is realised by at least one pair of distinct points of `A`, and by at most `A.card`
  pairs. The finite set of such distances is `rareDistances A`; the multiplicity of `d`
  is `pairMultiplicity A d`, counting unordered pairs.
* The first question is stated for `n ≥ 5`, the range in which Erdős expected a positive
  answer (the source records that `n = 4` is a counterexample, so the statement for all
  `n` is false).
* The second question is stated as: the minimum, over all `n`-point sets, of the number of
  rare distances tends to infinity (`minRareCount`), which is exactly "the number of such
  distances must tend to infinity as `n → ∞`".
-/

namespace OMA.S_erdos_132

open Filter
open scoped Topology Classical

/-- The number of unordered pairs of distinct points of `A` at distance `d`. -/
noncomputable def pairMultiplicity (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((A.offDiag.filter (fun p => dist p.1 p.2 = d)).card) / 2

/-- The set of distances that occur between at least one and at most `A.card` pairs of
points of `A`. -/
noncomputable def rareDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  (A.offDiag.image (fun p => dist p.1 p.2)).filter
    (fun d => 1 ≤ pairMultiplicity A d ∧ pairMultiplicity A d ≤ A.card)

/-- The least number of rare distances of an `n`-point set: the value whose growth the
second question of the source asks about. -/
noncomputable def minRareCount (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n ∧ (rareDistances A).card = k}

theorem main :
    (∀ A : Finset (EuclideanSpace ℝ (Fin 2)), 5 ≤ A.card → 2 ≤ (rareDistances A).card) ∧
    Tendsto (fun n : ℕ => (minRareCount n : ℝ)) atTop atTop := by
  sorry

end OMA.S_erdos_132
