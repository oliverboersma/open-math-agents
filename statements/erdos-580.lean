import Mathlib

/-!
# Erdős Problem 580

Source: https://www.erdosproblems.com/580
Credit: @timlantin

Let $G$ be a graph on $n$ vertices such that at least $n/2$ vertices have degree at least $n/2$.
Must $G$ contain every tree on at most $n/2$ vertices?

A conjecture of Erdős, Füredi, Loebl, and Sós [EFLS95], the $(n/2$-$n/2$-$n/2)$ case of the
Loebl–Komlós–Sós conjecture. Ajtai, Komlós, and Szemerédi [AKS95] proved an asymptotic version,
and Zhao [Zh11] proved it for all sufficiently large $n$; it is open for small $n$ in general.

Formalization notes:
* The halves are read in `ℚ`, so for odd $n$ the conditions are $\geq n/2$ (that is,
  $\geq \lceil n/2 \rceil$) and the trees have at most $\lfloor n/2 \rfloor$ vertices.
* The degree of `v` is `(G.neighborSet v).ncard`, which avoids decidability instances.
* Containment is as a (not necessarily induced) subgraph, `SimpleGraph.IsContained`.
* We follow the source in bounding the number of vertices of the tree. The usual statement in
  the literature (e.g. [Zh11]) bounds the number of edges by $n/2$, which is slightly stronger;
  that version implies this one.
-/

namespace OMA.S_erdos_580

/-- The number of vertices of `G` whose degree is at least `n / 2`. -/
noncomputable def numHighDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  {v : Fin n | ((n : ℚ) / 2) ≤ ((G.neighborSet v).ncard : ℚ)}.ncard

/-- If at least `n / 2` vertices of a graph `G` on `n` vertices have degree at least `n / 2`,
then `G` contains every tree with at most `n / 2` vertices. -/
theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ((n : ℚ) / 2) ≤ (numHighDegree G : ℚ) →
    ∀ (m : ℕ), (m : ℚ) ≤ (n : ℚ) / 2 →
    ∀ (T : SimpleGraph (Fin m)), T.IsTree → T.IsContained G := by
  sorry

end OMA.S_erdos_580
