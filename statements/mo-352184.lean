import Mathlib

/-!
# fair-indexed tournament

Source: https://mathoverflow.net/questions/352184 (question by jcdornano)
Credit: @tatashbar

Question (as stated in the source). Two tournaments `T` and `T'` with vertices `T_1, ..., T_n` and
`T'_1, ..., T'_n` are in the same score-class iff there is a permutation `s` of `{1, ..., n}` such
that for every `i`, `T_i` and `T'_{s(i)}` have the same number of victories. A tournament with
vertices `T_1, ..., T_n` is fair-indexed iff for every `i` in `{1, ..., n}` there exists `j` in
`{i, i+1, ..., n}` such that for every `k > i`, `T_i` beats `T_k` iff `k > j`.
Is there a fair-indexed tournament in any score-class?

`main` states the affirmative: every score-class (of every size `n`) contains a fair-indexed
tournament.

Conventions of this translation:
* A tournament on `n` vertices is a `Digraph (Fin n)` (Mathlib) in which no vertex is adjacent to
  itself and, for distinct `u` and `v`, exactly one of `u → v`, `v → u` holds. `T.Adj u v` is read
  as `u` beats `v`. The vertex `T_i` of the source is `(i - 1 : Fin n)`; only the order of the
  indices matters, and `Fin n` carries the same order as `{1, ..., n}`.
* The number of victories of a vertex is the number of vertices it beats.
* `any score-class` is read as `every score-class`: for every tournament `T` there is a fair-indexed
  tournament `T'` on the same number of vertices in the same score-class as `T`. Every `n` is
  allowed; for `n = 0` and `n = 1` the claim is trivial.
* In the definition of fair-indexed, `j` ranges over `{i, ..., n}`, so `j = i` (the vertex beats
  every later vertex) and `j = n` (it loses to every later vertex) are both allowed.

Status: the question itself proposes no answer. The answers and comments on the source page were
not consulted for this translation (the page could not be fetched automatically; the question
text above is the one recorded by the site). A computer search by the contributor, with a short
argument by hand (not a Lean proof, and not taken from the source page), indicates that the answer
is no: for `n = 16`, no fair-indexed tournament has four vertices with 3 victories and twelve
vertices with 9 victories, although tournaments with these scores exist; every score-class with
`n ≤ 15` contains a fair-indexed tournament. If that is right, the result to prove here is the
negation of `main`.
-/

namespace OMA.S_mo_352184

/-- A tournament: no vertex beats itself, and of two distinct vertices exactly one beats the
other. `T.Adj u v` is read as `u` beats `v`. -/
def IsTournament {n : ℕ} (T : Digraph (Fin n)) : Prop :=
  (∀ v, ¬ T.Adj v v) ∧ (∀ u v, u ≠ v → (T.Adj u v ↔ ¬ T.Adj v u))

/-- The score of a vertex: its number of victories, that is, the number of vertices it beats. -/
noncomputable def score {n : ℕ} (T : Digraph (Fin n)) (i : Fin n) : ℕ :=
  {k : Fin n | T.Adj i k}.ncard

/-- `T` and `T'` are in the same score-class: some permutation `s` of the indices matches every
vertex `T_i` with a vertex `T'_{s(i)}` that has the same number of victories. -/
def SameScoreClass {n : ℕ} (T T' : Digraph (Fin n)) : Prop :=
  ∃ s : Equiv.Perm (Fin n), ∀ i, score T i = score T' (s i)

/-- `T` is fair-indexed: for every `i` there is `j ≥ i` such that, among the later vertices `k > i`,
the vertex `i` beats exactly those with `k > j`. -/
def IsFairIndexed {n : ℕ} (T : Digraph (Fin n)) : Prop :=
  ∀ i : Fin n, ∃ j : Fin n, i ≤ j ∧ ∀ k : Fin n, i < k → (T.Adj i k ↔ j < k)

/-- Every score-class contains a fair-indexed tournament. -/
theorem main : ∀ (n : ℕ) (T : Digraph (Fin n)), IsTournament T →
    ∃ T' : Digraph (Fin n), IsTournament T' ∧ IsFairIndexed T' ∧ SameScoreClass T T' := by
  sorry

end OMA.S_mo_352184
