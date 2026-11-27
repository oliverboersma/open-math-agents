import Mathlib

/-!
# Erdős Problem 634

Source: https://www.erdosproblems.com/634
Credit: @adammcarter

Problem (erdosproblems.com/634): find all n such that there is at least one triangle which
can be cut into n congruent triangles. Squares work; Soifer showed 2n^2, 3n^2, 6n^2 and n^2+m^2
work; Beeson showed 7 and 11 do not. The source adds that it is possible that any prime of the
form 4n+3 does not have this property, and that it is not known whether 19 has it.

Encoding. The full classification asked for by find all n is open and the source states no
conjectured answer set, so it cannot be stated faithfully with a single answer placeholder.
Instead, main states the possibility the source itself raises (It is possible that any prime
of the form 4n+3 does not have this property): no prime p of the form 4n+3 has the property.
This is one sub-question of Problem 634, not the full classification. The prime 3 is excluded
(hypothesis 3 < p) because the source itself lists 3n^2 with n = 1 among the achievable values
(an equilateral triangle splits into 3 congruent triangles about its centre). Beeson and Roşu,
arXiv 2607.23453 (Theorem 42 and Corollary 43; a preprint with a Lean formalization), claim
this statement. The definitions below are intended to capture the notion exactly.

Conventions (as in the literature, e.g. Beeson and Roşu, Section 1, and as in
FormalConjectures/ErdosProblems/633.lean, whose IsCuttable is mirrored verbatim in meaning):
* the tiles are closed triangles, all congruent to one another, with pairwise disjoint
  interiors, whose union is exactly the given (closed) triangle;
* Congruent on vertex families means an isometry matching labelled vertices; since the family
  of tiles is existential, this is congruence up to relabelling vertices, and mirror images are
  allowed (any isometry of the plane, orientation reversing ones included);
* tilings need not be edge to edge;
* Affine.Triangle is a non-degenerate triangle (affinely independent vertices);
* Affine.Simplex.interior and Affine.Simplex.closedInterior are the Mathlib definitions
  (open and closed convex hull of the vertices, via barycentric weights in (0,1) resp. [0,1]);
* the plane is EuclideanSpace ℝ (Fin 2) (written as a notation in FormalConjectures).
-/

open scoped Congruent

namespace OMA.S_erdos_634

/-- A triangle `T` in the plane is `n`-cuttable if it can be decomposed into `n` pairwise
congruent triangles with pairwise disjoint interiors whose closed hulls cover `T` exactly.
Same as `Erdos633.IsCuttable` in FormalConjectures. -/
def IsCuttable (n : ℕ) (T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ Ts : Fin n → Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)),
    (∀ i j, (Ts i).points ≅ (Ts j).points) ∧
      Pairwise (fun i j ↦ Disjoint (Ts i).interior (Ts j).interior) ∧
      ⋃ i, (Ts i).closedInterior = T.closedInterior

/-- `n` has the property of Erdős Problem 634: some triangle in the plane can be cut into `n`
congruent triangles. -/
def HasCongruentTriangleCut (n : ℕ) : Prop :=
  ∃ T : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)), IsCuttable n T

/-- No prime `p ≡ 3 (mod 4)` with `p > 3` has the property (the possibility raised in the
source; `p = 3` is excluded since `3 = 3 * 1 ^ 2` is achievable). -/
theorem main : ∀ p : ℕ, p.Prime → p % 4 = 3 → 3 < p → ¬ HasCongruentTriangleCut p := by sorry

end OMA.S_erdos_634
