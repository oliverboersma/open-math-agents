import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1_H3_R1
import Mathlib

/-!
Re-embed a finite Brouwer triangulation using independent vertices, then
construct transverse affine leaf coordinates on its carrier. The normalized
projections share a kernel, which determines smooth chart transitions.
The finite complex assumptions follow @senamakel, merged PR 4604.
The leaf coordinate interface is adapted from the PoincareLib contributors,
LehengChen/PoincareConjecture at 60de1a94ca7038d04ed123b490a3229f8aa5fa75,
via frenzymath/Poincare-Conjecture at 432c38f2aa5a30efb13871292d17b4a3309a496a
and frenzymath/PoincareConjecture at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
Copyright (c) 2026 The PoincareLib contributors. Licensed under Apache-2.0.
See Cairns 1940, sections 7 to 9, and PoincareLib's FiniteTriangulationBridge
and LeafProjectionAtlas.
-/

open Set Geometry
open scoped Manifold ContDiff
namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1

/-- Re-embed while preserving the closed links and piecewise affine vertex-star data. -/
def H1 : Prop :=
  let Good (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))) : Prop :=
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}
    let carrier (F : Set (Finset E)) := ⋃ t ∈ F, convexHull ℝ (t : Set E)
    K.faces.Finite ∧ (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) ∧
    (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) ∧
    (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) ∧
    (∀ p : E, {p} ∈ K.faces → ∃ f : E → EuclideanSpace ℝ (Fin 3),
      (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3), EqOn f a (convexHull ℝ (s : Set E))) ∧
      InjOn f (carrier (star p)) ∧ (interior (f '' carrier (star p))).Nonempty)
  ∀ (n : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n))), Good n K →
    ∃ (m : ℕ) (L : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
      AffineIndependent ℝ ((↑) : L.vertices → EuclideanSpace ℝ (Fin m)) ∧
      Good m L ∧ Nonempty (K.space ≃ₜ L.space)

/-- Cairns' construction of local smooth leaf coordinates for an independent triangulation. -/
def H2 : Prop :=
  let Good (m : ℕ) (K : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))) : Prop :=
    let E := EuclideanSpace ℝ (Fin m)
    letI : DecidableEq E := Classical.decEq E
    let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
    let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}
    let carrier (F : Set (Finset E)) := ⋃ t ∈ F, convexHull ℝ (t : Set E)
    K.faces.Finite ∧ (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) ∧
    (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) ∧
    (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) ∧
    (∀ p : E, {p} ∈ K.faces → ∃ f : E → EuclideanSpace ℝ (Fin 3),
      (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3), EqOn f a (convexHull ℝ (s : Set E))) ∧
      InjOn f (carrier (star p)) ∧ (interior (f '' carrier (star p))).Nonempty)
  ∀ (m : ℕ) (L : SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))),
    AffineIndependent ℝ ((↑) : L.vertices → EuclideanSpace ℝ (Fin m)) → Good m L →
    let E := EuclideanSpace ℝ (Fin m)
    let V := EuclideanSpace ℝ (Fin 3)
    ∀ (M : Type) [TopologicalSpace M] (e : M ≃ₜ L.space),
    let v := fun y : M => (e y : E)
    ∃ (c : M → OpenPartialHomeomorph M V) (P : M → Submodule ℝ E)
      (b : M → V →ᴬ[ℝ] E) (Q : M → E → E →L[ℝ] V),
    (∀ y : M, ∃ i, y ∈ (c i).source) ∧
    (∀ i z, z ∈ (c i).target → ContDiffAt ℝ ∞ (Q i) (b i z)) ∧
    (∀ i y, y ∈ (c i).source → Function.RightInverse (b i).contLinear (Q i (v y)) ∧
      (Q i (v y)).ker = P y ∧ Q i (b i (c i y)) = Q i (v y) ∧ b i (c i y) - v y ∈ P y)

/-- Regularity and overlap compatibility of the normalized leaf projections give a smooth atlas. -/
def H3 : Prop :=
  ∀ (m : ℕ) (M : Type) [TopologicalSpace M],
    let E := EuclideanSpace ℝ (Fin m)
    let V := EuclideanSpace ℝ (Fin 3)
    ∀ (c : M → OpenPartialHomeomorph M V) (v : M → E) (P : M → Submodule ℝ E)
      (b : M → V →ᴬ[ℝ] E) (Q : M → E → E →L[ℝ] V),
    ((∀ y : M, ∃ i, y ∈ (c i).source) ∧
    (∀ i z, z ∈ (c i).target → ContDiffAt ℝ ∞ (Q i) (b i z)) ∧
    (∀ i y, y ∈ (c i).source → Function.RightInverse (b i).contLinear (Q i (v y)) ∧
      (Q i (v y)).ker = P y ∧ Q i (b i (c i y)) = Q i (v y) ∧ b i (c i y) - v y ∈ P y)) →
    ∃ atlas : ChartedSpace V M, letI := atlas; IsManifold (𝓡 3) ∞ M

theorem main : H1 → H2 → H3 → OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1.H2 := by
  intro independent coords smooth M _ _ _ _ _ n
  try dsimp only
  intro K
  try dsimp only
  intro hfin hp he ht hv ⟨e⟩
  obtain ⟨m,L,hind,hL,⟨a⟩⟩ := independent n K ⟨hfin,hp,he,ht,hv⟩
  obtain ⟨c,P,b,Q,hh⟩ := coords m L hind hL M (e.trans a)
  exact smooth m M c _ P b Q hh

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1_H2_R1

