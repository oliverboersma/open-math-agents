import OMAReductions.R_PoincareConjecture_poincare_conjecture_R1
import Mathlib

-- Reduction PoincareConjecture.poincare_conjecture.R1.H3.R1 of step
-- PoincareConjecture.poincare_conjecture.R1.H3
-- Credit: @senamakel

/-!
Separate the Moise route into finite geometric triangulation data and the Cairns smoothing
construction. The two leaves share the same `SimplicialComplex`, purity, edge-link, triangle-link,
Brouwer-star, and carrier-homeomorphism interface used by the public M76 bridge
in FrenzyMath/PoincareConjecture at 62db01af9388dc1d9b56b66d6674f4c09b2318a2.
Links and closed stars are expressed as families of faces, with carriers given
by the union of their convex hulls.
-/

open Set Geometry
open scoped Manifold ContDiff

namespace OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1

def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
    ∃ (n : ℕ),
      let E := EuclideanSpace ℝ (Fin n)
      letI : DecidableEq E := Classical.decEq E
      ∃ (K : SimplicialComplex ℝ E),
        let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
        let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}
        let carrier (faces : Set (Finset E)) := ⋃ t ∈ faces, convexHull ℝ (t : Set E)
        K.faces.Finite ∧
        (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) ∧
        (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) ∧
        (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) ∧
        (∀ p : E, {p} ∈ K.faces →
          ∃ f : E → EuclideanSpace ℝ (Fin 3),
            (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3),
              EqOn f a (convexHull ℝ (s : Set E))) ∧
            InjOn f (carrier (star p)) ∧
            (interior (f '' (carrier (star p)))).Nonempty) ∧
        Nonempty (M ≃ₜ K.space)

def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
    ∀ (n : ℕ),
      let E := EuclideanSpace ℝ (Fin n)
      letI : DecidableEq E := Classical.decEq E
      ∀ (K : SimplicialComplex ℝ E),
        let link (s : Finset E) := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
        let star (p : E) := {t | t ∈ K.faces ∧ {p} ∪ t ∈ K.faces}
        let carrier (faces : Set (Finset E)) := ⋃ t ∈ faces, convexHull ℝ (t : Set E)
        K.faces.Finite →
        (∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4) →
        (∀ t ∈ K.faces, t.card = 2 → IsConnected (carrier (link t))) →
        (∀ t ∈ K.faces, t.card = 3 → ({q : E | {q} ∈ link t} : Set E).ncard = 2) →
        (∀ p : E, {p} ∈ K.faces →
          ∃ f : E → EuclideanSpace ℝ (Fin 3),
            (∀ s ∈ star p, ∃ a : E →ᴬ[ℝ] EuclideanSpace ℝ (Fin 3),
              EqOn f a (convexHull ℝ (s : Set E))) ∧
            InjOn f (carrier (star p)) ∧
            (interior (f '' (carrier (star p)))).Nonempty) →
        Nonempty (M ≃ₜ K.space) →
        ∃ atlas : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
          letI := atlas
          IsManifold (𝓡 3) ∞ M

theorem main : H1 → H2 →
    OMA.R_PoincareConjecture_poincare_conjecture_R1.H3 := by
  intro htri hsmooth M _ _ _ _ _
  obtain ⟨n, K, hfinite, hpure, hedges, htriangles, hbrouwer, e⟩ := htri M
  exact hsmooth M n K hfinite hpure hedges htriangles hbrouwer e

end OMA.R_PoincareConjecture_poincare_conjecture_R1_H3_R1
