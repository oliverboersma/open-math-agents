import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1
import Mathlib

/-!
A connected closed surface admits a one-vertex, one-face cellular decomposition.
A primal tree and a disjoint dual tree in a triangulation give this cut graph.
Its bouquet of k circles is the one-point compactification of k disjoint lines.
The face traverses each edge twice. Van Kampen therefore presents the surface
group with k generators and a single even-length relator. Mapping every generator
to the same involution detects positive k, even for nonorientable surfaces.
When k vanishes the cut graph is a single point, so compactifying the open face
recovers the sphere. This argument does not require normalizing the boundary word.
-/

open Set
namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R1

/-- The cut graph and the complementary open face. -/
def H1 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [CompactSpace M] [ConnectedSpace M],
    ∃ (k : ℕ) (K : Set M), IsClosed K ∧ Nonempty (K ≃ₜ OnePoint (Fin k × ℝ)) ∧
      Nonempty (↥(Kᶜ) ≃ₜ EuclideanSpace ℝ (Fin 2))

/-- The van Kampen presentation read from the two sides of each cut edge. -/
def H2 : Prop := ∀ (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [CompactSpace M] [ConnectedSpace M]
    (k : ℕ) (K : Set M), 0 < k → IsClosed K → Nonempty (K ≃ₜ OnePoint (Fin k × ℝ)) →
    Nonempty (↥(Kᶜ) ≃ₜ EuclideanSpace ℝ (Fin 2)) →
    ∃ (p : M) (w : List (Fin k × Bool)), w.length = 2 * k ∧
      Nonempty (FundamentalGroup M p ≃* PresentedGroup ({FreeGroup.mk w} : Set (FreeGroup (Fin k))))

/-- A nonempty collection of generators and an even relator have a nontrivial quotient. -/
def H3 : Prop := ∀ (k : ℕ) (w : List (Fin k × Bool)), 0 < k → w.length = 2 * k →
    ¬ Subsingleton (PresentedGroup ({FreeGroup.mk w} : Set (FreeGroup (Fin k))))

theorem main : H1 → H2 → H3 → OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1.H4 := by
  intro graph presentation parity M _ _ _ _ _
  obtain ⟨k,K,hK,⟨e⟩,⟨face⟩⟩ := graph M
  have hk : k = 0 := by
    by_contra hn
    have hpos : 0 < k := Nat.pos_of_ne_zero hn
    obtain ⟨p,w,hw,⟨g⟩⟩ := presentation M k K hpos hK ⟨e⟩ ⟨face⟩
    exact parity k w hpos hw ⟨fun a b => g.symm.injective (Subsingleton.elim _ _)⟩
  subst k
  let p : K := e.symm OnePoint.infty
  have hsingle (y : K) : y = p := by
    apply e.injective
    change e y = e (e.symm OnePoint.infty)
    rw [e.apply_symm_apply]
    induction e y using OnePoint.rec with
    | infty => rfl
    | coe z => exact Fin.elim0 z.1
  have hset : K = {p.val} := by
    ext y
    constructor
    · intro hy
      exact congrArg Subtype.val (hsingle ⟨y,hy⟩)
    · rintro rfl
      exact p.property
  have er : Nonempty (↥(({p.val} : Set M)ᶜ) ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
    rw [← hset]
    exact ⟨face⟩
  obtain ⟨t⟩ := er
  let P := (({p.val} : Set M)ᶜ)
  let c := OnePoint.equivOfIsEmbeddingOfRangeEq p.val (Subtype.val : P → M)
    Topology.IsEmbedding.subtypeVal Subtype.range_val
  exact ⟨c.symm.trans (t.onePointCongr.trans (onePointEquivSphereOfFinrankEq (by simp)))⟩

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_two_R1_H4_R1
