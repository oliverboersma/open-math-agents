import FormalConjectures.Millennium.Poincare
import Mathlib

/-!
Recognize a high-dimensional homotopy sphere by puncturing it. A manifold chart
around the deleted point gives punctured balls outside arbitrary compact sets,
with compact complement. Open-manifold recognition then identifies the puncture
with Euclidean space. Its one-point compactification is the original sphere.
-/

namespace OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2

open Set Metric Topology ContinuousMap
open scoped ContinuousMap Manifold

/-- Compactness from the nonvanishing top homology of a homotopy sphere. -/
def H1 : Prop := ∀ n : ℕ, 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
  (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) → CompactSpace M

/-- Deleting a point from a closed homotopy sphere can give a contractible
manifold. This is a homotopy statement about an open manifold. -/
def H2 : Prop := ∀ n : ℕ, 5 ≤ n → ∀ (M : Type) [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M],
  (M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) →
  ∃ p : M, ContractibleSpace ↥(({p} : Set M)ᶜ)

/-- Euclidean recognition for a contractible open manifold with punctured-ball
neighbourhoods at infinity. These neighbourhoods are simply connected for n ≥ 3. -/
def H3 : Prop := ∀ n : ℕ, 5 ≤ n → ∀ (X : Type) [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [ContractibleSpace X],
  (∀ K : Set X, IsCompact K → ∃ U : Set X, IsOpen U ∧ IsCompact Uᶜ ∧ Disjoint K U ∧
    ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r ∧ Nonempty (U ≃ₜ ↥(ball c r \ {c}))) →
  Nonempty (X ≃ₜ EuclideanSpace ℝ (Fin n))

theorem punctured_chart_end {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] (p : M)
    (K : Set ↥(({p} : Set M)ᶜ)) (hK : IsCompact K) :
    ∃ U : Set ↥(({p} : Set M)ᶜ), IsOpen U ∧ IsCompact Uᶜ ∧ Disjoint K U ∧
      ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r ∧ Nonempty (U ≃ₜ ↥(ball c r \ {c})) := by
  classical
  let P := ↥(({p} : Set M)ᶜ)
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  let F : Set M := (Subtype.val : P → M) '' K
  have hc : IsCompact F := hK.image continuous_subtype_val
  have hpF : p ∉ F := by
    rintro ⟨x,hx,hxp⟩
    exact x.property (Set.mem_singleton_iff.mpr hxp)
  have hps : p ∈ e.source := mem_chart_source _ _
  have hop := e.isOpen_inter_preimage_symm hc.isClosed.isOpen_compl
  have hm : e p ∈ e.target ∩ e.symm ⁻¹' Fᶜ := ⟨e.map_source hps,by simpa [e.left_inv hps] using hpF⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hop (e p) hm
  let W := e.source ∩ e ⁻¹' ball (e p) r
  let U := (Subtype.val : P → M) ⁻¹' W
  have hW : IsOpen W := e.isOpen_inter_preimage Metric.isOpen_ball
  have hpW : p ∈ W := ⟨hps,Metric.mem_ball_self hr⟩
  refine ⟨U,hW.preimage continuous_subtype_val,?_,?_,e p,r,hr,?_⟩
  · apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have heq : (Subtype.val : P → M) '' Uᶜ = Wᶜ := by
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact hx
      · intro hy
        have hne : y ≠ p := fun h => hy (h.symm ▸ hpW)
        exact ⟨⟨y,hne⟩,hy,rfl⟩
    rw [heq]
    exact hW.isClosed_compl.isCompact
  · apply Set.disjoint_left.mpr
    intro x hxK hxU
    have hx : (x:M) ∈ W := hxU
    have hout := (hball hx.2).2
    exact (show e.symm (e x) ∉ F from hout) (by rw [e.left_inv hx.1]; exact ⟨x,hxK,rfl⟩)
  · let V := ball (e p) r \ {e p}
    have fu (x : U) : e x.val.val ∈ V := by
      have hx : x.val.val ∈ W := x.property
      refine ⟨hx.2,?_⟩
      intro he
      have hpEq := e.injOn hx.1 hps (Set.mem_singleton_iff.mp he)
      exact x.val.property (Set.mem_singleton_iff.mpr hpEq)
    have bv (y : V) : e.symm y.val ≠ p := by
      intro he
      have htar := (hball y.property.1).1
      apply y.property.2
      exact Set.mem_singleton_iff.mpr ((e.right_inv htar).symm.trans (congrArg e he))
    have bu (y : V) : (⟨e.symm y.val,bv y⟩ : P) ∈ U := by
      have htar := (hball y.property.1).1
      refine ⟨e.map_target htar,?_⟩
      change e (e.symm y.val) ∈ ball (e p) r
      rw [e.right_inv htar]
      exact y.property.1
    refine ⟨{ toFun := fun x => ⟨e x.val.val,fu x⟩
              invFun := fun y => ⟨⟨e.symm y.val,bv y⟩,bu y⟩
              left_inv := fun x => Subtype.ext (Subtype.ext (e.left_inv (show x.val.val ∈ W from x.property).1))
              right_inv := fun y => Subtype.ext (e.right_inv (hball y.property.1).1)
              continuous_toFun := ?_
              continuous_invFun := ?_ }⟩
    · exact (e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
        fun x => (show x.val.val ∈ W from x.property).1).subtype_mk _
    · exact ((e.continuousOn_symm.comp_continuous continuous_subtype_val
        fun y => (hball y.property.1).1).subtype_mk _).subtype_mk _

theorem main : H1 → H2 → H3 → type_of% @PoincareConjecture.poincare_conjecture.variants.dimension_ge_five := by
  intro hcompact hpuncture hrecognize n hn M _ _ _ e
  have : CompactSpace M := hcompact n hn M e
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨p,hcontr⟩ := hpuncture n hn M e
  let U : TopologicalSpace.Opens M := ⟨({p} : Set M)ᶜ,isClosed_singleton.isOpen_compl⟩
  have : ContractibleSpace U := hcontr
  obtain ⟨h⟩ := hrecognize n hn U (fun K hK => punctured_chart_end p K hK)
  let eM := OnePoint.equivOfIsEmbeddingOfRangeEq p (Subtype.val : U → M)
    Topology.IsEmbedding.subtypeVal (by exact Subtype.range_coe)
  let eS : OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  exact ⟨eM.symm.trans (h.onePointCongr.trans eS)⟩

end OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R2
