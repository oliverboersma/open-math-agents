import OMAReductions.R_PoincareConjecture_poincare_conjecture_R2
import Mathlib.Topology.LocalAtTarget

/-!
Reduce the spherical covering statement to the existence of finite universal
covers and the compact simply connected form of the Poincaré theorem.
-/

open Set TopologicalSpace Topology

namespace OMA.R_PoincareConjecture_poincare_conjecture_R2_H2_R1

private theorem compact_of_finite_cover {E M : Type} [TopologicalSpace E]
    [TopologicalSpace M] [CompactSpace M] {p : E → M} (hp : IsCoveringMap p)
    (finiteFiber : ∀ x : M, Finite (p ⁻¹' {x})) : CompactSpace E := by
  choose U hmem hopen _ e he using fun x => (hp x).2
  let V : M → Opens M := fun x => ⟨U x, hopen x⟩
  have hV : IsOpenCover V := by
    change iSup V = ⊤
    refine le_antisymm le_top ?_
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hmem x⟩
  have hclosed : IsClosedMap p := (hV.isClosedMap_iff_restrictPreimage).2 fun x => by
    let : Finite (p ⁻¹' {x}) := finiteFiber x
    have hfst : IsClosedMap (Prod.fst : U x × (p ⁻¹' {x}) → U x) :=
      isProperMap_fst_of_compactSpace.isClosedMap
    have heq : (V x).1.restrictPreimage p = Prod.fst ∘ e x := by
      funext y
      exact Subtype.ext (he x y).symm
    rw [heq]
    exact hfst.comp (e x).isClosedMap
  have hproper : IsProperMap p :=
    isProperMap_iff_isClosedMap_and_compact_fibers.mpr
      ⟨hp.continuous, hclosed, fun x => by
        let : Finite (p ⁻¹' {x}) := finiteFiber x
        exact isCompact_iff_compactSpace.mpr inferInstance⟩
  exact ⟨by simpa using hproper.isCompact_preimage (K := univ) isCompact_univ⟩

private theorem hausdorff_of_cover {E M : Type} [TopologicalSpace E]
    [TopologicalSpace M] [T2Space M] {p : E → M} (hp : IsCoveringMap p) : T2Space E := by
  refine ⟨fun x y hxy => ?_⟩
  by_cases heq : p x = p y
  · exact hp.isSeparatedMap x y heq hxy
  · obtain ⟨U, V, hU, hV, hx, hy, hd⟩ := t2_separation heq
    exact ⟨p ⁻¹' U, p ⁻¹' V, hU.preimage hp.continuous, hV.preimage hp.continuous,
      hx, hy, hd.preimage p⟩

/-- The universal covering construction, with finite fibers when the base has finite π₁. -/
def H1 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
    (∀ x : M, Finite (FundamentalGroup M x)) →
    ∃ (E : Type) (t : TopologicalSpace E), letI := t
      SimplyConnectedSpace E ∧
        ∃ p : E → M, IsCoveringMap p ∧ ∀ x : M, Finite (p ⁻¹' {x})

/-- The compact simply connected topological Poincaré theorem. -/
def H2 : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [SimplyConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M],
    Nonempty (M ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

theorem main : H1 → H2 → OMA.R_PoincareConjecture_poincare_conjecture_R2.H2 := by
  intro universal poincare M _ _ _ _ _ finitePi
  obtain ⟨E, topology, conn, p, hp, finiteFiber⟩ := universal M finitePi
  let : TopologicalSpace E := topology
  let : SimplyConnectedSpace E := conn
  let : CompactSpace E := compact_of_finite_cover hp finiteFiber
  let : T2Space E := hausdorff_of_cover hp
  let q := hp.isLocalHomeomorph
  let model := EuclideanSpace ℝ (Fin 3)
  let chart : E → OpenPartialHomeomorph E model := fun x =>
    (q.localInverseAt x).symm.trans (chartAt model (p x))
  let : ChartedSpace model E :=
    { atlas := range chart
      chartAt := chart
      mem_chart_source := fun x => by
        change x ∈ ((q.localInverseAt x).symm.trans (chartAt model (p x))).source
        rw [OpenPartialHomeomorph.trans_source]
        exact ⟨q.self_mem_localInverseAt_target, by simp [mem_chart_source]⟩
      chart_mem_atlas := fun x => ⟨x, rfl⟩ }
  obtain ⟨homeo⟩ := poincare E
  exact ⟨p ∘ homeo.symm, hp.comp_homeomorph homeo.symm⟩

end OMA.R_PoincareConjecture_poincare_conjecture_R2_H2_R1
