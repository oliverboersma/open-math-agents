import FormalConjectures.ErdosProblems.«827»

/-!
# Erdős 827: five points with distinct circumradii

Martínez and Roldán-Pensado, “Points defining triangles with distinct
circumradii” (2015), Theorem 1.2, state the bound 37. The counting argument
in §3 of arXiv:1402.6276 counts pairs of equal-radius triangles sharing one
vertex. A pair can also share an edge; its union then leaves the fifth
point undetermined.

The first step records the fixed-chord geometry. The second is a finite
color-counting statement addressing both kinds of overlap. The remaining
geometric case is a point incident with thirteen distinct triangles of a
single circumradius. -/
namespace OMA.R_Erdos827_erdos_827_variants_n_five_le_R1
open Finset EuclideanGeometry Erdos827
open scoped Classical

/-- Triangle circumradii are well defined; at most two third vertices
complete a fixed chord to a triangle of any specified radius. -/
def H1 : Prop := ∀ X : Finset ℝ², InGeneralPosition (X:Set ℝ²) →
  ∃ c : Finset ℝ²→ℝ,
    (∀ T⊆X,T.card=3 → ∀ r, c T=r ↔ OnCircleOfRadius T r) ∧
    ∀ B⊆X,B.card=2 → ∀ r, ((X\B).filter (fun z => c (insert z B)=r)).card≤2

/-- A triple coloring with at most two completions per fixed pair and at most
twelve equal-colored triangles at any one vertex has five rainbow vertices. -/
def H2 : Prop := ∀ (X : Finset ℝ²) (c : Finset ℝ²→ℝ), X.card=37 →
  (∀ B⊆X,B.card=2 → ∀ r, ((X\B).filter (fun z => c (insert z B)=r)).card≤2) →
  (∀ a∈X,∀ r,(((X.erase a).powersetCard 2).filter (fun B => c (insert a B)=r)).card≤12) →
  ∃ Y⊆X, Y.card=5 ∧ Set.InjOn c (Y.powersetCard 3 : Set (Finset ℝ²))

/-- The geometric dense case: thirteen triangles of the same radius have a
common vertex. A rainbow five-set may use any of the 37 vertices. -/
def H3 : Prop := ∀ (X : Finset ℝ²), X.card=37 → InGeneralPosition (X:Set ℝ²) →
  ∀ a∈X,∀ r,13≤(((X.erase a).powersetCard 2).filter
    (fun B => OnCircleOfRadius (insert a B) r)).card →
  ∃ Y⊆X,Y.card=5 ∧ HasDistinctCircumradii Y

theorem main : H1 → H2 → H3 → type_of% @Erdos827.erdos_827.variants.n_five_le := by
  intro geometry rainbow dense
  apply n_le
  intro X size general
  obtain ⟨c,track,cap⟩ := geometry X general
  by_cases thin : ∀ a∈X,∀ r,
      (((X.erase a).powersetCard 2).filter (fun B => c (insert a B)=r)).card≤12
  · obtain ⟨Y,yx,sy,injective⟩ := rainbow X c size cap thin
    refine ⟨Y,yx,sy,?_⟩
    intro T ty U uy st su ne r hr hs
    apply ne
    exact injective (mem_powersetCard.mpr ⟨ty,st⟩) (mem_powersetCard.mpr ⟨uy,su⟩)
      (((track T (Subset.trans ty yx) st r).mpr hr).trans
        ((track U (Subset.trans uy yx) su r).mpr hs).symm)
  · push Not at thin
    obtain ⟨a,ax,r,many⟩ := thin
    apply dense X size general a ax r
    apply many.trans_le (card_le_card ?_)
    intro B hb
    obtain ⟨be,eq⟩ := mem_filter.mp hb
    obtain ⟨sub,sb⟩ := mem_powersetCard.mp be
    have bx : insert a B⊆X := insert_subset ax (Subset.trans sub (erase_subset ..))
    have ab : a∉B := fun mem => notMem_erase a X (sub mem)
    exact mem_filter.mpr ⟨be,(track _ bx (by rw [card_insert_of_notMem ab,sb]) r).mp eq⟩

end OMA.R_Erdos827_erdos_827_variants_n_five_le_R1
