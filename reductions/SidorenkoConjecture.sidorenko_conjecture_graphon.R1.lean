import FormalConjectures.Wikipedia.SidorenkoConjecture

/-!
# From a finite Sidorenko counterexample to a graphon counterexample

H1 is the finite counterexample theorem proved in OpenAI's 2026 paper.
H2 realizes a finite host on the unit interval while preserving both
densities for every finite test graph. Applying the proposed graphon
inequality to this realization would give the refuted finite inequality.

Source for H1: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/RandomHost.lean
Reduction and density transfer by @Deldor14.
-/

namespace OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1
open SimpleGraph LimitObjects

/-- The finite counterexample theorem of the cited paper. -/
def H1 : Prop := ¬ ∀ {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    [Nonempty W] (H : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel G.Adj], H.IsBipartite →
    homDensity (completeGraph (Fin 2)) G ^ H.edgeFinset.card ≤ homDensity H G

/-- Realization of every nonempty finite host, with both densities preserved. -/
def H2 : Prop := ∀ {V W : Type} [Fintype V] [Fintype W] [Nonempty W]
  [DecidableEq V] [DecidableEq W] (H : SimpleGraph V) [DecidableRel H.Adj]
  (G : SimpleGraph W) [DecidableRel G.Adj], ∃ S : Graphon,
    graphonEdgeDensity S = homDensity (completeGraph (Fin 2)) G ∧
    graphonHomDensity H S = homDensity H G

open MeasureTheory Filter
universe u

/-- Change of coordinates for graphon densities. Adapted to arbitrary finite vertex
universes from @TheWaler's proof of the tree case in Left to Solve. -/
private lemma graphonHomDensity_congr_iso {V : Type*} [Fintype V] [DecidableEq V]
    {T : Type*} [Fintype T] [DecidableEq T] (H : SimpleGraph V) [DecidableRel H.Adj]
    (H' : SimpleGraph T) [DecidableRel H'.Adj]
    (iso : H ≃g H') (W : Graphon) :
    H'.edgeFinset.card = H.edgeFinset.card ∧ graphonHomDensity H' W = graphonHomDensity H W := by
  let e : V ≃ T := iso.toEquiv
  have hedges : H'.edgeFinset = H.edgeFinset.image (Sym2.map e) := by
    ext s
    induction s using Sym2.ind with
    | _ a b =>
      simp only [mem_edgeFinset, mem_edgeSet, Finset.mem_image]
      constructor
      · intro hab
        refine ⟨s(e.symm a, e.symm b), ?_, by simp⟩
        have hrel : H'.Adj (iso (e.symm a)) (iso (e.symm b)) := by
          rw [show iso (e.symm a) = a from iso.apply_symm_apply a,
            show iso (e.symm b) = b from iso.apply_symm_apply b]
          exact hab
        exact (iso.map_rel_iff).mp hrel
      · rintro ⟨s', hs', hmap⟩
        induction s' using Sym2.ind with
        | _ u v =>
          simp only [Sym2.map_mk, Sym2.eq_iff] at hmap
          rcases hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact (iso.map_rel_iff).mpr hs'
          · exact ((iso.map_rel_iff).mpr hs').symm
  have hcard : H'.edgeFinset.card = H.edgeFinset.card := by
    rw [hedges, Finset.card_image_of_injective _ (Sym2.map.injective e.injective)]
  refine ⟨hcard, ?_⟩
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : T => LimitObjects.UnitInterval) e)
      (Measure.pi fun _ : V => (volume : Measure LimitObjects.UnitInterval)) (Measure.pi fun _ : T => (volume : Measure LimitObjects.UnitInterval)) :=
    measurePreserving_piCongrLeft (fun _ : T => (volume : Measure LimitObjects.UnitInterval)) e
  have hFmeas : Measurable (fun x : T → LimitObjects.UnitInterval => graphonHomIntegrand H' W x) :=
    Finset.measurable_prod H'.edgeFinset fun s _ => by
      induction s using Sym2.ind with
      | _ a b =>
        exact measurable_subtype_coe.comp (W.measurable.comp
          ((measurable_pi_apply a).prodMk (measurable_pi_apply b)))
  have hint_eq : ∀ x : V → LimitObjects.UnitInterval,
      graphonHomIntegrand H' W (MeasurableEquiv.piCongrLeft (fun _ : T => LimitObjects.UnitInterval) e x) =
        graphonHomIntegrand H W x := by
    intro x
    unfold graphonHomIntegrand
    rw [hedges, Finset.prod_image (fun _ _ _ _ h => Sym2.map.injective e.injective h)]
    refine Finset.prod_congr rfl fun s _ => ?_
    induction s using Sym2.ind with
    | _ u v =>
      simp [Graphon.evalEdge, MeasurableEquiv.piCongrLeft]
  unfold graphonHomDensity
  change ∫ x, graphonHomIntegrand H' W x ∂(Measure.pi fun _ : T => (volume : Measure LimitObjects.UnitInterval)) =
    ∫ x, graphonHomIntegrand H W x ∂(Measure.pi fun _ : V => (volume : Measure LimitObjects.UnitInterval))
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
    (by rw [hmp.map_eq]; exact hFmeas.aestronglyMeasurable)]
  exact integral_congr_ae (Filter.Eventually.of_forall hint_eq)

private lemma small_inequality
    (allGraphons : ∀ {T : Type u} [Fintype T] [DecidableEq T] (J : SimpleGraph T)
      [DecidableRel J.Adj], J.IsBipartite → ∀ S : Graphon,
      graphonEdgeDensity S ^ J.edgeFinset.card ≤ graphonHomDensity J S)
    {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (bip : H.IsBipartite) (S : Graphon) :
    graphonEdgeDensity S ^ H.edgeFinset.card ≤ graphonHomDensity H S := by
  classical
  let e : V ≃ ULift.{u} V := Equiv.ulift.symm
  let J := H.comap e.symm
  let iso : H ≃g J := { toEquiv := e, map_rel_iff' := by intro x y; simp [J] }
  have bipJ : J.IsBipartite := SimpleGraph.Colorable.of_hom iso.symm.toHom bip
  obtain ⟨edges,density⟩ := graphonHomDensity_congr_iso H J iso S
  rw [← edges, ← density]
  exact allGraphons J bipJ S

theorem main : H1 → H2 → type_of% @SidorenkoConjecture.sidorenko_conjecture_graphon := by
  intro counterexample realization allGraphons
  apply counterexample
  intro V W _ _ _ _ _ H G _ _ bip
  obtain ⟨S,edge,hom⟩ := realization H G
  rw [← edge, ← hom]
  exact small_inequality @allGraphons H bip S

end OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1
