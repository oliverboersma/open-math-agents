import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1
import Mathlib

/-! Equal-volume bins on the unit interval induce uniform counting measure. -/

open MeasureTheory MeasureTheory.Measure Set LimitObjects Filter
open scoped unitInterval ENNReal

namespace StepGraphonProof

private noncomputable def endpoint (m i : ℕ) (hm : 0 < m) (hi : i ≤ m) : I :=
  ⟨(i : ℝ) / m, div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _),
    (div_le_one (by exact_mod_cast hm)).mpr (by exact_mod_cast hi)⟩

private noncomputable def bin (m : ℕ) (hm : 0 < m) (x : I) : Fin m :=
  ⟨⌊(m : ℝ) * (x : ℝ)⌋₊ % m, Nat.mod_lt _ hm⟩

private theorem measurable_bin (m : ℕ) (hm : 0 < m) : Measurable (bin m hm) := by
  unfold bin
  let g (k : ℕ) : Fin m := ⟨k % m, Nat.mod_lt _ hm⟩
  exact (measurable_of_countable g).comp
    (Nat.measurable_floor.comp (measurable_const.mul measurable_subtype_coe))

private theorem bin_volume (m : ℕ) (hm : 0 < m) (i : Fin m) :
    volume ((bin m hm) ⁻¹' {i}) = ENNReal.ofReal (1 / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  let l := endpoint m i hm i.isLt.le
  let r := endpoint m (i.val+1) hm (Nat.succ_le_of_lt i.isLt)
  have ha : (bin m hm ⁻¹' {i}) =ᵐ[volume] Ico l r := by
    filter_upwards [(countable_singleton (1 : I)).ae_notMem (volume : Measure I)] with x hx
    have hx1 : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 (fun h => hx (Subtype.ext h))
    have hx0 : 0 ≤ (m : ℝ) * (x : ℝ) := mul_nonneg hmR.le x.property.1
    have hf : ⌊(m : ℝ) * (x : ℝ)⌋₊ < m :=
      (Nat.floor_lt hx0).mpr (by simpa using mul_lt_mul_of_pos_left hx1 hmR)
    apply propext
    change bin m hm x = i ↔ (i : ℝ) / m ≤ (x : ℝ) ∧ (x : ℝ) < (↑(i.val+1) : ℝ)/m
    rw [Fin.ext_iff]
    change (⌊(m : ℝ) * (x : ℝ)⌋₊ % m : ℕ) = i.val ↔ _
    rw [Nat.mod_eq_of_lt hf, Nat.floor_eq_iff hx0, div_le_iff₀ hmR, lt_div_iff₀ hmR]
    simp [Nat.cast_add, mul_comm]
  rw [measure_congr ha, unitInterval.volume_Ico]
  congr 1
  change ((i.val+1 : ℕ) : ℝ) / m - (i.val : ℝ) / m = 1/m
  push_cast
  ring

private noncomputable def finiteLabel (W : Type) [Fintype W] [Nonempty W] (x : I) : W :=
  (Fintype.equivFin W).symm (bin (Fintype.card W) Fintype.card_pos x)

private noncomputable def uniform (W : Type) [Fintype W] [MeasurableSpace W] : Measure W :=
  ENNReal.ofReal (1 / (Fintype.card W : ℝ)) • Measure.count

private theorem label_preserving (W : Type) [Fintype W] [Nonempty W] [MeasurableSpace W]
    [MeasurableSingletonClass W] : MeasurePreserving (finiteLabel W) volume (uniform W) := by
  classical
  have hmeas : Measurable (finiteLabel W) :=
    (measurable_of_countable (Fintype.equivFin W).symm).comp (measurable_bin _ _)
  refine ⟨hmeas, Measure.ext_of_singleton fun w => ?_⟩
  rw [Measure.map_apply hmeas (measurableSet_singleton w)]
  have he : (finiteLabel W) ⁻¹' {w} =
      (bin (Fintype.card W) Fintype.card_pos) ⁻¹' {Fintype.equivFin W w} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, finiteLabel, Equiv.symm_apply_eq]
  rw [he, bin_volume]
  simp [uniform]

open Finset SimpleGraph
open scoped Classical

private noncomputable def step (W : Type) [Fintype W] [Nonempty W] (G : SimpleGraph W)
    [DecidableRel G.Adj] : Graphon := by
  letI : MeasurableSpace W := ⊤
  letI : MeasurableSingletonClass W := ⟨fun _ => trivial⟩
  let weight (p : W × W) : I := if G.Adj p.1 p.2 then 1 else 0
  let f := finiteLabel W
  have hf := (label_preserving W).measurable
  refine ⟨fun p => weight (f p.1, f p.2),
    (measurable_of_countable weight).comp ((hf.comp measurable_fst).prodMk (hf.comp measurable_snd)), ?_⟩
  intro x y
  simp only [weight]
  exact if_congr ⟨fun h => h.symm, fun h => h.symm⟩ rfl rfl

private def Preserves {V W : Type} (H : SimpleGraph V) (G : SimpleGraph W) (f : V → W) : Prop :=
  ∀ u v, H.Adj u v → G.Adj (f u) (f v)

private theorem step_integrand {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [Nonempty W]
    (H : SimpleGraph V) (G : SimpleGraph W) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (x : V → I) : graphonHomIntegrand H (step W G) x =
      if Preserves H G (fun v => finiteLabel W (x v)) then 1 else 0 := by
  by_cases h : Preserves H G (fun v => finiteLabel W (x v))
  · rw [if_pos h, graphonHomIntegrand]
    apply Finset.prod_eq_one
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      change (↑(if G.Adj (finiteLabel W (x u)) (finiteLabel W (x v)) then (1:I) else 0) : ℝ) = 1
      rw [if_pos (h u v (mem_edgeFinset.mp he))]
      rfl
  · rw [if_neg h, graphonHomIntegrand]
    unfold Preserves at h
    push Not at h
    obtain ⟨u,v,hu,hv⟩ := h
    have he : s(u,v) ∈ H.edgeFinset := mem_edgeFinset.mpr hu
    apply Finset.prod_eq_zero he
    change (↑(if G.Adj (finiteLabel W (x u)) (finiteLabel W (x v)) then (1:I) else 0) : ℝ) = 0
    rw [if_neg hv]
    rfl

private theorem count_indicator {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (H : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel G.Adj] :
    ∑ f : V → W, (if Preserves H G f then (1 : ℝ) else 0) = (homCount H G : ℝ) := by
  let e : (H →g G) ≃ {f : V → W // Preserves H G f} :=
    { toFun := fun f => ⟨f, fun _ _ h => f.map_adj h⟩
      invFun := fun f => ⟨f.val, fun h => f.property _ _ h⟩
      left_inv := fun f => DFunLike.ext _ _ fun _ => rfl
      right_inv := fun f => Subtype.ext rfl }
  rw [Finset.sum_boole, homCount, Fintype.card_congr e, Fintype.card_subtype]

private theorem step_hom_density {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
    [Nonempty W] [DecidableEq W] (H : SimpleGraph V) (G : SimpleGraph W)
    [DecidableRel H.Adj] [DecidableRel G.Adj] :
    graphonHomDensity H (step W G) = homDensity H G := by
  letI : MeasurableSpace W := ⊤
  letI : MeasurableSingletonClass W := ⟨fun _ => trivial⟩
  letI : IsFiniteMeasure (uniform W) := ⟨by
    change (ENNReal.ofReal (1/(Fintype.card W : ℝ)) • (Measure.count : Measure W)) Set.univ < ⊤
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  let μ := Measure.pi (fun _ : V => (volume : Measure I))
  let ν := Measure.pi (fun _ : V => uniform W)
  let f (x : V → I) (v : V) := finiteLabel W (x v)
  let F (g : V → W) : ℝ := if Preserves H G g then 1 else 0
  have hf : MeasurePreserving f μ ν := measurePreserving_pi _ _ (fun _ => label_preserving W)
  have hF : Measurable F := measurable_of_countable _
  have htransport : (∫ x, F (f x) ∂μ) = ∫ g, F g ∂ν := by
    have hFm : AEStronglyMeasurable F (Measure.map f μ) := hF.aestronglyMeasurable
    simpa only [hf.map_eq] using (integral_map hf.aemeasurable hFm).symm
  have hnu : ν = (ENNReal.ofReal (1/(Fintype.card W : ℝ))) ^ Fintype.card V •
      (Measure.count : Measure (V → W)) := by
    apply Measure.ext_of_singleton
    intro g
    change (Measure.pi (fun _ : V => uniform W)) {g} = _
    rw [Measure.pi_singleton]
    simp [uniform, Measure.smul_apply, Finset.prod_const]
  calc
    _ = ∫ x, F (f x) ∂μ := by
      unfold graphonHomDensity
      apply integral_congr_ae
      exact Eventually.of_forall (step_integrand H G)
    _ = ∫ g, F g ∂ν := htransport
    _ = _ := by
      rw [hnu, integral_smul_measure, integral_count, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (by positivity)]
      rw [show (∑ g, F g) = (homCount H G : ℝ) from count_indicator H G]
      simp [homDensity, div_eq_mul_inv, mul_comm]

private theorem single_edge_density (S : Graphon) :
    graphonEdgeDensity S = graphonHomDensity (completeGraph (Fin 2)) S := by
  have hedges : (completeGraph (Fin 2)).edgeFinset = {s((0 : Fin 2), (1 : Fin 2))} := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [mem_edgeFinset, mem_edgeSet, Finset.mem_singleton]
      fin_cases u <;> fin_cases v <;> decide
  unfold graphonEdgeDensity graphonHomDensity
  rw [← (measurePreserving_finTwoArrow (volume : Measure I)).integral_comp']
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  rw [graphonHomIntegrand, hedges, Finset.prod_singleton]
  rfl

theorem main {V W : Type} [Fintype V] [Fintype W] [Nonempty W]
    [DecidableEq V] [DecidableEq W] (H : SimpleGraph V) [DecidableRel H.Adj]
    (G : SimpleGraph W) [DecidableRel G.Adj] : ∃ S : Graphon,
    graphonEdgeDensity S = homDensity (completeGraph (Fin 2)) G ∧
      graphonHomDensity H S = homDensity H G := by
  refine ⟨step W G, ?_, step_hom_density H G⟩
  rw [single_edge_density, step_hom_density]

end StepGraphonProof

theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1.H2 :=
  StepGraphonProof.main