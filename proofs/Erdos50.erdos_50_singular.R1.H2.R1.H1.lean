import OMAReductions.R_Erdos50_erdos_50_singular_R1_H2_R1
import Mathlib

/-! The empirical probability measures live on the compact unit interval.
A weak cluster point satisfies the closed-set inequality. The given
continuity then identifies its distribution function, including at the endpoints. -/
namespace PhiEmpirical
open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Classical

private noncomputable def numberBelow (S : Set ℕ) (N : ℕ) := ((Finset.range N).filter (· ∈ S)).card
private noncomputable def value (n : ℕ) : ℝ := n.totient/(n:ℝ)

private lemma density_count (S : Set ℕ) (N : ℕ) : S.partialDensity univ N =
    (numberBelow S N : ℝ)/N := by
  have h : S ∩ Iio N = ↑((Finset.range N).filter (· ∈ S)) := by ext n; simp [and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  rw [h,Set.ncard_coe_finset,Nat.ncard_Iio]
  rfl

private lemma count_compare {S T : Set ℕ} {K : ℕ} (h : ∀ n ≥ K, n ∈ S → n ∈ T) (N : ℕ) :
    numberBelow S N ≤ numberBelow T N + K := by
  let U := (Finset.range N).filter (· ∈ T)
  have sub : (Finset.range N).filter (· ∈ S) ⊆ U ∪ Finset.range K := by
    intro n hn
    obtain ⟨hN,hs⟩ := Finset.mem_filter.mp hn
    by_cases b : n<K
    · exact Finset.mem_union_right _ (Finset.mem_range.mpr b)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hN,h n (by omega) hs⟩)
  simpa [numberBelow,U] using (Finset.card_le_card sub).trans (Finset.card_union_le _ _)

private lemma density_transfer {S T : Set ℕ} {K : ℕ} {a : ℝ} (h : ∀ n ≥ K, n ∈ S ↔ n ∈ T)
    (lim : S.HasDensity a) : Tendsto (fun N : ℕ => (numberBelow T N : ℝ)/N) atTop (𝓝 a) := by
  have base : Tendsto (fun N : ℕ => (numberBelow S N : ℝ)/N) atTop (𝓝 a) := by
    simpa only [Set.HasDensity,density_count] using lim
  have small : Tendsto (fun N : ℕ => (K:ℝ)/N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have lo := base.sub small
  have hi := base.add small
  rw [sub_zero] at lo
  rw [add_zero] at hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le lo hi
  · intro N
    have e : (numberBelow S N:ℝ) ≤ numberBelow T N+K := by exact_mod_cast count_compare (fun n b => (h n b).mp) N
    change (numberBelow S N:ℝ)/N - K/N ≤ _
    rw [←sub_div]
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  · intro N
    have e : (numberBelow T N:ℝ) ≤ numberBelow S N+K := by exact_mod_cast count_compare (fun n b => (h n b).mpr) N
    change _ ≤ (numberBelow S N:ℝ)/N + K/N
    rw [←add_div]
    exact div_le_div_of_nonneg_right e (Nat.cast_nonneg _)

private noncomputable def boundedValue (n : ℕ) : Icc (0:ℝ) 1 :=
  ⟨value n,by
    dsimp [value]
    refine ⟨by positivity, ?_⟩
    rcases n.eq_zero_or_pos with rfl|hn
    · simp
    · exact (div_le_one (by exact_mod_cast hn)).mpr (by exact_mod_cast Nat.totient_le n)⟩

private noncomputable def indexMeasure (N : ℕ) : ProbabilityMeasure ℕ :=
  ⟨uniformOn (Finset.range (N+1) : Set ℕ),
    isProbabilityMeasure_uniformOn (Finset.range (N+1)).finite_toSet (by simp)⟩

private noncomputable def law (N : ℕ) : ProbabilityMeasure (Icc (0:ℝ) 1) :=
  (indexMeasure N).map (f := boundedValue) (measurable_of_countable _).aemeasurable

private noncomputable def realLaw (N : ℕ) : ProbabilityMeasure ℝ :=
  (law N).map (f := Subtype.val) continuous_subtype_val.measurable.aemeasurable

private lemma law_eval (N : ℕ) {C : Set ℝ} (hC : MeasurableSet C) :
    (realLaw N : Measure ℝ) C = ENNReal.ofReal ((numberBelow (value ⁻¹' C) (N+1):ℝ)/(N+1)) := by
  rw [realLaw,ProbabilityMeasure.map_apply' _ _ hC,law,ProbabilityMeasure.map_apply' _ _
    (continuous_subtype_val.measurable hC)]
  let R := Finset.range (N+1)
  let S := R.filter (· ∈ value ⁻¹' C)
  change uniformOn (R : Set ℕ) (value ⁻¹' C) = _
  rw [← uniformOn_inter_self R.finite_toSet]
  have eq : (R : Set ℕ) ∩ value ⁻¹' C = (S : Set ℕ) := by ext n; simp [S]
  rw [eq,uniformOn_apply_finset,Finset.inter_eq_right.mpr (Finset.filter_subset ..)]
  rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast]
  simp [R,S,numberBelow,ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]


private lemma claim : OMA.R_Erdos50_erdos_50_singular_R1_H2_R1.H1 := by
  classical
  intro f hf hc
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let L : Filter ℕ := U
  haveI : L.NeBot := U.neBot'
  have hL : L ≤ atTop := Ultrafilter.of_le _
  let ν := (U.map law).lim
  have weak : Tendsto law L (𝓝 ν) := (U.map law).le_nhds_lim
  let μ : ProbabilityMeasure ℝ := ν.map (f := Subtype.val) continuous_subtype_val.measurable.aemeasurable
  have weakR : Tendsto realLaw L (𝓝 μ) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous law ν weak continuous_subtype_val
  refine ⟨(μ : Measure ℝ), inferInstance, ?_, ?_⟩
  · have strict (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
        Tendsto (fun n => (realLaw n : Measure ℝ) (Iio t)) L (𝓝 (ENNReal.ofReal (f t))) := by
      have start := hf t ht
      have lim := density_transfer (T := value ⁻¹' Iio t) (K := 1) (by
        intro n hn
        change (n.totient:ℝ) < t*n ↔ (n.totient:ℝ)/n < t
        exact (div_lt_iff₀ (by exact_mod_cast (by omega : 0<n))).symm) start
      have comp := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (lim.comp ((tendsto_add_atTop_nat 1).mono_left hL))
      apply comp.congr fun n => ?_
      simpa only [Function.comp_apply,Nat.cast_add,Nat.cast_one] using (law_eval n measurableSet_Iio).symm
    have topval : f 1 = 1 := by
      have h := hf 1 (by simp)
      have left : Tendsto (fun N : ℕ => (numberBelow {n : ℕ | (n.totient:ℝ)<1*n} N:ℝ)/N)
          atTop (𝓝 (f 1)) := by simpa only [Set.HasDensity,density_count] using h
      have right := density_transfer (S := (univ : Set ℕ))
        (T := {n : ℕ | (n.totient:ℝ)<1*n}) (K:=2) (by
          intro n hn
          simp only [mem_univ,mem_setOf_eq,one_mul,true_iff]
          exact_mod_cast Nat.totient_lt n (by omega : 1<n)) Set.HasDensity.univ_nat_hasDensity_one
      exact tendsto_nhds_unique left right
    have leftRay (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
        (μ:Measure ℝ).real (Iio s) ≤ f s := by
      have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto weakR (isOpen_Iio (a:=s))
      rw [(strict s hs).liminf_eq] at h
      simpa only [Measure.real,ENNReal.toReal_ofReal (hf s hs).nonneg] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    intro t ht
    rw [cdf_eq_real]
    apply le_antisymm
    · have h : ENNReal.ofReal (f t) ≤ (μ:Measure ℝ) (Iic t) := calc
        _ = L.limsup (fun n => (realLaw n : Measure ℝ) (Iio t)) := (strict t ht).limsup_eq.symm
        _ ≤ L.limsup (fun n => (realLaw n : Measure ℝ) (Iic t)) :=
          limsup_le_limsup (Eventually.of_forall fun _ => measure_mono Iio_subset_Iic_self)
        _ ≤ _ := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto weakR isClosed_Iic
      simpa only [Measure.real,ENNReal.toReal_ofReal (hf t ht).nonneg] using
        ENNReal.toReal_mono (measure_ne_top _ _) h
    · rcases ht.2.eq_or_lt with rfl|ht'
      · rw [topval]
        exact measureReal_le_one
      have ev : Ioc t 1 ∈ 𝓝[>] t := Ioc_mem_nhdsGT ht'
      have incl : 𝓝[>] t ≤ 𝓝[Icc 0 1] t := le_inf nhdsWithin_le_nhds
        (le_principal_iff.mpr (mem_of_superset ev fun y hy => ⟨ht.1.trans hy.1.le,hy.2⟩))
      apply ge_of_tendsto ((hc t ht).mono_left incl)
      filter_upwards [ev] with y hy
      exact (measureReal_mono (μ := (μ : Measure ℝ)) (Iic_subset_Iio.mpr hy.1)).trans (leftRay y ⟨ht.1.trans hy.1.le,hy.2⟩)
  · intro C hC a bound
    apply le_trans _ (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto weakR hC)
    apply le_limsup_of_frequently_le'
    apply Eventually.frequently
    have shifted := (tendsto_add_atTop_nat 1).eventually bound
    apply (shifted.filter_mono hL).mono
    intro n hn
    rw [law_eval n hC.measurableSet]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
    simpa only [Nat.cast_add,Nat.cast_one,numberBelow,show value = (fun n : ℕ => (n.totient:ℝ)/n) from rfl] using hn

end PhiEmpirical

theorem OMA.solution : OMA.R_Erdos50_erdos_50_singular_R1_H2_R1.H1 := PhiEmpirical.claim

