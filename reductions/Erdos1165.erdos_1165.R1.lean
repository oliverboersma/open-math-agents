import FormalConjectures.ErdosProblems.«1165»
import Mathlib

/-!
Work with the canonical product law of the increments. Index ties by the
maximum local time, as in Hao, Li, Okada and Zheng (2024), Section 4. Summably
rare missed windows for three favourites force arbitrarily high record levels.
Thus time eventually leaves each finite range of levels. Borel-Cantelli at the
levels with four favourites gives the stated probability for every r ≥ 3.
-/

namespace OMA.R_Erdos1165_erdos_1165_R1
open Erdos1165 Filter MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

/-- Choose windows of record levels in which the probability of missing a
triple tie is summable. -/
def H1 : Prop :=
  let μ := Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond (Measure.count : Measure (ℤ × ℤ)) steps)
  let inc (i : ℕ) (w : ℕ → ℤ × ℤ) := w i
  let peak (n : ℕ) (w : ℕ → ℤ × ℤ) := (Finset.range (n+1)).sup fun i =>
    localTime inc n w (position inc i w)
  let hit (m k : ℕ) : Set (ℕ → ℤ × ℤ) := {w | ∃ n, peak n w = m ∧
    (k : ℕ∞) ≤ (favouriteSites inc n w).encard}
  ∃ b : ℕ → ℕ, (∑' j : ℕ, μ {w | ¬ ∃ m ∈ Finset.Icc j (b j), w ∈ hit m 3}) ≠ ∞

/-- The probabilities of four-way ties on the good profiles are summable.
Almost every walk has a good profile at every sufficiently large level. -/
def H2 : Prop :=
  let μ := Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond (Measure.count : Measure (ℤ × ℤ)) steps)
  let inc (i : ℕ) (w : ℕ → ℤ × ℤ) := w i
  let peak (n : ℕ) (w : ℕ → ℤ × ℤ) := (Finset.range (n+1)).sup fun i =>
    localTime inc n w (position inc i w)
  let hit (m k : ℕ) : Set (ℕ → ℤ × ℤ) := {w | ∃ n, peak n w = m ∧
    (k : ℕ∞) ≤ (favouriteSites inc n w).encard}
  ∃ G : ℕ → Set (ℕ → ℤ × ℤ), (∀ᵐ w ∂μ, ∀ᶠ m in atTop, w ∈ G m) ∧
    (∑' m : ℕ, μ (hit m 4 ∩ G m)) ≠ ∞

theorem favourite_event_measurable (n r : ℕ) :
    MeasurableSet {w : ℕ → ℤ × ℤ | (favouriteSites (fun i v => v i) n w).encard = (r:ℕ∞)} := by
  classical
  let cut (w : ℕ → ℤ × ℤ) (i : Fin n) := w i
  let extend (a : Fin n → ℤ × ℤ) (i : ℕ) := if hi : i < n then a ⟨i,hi⟩ else 0
  have hcut : Measurable cut := measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  let T := {a : Fin n → ℤ × ℤ | (favouriteSites (fun i v => v i) n (extend a)).encard = r}
  have hT : MeasurableSet T := (Set.to_countable T).measurableSet
  convert hcut hT using 1
  ext w
  have pos (k : ℕ) (hk : k ≤ n) : position (fun i v => v i) k (extend (cut w)) =
      position (fun i v => v i) k w := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mem_range] at hi
    simp [extend,cut,show i<n by omega]
  have loc (x : ℤ × ℤ) : localTime (fun i v => v i) n (extend (cut w)) x =
      localTime (fun i v => v i) n w x := by
    unfold localTime
    congr 1
    apply Finset.filter_congr
    intro k hk
    rw [pos k (by simpa using hk)]
  have fav : favouriteSites (fun i v => v i) n (extend (cut w)) =
      favouriteSites (fun i v => v i) n w := by
    ext x
    simp only [favouriteSites,Set.mem_ofPred_eq,loc]
  change _ ↔ (favouriteSites (fun i v => v i) n (extend (cut w))).encard = (r:ℕ∞)
  rw [fav]
  rfl

theorem main : H1 → H2 → type_of% @Erdos1165.erdos_1165 := by
  classical
  intro h₁ h₂ Ω inst prob X walk r hr
  let μ := Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.cond (Measure.count : Measure (ℤ × ℤ)) steps)
  let inc (i : ℕ) (w : ℕ → ℤ × ℤ) := w i
  let peak (n : ℕ) (w : ℕ → ℤ × ℤ) := (Finset.range (n+1)).sup fun i =>
    localTime inc n w (position inc i w)
  let hit (m k : ℕ) : Set (ℕ → ℤ × ℤ) := {w | ∃ n, peak n w = m ∧
    (k : ℕ∞) ≤ (favouriteSites inc n w).encard}
  let sample (ω : Ω) (i : ℕ) := X i ω
  have hsm : Measurable sample := measurable_pi_lambda _ walk.measurable
  have law : Measure.map sample ℙ = μ := by
    have h := walk.indep.map_fun_eq_infinitePi_map walk.measurable
    have marg : (fun i => Measure.map (X i) ℙ) =
        fun _ : ℕ => ProbabilityTheory.cond (Measure.count : Measure (ℤ × ℤ)) steps :=
      funext fun i => walk.isUniform i
    simpa only [marg] using h
  have : IsProbabilityMeasure μ := law ▸ Measure.isProbabilityMeasure_map hsm.aemeasurable
  obtain ⟨b,hMiss⟩ := h₁
  obtain ⟨G,hGood,hFour⟩ := h₂
  change (∑' j : ℕ, μ {w | ¬ ∃ m ∈ Finset.Icc j (b j), w ∈ hit m 3}) ≠ ∞ at hMiss
  change (∑' m : ℕ, μ (hit m 4 ∩ G m)) ≠ ∞ at hFour
  have hm (w : ℕ → ℤ × ℤ) : Monotone (fun n => peak n w) := by
    intro n k hnk
    apply Finset.sup_le
    intro i hi
    have hix : i ∈ range (k+1) := (range_mono (by omega : n+1 ≤ k+1)) hi
    refine le_trans ?_ (Finset.le_sup (f := fun i => localTime inc k w (position inc i w)) hix)
    exact Finset.card_le_card (Finset.filter_subset_filter _ (range_mono (by omega)))
  have cap (w : ℕ → ℤ × ℤ) (n : ℕ) : peak n w ≤ n+1 := by
    apply Finset.sup_le
    intro i hi
    simpa [localTime] using (Finset.card_filter_le (range (n+1)) (fun k => position inc k w = position inc i w))
  let C (w : ℕ → ℤ × ℤ) (n : ℕ) := (favouriteSites inc n w).encard
  have core : ∀ᵐ w ∂μ, (∃ᶠ n in atTop, C w n = 3) ∧ ∀ᶠ n in atTop, C w n < 4 := by
    filter_upwards [ae_eventually_notMem hMiss,ae_eventually_notMem hFour,hGood] with w miss rare good
    obtain ⟨j₀,hj⟩ := eventually_atTop.mp miss
    have many (L : ℕ) : ∃ n, L ≤ peak n w ∧ 3 ≤ C w n := by
      have hex := hj (max L j₀) (le_max_right _ _)
      change ¬ ¬ ∃ m ∈ Finset.Icc (max L j₀) (b (max L j₀)), w ∈ hit m 3 at hex
      obtain ⟨m,hm,nn,he,hc⟩ := not_not.mp hex
      refine ⟨nn,?_,hc⟩
      rw [he]
      exact (le_max_left _ _).trans (Finset.mem_Icc.mp hm).1
    have few : ∀ᶠ m in atTop, w ∉ hit m 4 := by
      filter_upwards [rare,good] with m hbad hg hw using hbad ⟨hw,hg⟩
    obtain ⟨K,hK⟩ := eventually_atTop.mp few
    obtain ⟨t,ht,_⟩ := many K
    have upper : ∀ n ≥ t, C w n < 4 := by
      intro n hn
      apply lt_of_not_ge
      intro hc
      exact hK (peak n w) (ht.trans (hm w hn)) ⟨n,rfl,hc⟩
    refine ⟨frequently_atTop.mpr ?_, eventually_atTop.mpr ⟨t,upper⟩⟩
    intro N
    obtain ⟨n,hlev,hc⟩ := many (N+t+2)
    have hcap := cap w n
    have hut := upper n (by omega)
    exact ⟨n,by omega,le_antisymm ((ENat.lt_add_one_iff (by decide : (3:ℕ∞) ≠ ⊤)).mp hut) hc⟩
  let event := {w : ℕ → ℤ × ℤ | ∃ᶠ n in atTop, C w n = (r:ℕ∞)}
  have hev : MeasurableSet event := by
    have eqn : event = ⋂ j : ℕ, ⋃ (n : ℕ) (_ : j ≤ n), {w | C w n = (r:ℕ∞)} := by
      ext w
      simp [event,frequently_atTop]
    rw [eqn]
    exact MeasurableSet.iInter fun j => MeasurableSet.iUnion fun n =>
      MeasurableSet.iUnion fun _ => favourite_event_measurable n r
  change ℙ (sample ⁻¹' event) = _
  rw [← Measure.map_apply hsm hev,law]
  by_cases h : r = 3
  · subst r
    rw [erdos_1165.answer,if_pos rfl]
    exact (mem_ae_iff_prob_eq_one hev).mp (core.mono fun w hw => hw.1)
  · rw [erdos_1165.answer,if_neg h]
    apply ae_iff.mp
    filter_upwards [core] with w hw
    filter_upwards [hw.2] with n hn he
    have hh : (4:ℕ∞) ≤ (r:ℕ∞) := by exact_mod_cast (show 4 ≤ r by omega)
    exact (not_le_of_gt hn) (he.symm ▸ hh)

end OMA.R_Erdos1165_erdos_1165_R1
