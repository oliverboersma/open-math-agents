import OMAReductions.R_Green3_green_3_R2_H1_R1
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real

-- Step Green3.green_3.R2.H1.R1.H2: hypothesis H2 of reduction Green3.green_3.R2.H1.R1
-- Credit: @tongenspace

/-!
Proof of Franchi-Gowers-Yip Lemma 4.4 (`OMA.R_Green3_green_3_R2_H1_R1.H2`).
Let `g y = |A ∩ [0, y - 1]| + |A ∩ [0, y]| + |A ∩ [0, y + 1]| - y`.
Then `g` is continuous, `g 1 ≤ 0`, and `g z > 0`. Taking `t0 = sSup {y ∈ [1, z] | g y ≤ 0}`
and `t1` to be the least shifted endpoint of `A` (or `z`) strictly above `t0`, each of
`(t0 - 1, t1 - 1)`, `(t0, t1)`, `(t0 + 1, t1 + 1)` is either contained in `A` or disjoint
from `A`. Since `g t1 - g t0 > 0` and `A` is sum-free with `1 ∈ A`, both `(t0 - 1, t1 - 1)`
and `(t0 + 1, t1 + 1)` must lie in `A`. Choosing `x = (t0 + t1) / 2` and `ε = (t1 - t0) / 4`
gives the claim.
-/

namespace G3R2H1R1H2

open Set MeasureTheory

lemma volume_real_Icc_of_le {a b : ℝ} (h : a ≤ b) :
    volume.real (Icc a b) = b - a := by
  rw [Real.volume_real_Icc, max_eq_left (sub_nonneg.mpr h)]

lemma volume_real_Ioc_of_le {a b : ℝ} (h : a ≤ b) :
    volume.real (Ioc a b) = b - a := by
  rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr h)]

lemma volume_real_Ioo_of_le {a b : ℝ} (h : a ≤ b) :
    volume.real (Ioo a b) = b - a := by
  rw [measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (sub_nonneg.mpr h)]

lemma f_sub_le (A : Set ℝ) {a b : ℝ} (hab : a ≤ b) :
    volume.real (A ∩ Icc 0 b) - volume.real (A ∩ Icc 0 a) ≤ b - a := by
  have hsub : A ∩ Icc 0 b ⊆ (A ∩ Icc 0 a) ∪ Ioc a b := by
    rintro x ⟨hxA, hx0, hxb⟩
    rcases le_or_gt x a with hxa | hxa
    · exact Or.inl ⟨hxA, hx0, hxa⟩
    · exact Or.inr ⟨hxa, hxb⟩
  have hfin : volume ((A ∩ Icc 0 a) ∪ Ioc a b) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_union_le _ _)
    exact ENNReal.add_ne_top.mpr
      ⟨ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_right), by simp⟩
  have h1 : volume.real (A ∩ Icc 0 b) ≤ volume.real ((A ∩ Icc 0 a) ∪ Ioc a b) :=
    measureReal_mono hsub hfin
  have h2 : volume.real ((A ∩ Icc 0 a) ∪ Ioc a b) ≤
      volume.real (A ∩ Icc 0 a) + volume.real (Ioc a b) :=
    measureReal_union_le _ _
  rw [volume_real_Ioc_of_le hab] at h2
  linarith

lemma f_mono (A : Set ℝ) {a b : ℝ} (hab : a ≤ b) :
    volume.real (A ∩ Icc 0 a) ≤ volume.real (A ∩ Icc 0 b) := by
  refine measureReal_mono ?_ (ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_right))
  rintro x ⟨hxA, hx0, hxa⟩
  exact ⟨hxA, hx0, hxa.trans hab⟩

lemma f_continuous (A : Set ℝ) :
    Continuous (fun y : ℝ => volume.real (A ∩ Icc 0 y)) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε, hε, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  rcases le_total x y with hxy | hyx
  · have h1 := f_mono A hxy
    have h2 := f_sub_le A hxy
    rw [abs_of_nonneg (sub_nonneg.mpr h1)]
    rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at hy
    linarith
  · have h1 := f_mono A hyx
    have h2 := f_sub_le A hyx
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h1)]
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hyx)] at hy
    linarith

lemma f_sub_eq_Ioc {A : Set ℝ} (hAm : MeasurableSet A) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    volume.real (A ∩ Icc 0 b) - volume.real (A ∩ Icc 0 a) = volume.real (A ∩ Ioc a b) := by
  have hunion : A ∩ Icc 0 b = (A ∩ Icc 0 a) ∪ (A ∩ Ioc a b) := by
    ext x
    simp only [mem_inter_iff, mem_union, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨hxA, hx0, hxb⟩
      rcases le_or_gt x a with hxa | hxa
      · exact Or.inl ⟨hxA, hx0, hxa⟩
      · exact Or.inr ⟨hxA, hxa, hxb⟩
    · rintro (⟨hxA, hx0, hxa⟩ | ⟨hxA, hxa, hxb⟩)
      · exact ⟨hxA, hx0, hxa.trans hab⟩
      · exact ⟨hxA, ha.trans hxa.le, hxb⟩
  have hdisj : Disjoint (A ∩ Icc 0 a) (A ∩ Ioc a b) := by
    rw [Set.disjoint_left]
    rintro x ⟨_, _, hxa⟩ ⟨_, hax, _⟩
    linarith
  have hfin1 : volume (A ∩ Icc 0 a) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_right)
  have hfin2 : volume (A ∩ Ioc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_right)
  rw [hunion, measureReal_union hdisj (hAm.inter measurableSet_Ioc) hfin1 hfin2]
  ring

lemma vol_inter_Ioc_of_subset {A : Set ℝ} {a b : ℝ} (hab : a ≤ b)
    (hsub : Ioo a b ⊆ A) : volume.real (A ∩ Ioc a b) = b - a := by
  have hle : volume.real (A ∩ Ioc a b) ≤ b - a := by
    calc volume.real (A ∩ Ioc a b) ≤ volume.real (Ioc a b) :=
          measureReal_mono inter_subset_right (by simp)
      _ = b - a := volume_real_Ioc_of_le hab
  have hge : b - a ≤ volume.real (A ∩ Ioc a b) := by
    calc b - a = volume.real (Ioo a b) := (volume_real_Ioo_of_le hab).symm
      _ ≤ volume.real (A ∩ Ioc a b) :=
          measureReal_mono (fun x hx => ⟨hsub hx, hx.1, hx.2.le⟩)
            (ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_right))
  linarith

lemma vol_inter_Ioc_of_disjoint {A : Set ℝ} {a b : ℝ}
    (hdisj : Disjoint (Ioo a b) A) : volume.real (A ∩ Ioc a b) = 0 := by
  have hsub : A ∩ Ioc a b ⊆ {b} := by
    rintro x ⟨hxA, hax, hxb⟩
    rcases lt_or_eq_of_le hxb with hlt | heq
    · exact False.elim (Set.disjoint_left.mp hdisj ⟨hax, hlt⟩ hxA)
    · exact heq
  have hle : volume.real (A ∩ Ioc a b) ≤ volume.real ({b} : Set ℝ) :=
    measureReal_mono hsub (by simp)
  have hsing : volume.real ({b} : Set ℝ) = 0 := by
    rw [measureReal_def, Real.volume_singleton, ENNReal.toReal_zero]
  have hnn : 0 ≤ volume.real (A ∩ Ioc a b) := measureReal_nonneg
  linarith

lemma interval_dichotomy {s : Finset (ℝ × ℝ)} {A : Set ℝ}
    (hA : A = ⋃ p ∈ s, Icc p.1 p.2) {a b : ℝ}
    (hno : ∀ p ∈ s, p.1 ∉ Ioo a b ∧ p.2 ∉ Ioo a b) :
    Ioo a b ⊆ A ∨ Disjoint (Ioo a b) A := by
  by_cases h : Disjoint (Ioo a b) A
  · exact Or.inr h
  · left
    rw [Set.not_disjoint_iff] at h
    obtain ⟨w, ⟨haw, hwb⟩, hwA⟩ := h
    rw [hA, mem_iUnion₂] at hwA
    obtain ⟨p, hps, hp1, hp2⟩ := hwA
    have ⟨hno1, hno2⟩ := hno p hps
    have hp1le : p.1 ≤ a := by
      by_contra hlt
      push Not at hlt
      exact hno1 ⟨hlt, hp1.trans_lt hwb⟩
    have hblep2 : b ≤ p.2 := by
      by_contra hlt
      push Not at hlt
      exact hno2 ⟨haw.trans_le hp2, hlt⟩
    intro u ⟨hau, hub⟩
    rw [hA, mem_iUnion₂]
    exact ⟨p, hps, hp1le.trans hau.le, hub.le.trans hblep2⟩

end G3R2H1R1H2

open Set MeasureTheory in
theorem OMA.solution : OMA.R_Green3_green_3_R2_H1_R1.H2 := by
  classical
  intro A ⟨s, hs⟩ hleast hsf z hz1 hz
  have hAm : MeasurableSet A := by
    rw [hs]
    exact Finset.measurableSet_biUnion s (fun _ _ => measurableSet_Icc)
  let f : ℝ → ℝ := fun y => volume.real (A ∩ Icc 0 y)
  let g : ℝ → ℝ := fun y => f (y - 1) + f y + f (y + 1) - y
  have hg_cont : Continuous g := by
    have hf := G3R2H1R1H2.f_continuous A
    exact (((hf.comp (continuous_id.sub continuous_const)).add hf).add
      (hf.comp (continuous_id.add continuous_const))).sub continuous_id
  have hg1 : g 1 ≤ 0 := by
    have hf0 : f 0 = 0 := by
      have hempty : A ∩ Icc 0 0 = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Icc, mem_empty_iff_false, iff_false, not_and]
        intro hxA _ hx0
        have := hleast.2 hxA
        linarith
      change volume.real (A ∩ Icc 0 0) = 0
      rw [hempty, measureReal_empty]
    have hf1 : f 1 = 0 := by
      have hsub : A ∩ Icc 0 1 ⊆ ({1} : Set ℝ) := by
        rintro x ⟨hxA, _, hx1⟩
        have := hleast.2 hxA
        exact le_antisymm hx1 this
      have hle : f 1 ≤ volume.real ({1} : Set ℝ) := measureReal_mono hsub (by simp)
      have hsing : volume.real ({1} : Set ℝ) = 0 := by
        rw [measureReal_def, Real.volume_singleton, ENNReal.toReal_zero]
      have hnn : 0 ≤ f 1 := measureReal_nonneg
      linarith
    have hf2 : f 2 ≤ 1 := by
      have hsub : A ∩ Icc 0 2 ⊆ Icc (1 : ℝ) 2 := by
        rintro x ⟨hxA, _, hx2⟩
        exact ⟨hleast.2 hxA, hx2⟩
      calc f 2 ≤ volume.real (Icc (1 : ℝ) 2) := measureReal_mono hsub (by simp)
        _ = 1 := by rw [G3R2H1R1H2.volume_real_Icc_of_le (by norm_num)]; norm_num
    have heq : g 1 = f 0 + f 1 + f 2 - 1 := by
      dsimp only [g]
      norm_num
    linarith
  have hgz : 0 < g z := by
    dsimp only [g, f]
    linarith
  let S : Set ℝ := Icc 1 z ∩ g ⁻¹' Iic 0
  have h1S : (1 : ℝ) ∈ S := ⟨⟨le_rfl, hz1⟩, hg1⟩
  have hSne : S.Nonempty := ⟨1, h1S⟩
  have hSbdd : BddAbove S := ⟨z, fun y hy => hy.1.2⟩
  have hSclosed : IsClosed S := isClosed_Icc.inter (isClosed_Iic.preimage hg_cont)
  let t0 : ℝ := sSup S
  have ht0S : t0 ∈ S := hSclosed.csSup_mem hSne hSbdd
  have ht0_ge1 : 1 ≤ t0 := ht0S.1.1
  have ht0_lez : t0 ≤ z := ht0S.1.2
  have hgt0 : g t0 ≤ 0 := ht0S.2
  have ht0_ltz : t0 < z := lt_of_le_of_ne ht0_lez (fun h => by rw [h] at hgt0; linarith)
  have hg_pos : ∀ y ∈ Ioc t0 z, 0 < g y := by
    intro y ⟨ht0y, hyz⟩
    by_contra hle
    push Not at hle
    have hyS : y ∈ S := ⟨⟨ht0_ge1.trans ht0y.le, hyz⟩, hle⟩
    have : y ≤ t0 := le_csSup hSbdd hyS
    linarith
  let E : Finset ℝ :=
    {z} ∪ s.biUnion (fun p => {p.1 - 1, p.1, p.1 + 1, p.2 - 1, p.2, p.2 + 1})
  let E' : Finset ℝ := E.filter (fun e => t0 < e)
  have hzE' : z ∈ E' := by
    simp only [E', E, Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    exact ⟨Or.inl trivial, ht0_ltz⟩
  have hE'ne : E'.Nonempty := ⟨z, hzE'⟩
  let t1 : ℝ := E'.min' hE'ne
  have ht1_mem : t1 ∈ E' := Finset.min'_mem E' hE'ne
  have ht0_lt_t1 : t0 < t1 := (Finset.mem_filter.mp ht1_mem).2
  have ht1_lez : t1 ≤ z := Finset.min'_le E' z hzE'
  have hno_E : ∀ e ∈ E, e ∉ Ioo t0 t1 := by
    intro e he ⟨ht0e, het1⟩
    have heE' : e ∈ E' := Finset.mem_filter.mpr ⟨he, ht0e⟩
    have : t1 ≤ e := Finset.min'_le E' e heE'
    linarith
  have hno_shift : ∀ k : ℝ, (k = -1 ∨ k = 0 ∨ k = 1) →
      ∀ p ∈ s, p.1 ∉ Ioo (t0 + k) (t1 + k) ∧ p.2 ∉ Ioo (t0 + k) (t1 + k) := by
    intro k hk p hps
    have hmem : ∀ c : ℝ, (c = p.1 ∨ c = p.2) → c - k ∈ E := by
      intro c hc
      simp only [E, Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert,
        Finset.mem_singleton]
      right
      refine ⟨p, hps, ?_⟩
      rcases hc with rfl | rfl <;> rcases hk with rfl | rfl | rfl
      · right; right; left; ring
      · right; left; ring
      · left; ring
      · right; right; right; right; right; ring
      · right; right; right; right; left; ring
      · right; right; right; left; ring
    constructor
    · intro ⟨h1, h2⟩
      exact hno_E (p.1 - k) (hmem p.1 (Or.inl rfl)) ⟨by linarith, by linarith⟩
    · intro ⟨h1, h2⟩
      exact hno_E (p.2 - k) (hmem p.2 (Or.inr rfl)) ⟨by linarith, by linarith⟩
  have hd_m1 : Ioo (t0 - 1) (t1 - 1) ⊆ A ∨ Disjoint (Ioo (t0 - 1) (t1 - 1)) A := by
    have h := G3R2H1R1H2.interval_dichotomy hs (hno_shift (-1) (Or.inl rfl))
    simpa only [← sub_eq_add_neg] using h
  have hd_0 : Ioo t0 t1 ⊆ A ∨ Disjoint (Ioo t0 t1) A := by
    have h := G3R2H1R1H2.interval_dichotomy hs (hno_shift 0 (Or.inr (Or.inl rfl)))
    simpa only [add_zero] using h
  have hd_p1 : Ioo (t0 + 1) (t1 + 1) ⊆ A ∨ Disjoint (Ioo (t0 + 1) (t1 + 1)) A :=
    G3R2H1R1H2.interval_dichotomy hs (hno_shift 1 (Or.inr (Or.inr rfl)))
  have hgt1 : 0 < g t1 := hg_pos t1 ⟨ht0_lt_t1, ht1_lez⟩
  have hdg : 0 < g t1 - g t0 := by linarith
  have hdg_eq : g t1 - g t0 =
      volume.real (A ∩ Ioc (t0 - 1) (t1 - 1)) + volume.real (A ∩ Ioc t0 t1) +
        volume.real (A ∩ Ioc (t0 + 1) (t1 + 1)) - (t1 - t0) := by
    have e1 := G3R2H1R1H2.f_sub_eq_Ioc hAm (a := t0 - 1) (b := t1 - 1) (by linarith) (by linarith)
    have e2 := G3R2H1R1H2.f_sub_eq_Ioc hAm (a := t0) (b := t1) (by linarith) (by linarith)
    have e3 := G3R2H1R1H2.f_sub_eq_Ioc hAm (a := t0 + 1) (b := t1 + 1) (by linarith) (by linarith)
    dsimp only [g, f]
    linarith
  have hboth : Ioo (t0 - 1) (t1 - 1) ⊆ A ∧ Ioo (t0 + 1) (t1 + 1) ⊆ A := by
    set m : ℝ := (t0 + t1) / 2 with hm_def
    have hm_m1 : m - 1 ∈ Ioo (t0 - 1) (t1 - 1) := ⟨by linarith, by linarith⟩
    have hm_0 : m ∈ Ioo t0 t1 := ⟨by linarith, by linarith⟩
    have hm_p1 : m + 1 ∈ Ioo (t0 + 1) (t1 + 1) := ⟨by linarith, by linarith⟩
    rcases hd_m1 with h1 | h1 <;> rcases hd_0 with h2 | h2 <;> rcases hd_p1 with h3 | h3
    · exfalso
      have hbad := hsf (m - 1) (h1 hm_m1) 1 hleast.1
      have : (m - 1) + 1 = m := by ring
      rw [this] at hbad
      exact hbad (h2 hm_0)
    · exfalso
      have hbad := hsf (m - 1) (h1 hm_m1) 1 hleast.1
      have : (m - 1) + 1 = m := by ring
      rw [this] at hbad
      exact hbad (h2 hm_0)
    · exact ⟨h1, h3⟩
    · exfalso
      rw [G3R2H1R1H2.vol_inter_Ioc_of_subset (by linarith) h1,
        G3R2H1R1H2.vol_inter_Ioc_of_disjoint h2,
        G3R2H1R1H2.vol_inter_Ioc_of_disjoint h3] at hdg_eq
      linarith
    · exfalso
      have hbad := hsf m (h2 hm_0) 1 hleast.1
      exact hbad (h3 hm_p1)
    · exfalso
      rw [G3R2H1R1H2.vol_inter_Ioc_of_disjoint h1,
        G3R2H1R1H2.vol_inter_Ioc_of_subset (by linarith) h2,
        G3R2H1R1H2.vol_inter_Ioc_of_disjoint h3] at hdg_eq
      linarith
    · exfalso
      rw [G3R2H1R1H2.vol_inter_Ioc_of_disjoint h1,
        G3R2H1R1H2.vol_inter_Ioc_of_disjoint h2,
        G3R2H1R1H2.vol_inter_Ioc_of_subset (by linarith) h3] at hdg_eq
      linarith
    · exfalso
      rw [G3R2H1R1H2.vol_inter_Ioc_of_disjoint h1,
        G3R2H1R1H2.vol_inter_Ioc_of_disjoint h2,
        G3R2H1R1H2.vol_inter_Ioc_of_disjoint h3] at hdg_eq
      linarith
  refine ⟨(t0 + t1) / 2, (t1 - t0) / 4, by linarith, by linarith, ?_, ?_, ?_⟩
  · intro y ⟨hy1, hy2⟩
    have hy : 0 < g y := hg_pos y ⟨by linarith, by linarith⟩
    dsimp only [g, f] at hy
    linarith
  · intro u ⟨hu1, hu2⟩
    exact hboth.1 ⟨by linarith, by linarith⟩
  · intro u ⟨hu1, hu2⟩
    exact hboth.2 ⟨by linarith, by linarith⟩
