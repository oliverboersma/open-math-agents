import OMAReductions.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1

-- Step Erdos36.minimum_overlap.variants.lower.white_2022.R1.H3: hypothesis H3 of reduction Erdos36.minimum_overlap.variants.lower.white_2022.R1
-- Credit: @ivillar
-- The step function is 1 on the cells ((a-1)/n - 1, a/n - 1] with a in A. Its overlap integrand is bounded by the indicators of the pairwise cell intersections, whose lengths are the tent values divided by n.

namespace WhiteStep

open MeasureTheory

noncomputable def lo (n : ℕ) (a : ℤ) : ℝ := ((a : ℝ) - 1) / n - 1

noncomputable def hi (n : ℕ) (a : ℤ) : ℝ := (a : ℝ) / n - 1

lemma ceil_eq_iff_mem {n : ℕ} (hn : 0 < n) (a : ℤ) (t : ℝ) :
    ⌈(n : ℝ) * (t + 1)⌉ = a ↔ t ∈ Set.Ioc (lo n a) (hi n a) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Int.ceil_eq_iff, Set.mem_Ioc]
  unfold lo hi
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hN]
      nlinarith
    · rw [le_sub_iff_add_le, le_div_iff₀ hN]
      nlinarith
  · rintro ⟨h1, h2⟩
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hN] at h1
    rw [le_sub_iff_add_le, le_div_iff₀ hN] at h2
    constructor <;> nlinarith

lemma tent_eq {n : ℕ} (hn : 0 < n) (a b : ℤ) (x : ℝ) :
    max (min (hi n a) (hi n b - x) - max (lo n a) (lo n b - x)) 0 =
      max 0 (1 - |((b - a : ℤ) : ℝ) - n * x|) / n := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : hi n b - x = hi n a + (((b - a : ℤ) : ℝ) - n * x) / n := by
    unfold hi
    push_cast
    field_simp
    ring
  have e2 : lo n b - x = lo n a + (((b - a : ℤ) : ℝ) - n * x) / n := by
    unfold lo
    push_cast
    field_simp
    ring
  have e3 : hi n a - lo n a = 1 / n := by
    unfold hi lo
    field_simp
    ring
  rw [e1, e2]
  generalize (((b - a : ℤ) : ℝ) - n * x) = u
  have key : min (hi n a) (hi n a + u / n) - max (lo n a) (lo n a + u / n) = (1 - |u|) / n := by
    rcases le_total 0 u with h | h
    · have h' : 0 ≤ u / n := div_nonneg h hN.le
      rw [min_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg h, sub_div]
      linarith
    · have h' : u / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hN.le
      rw [min_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos h, sub_div, neg_div]
      linarith
  rw [key]
  rcases le_total 0 (1 - |u|) with h | h
  · rw [max_eq_left (div_nonneg h hN.le), max_eq_right h]
  · rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg h hN.le), max_eq_left h, zero_div]

end WhiteStep

open MeasureTheory WhiteStep OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1

theorem OMA.solution : OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1.H3 := by
  intro n hn A B hd hu hc
  classical
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hAn : A.card = n := card_left hd hu hc
  have hmemA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ 2 * (n : ℤ) := by
    intro a ha
    have h1 : a ∈ Finset.Icc (1 : ℤ) (2 * n) := hu ▸ Finset.mem_union_left B ha
    exact Finset.mem_Icc.mp h1
  let f : ℝ → ℝ := fun t => if ⌈(n : ℝ) * (t + 1)⌉ ∈ A then 1 else 0
  have hf01 : ∀ t, 0 ≤ f t ∧ f t ≤ 1 := by
    intro t
    simp only [f]
    split_ifs <;> norm_num
  have hfm : Measurable f := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (Int.measurable_ceil.comp (measurable_const.mul (measurable_id.add_const 1)))
      (Finset.measurableSet A)
  have hfsum : ∀ t, f t = ∑ a ∈ A, (Set.Ioc (lo n a) (hi n a)).indicator (1 : ℝ → ℝ) t := by
    intro t
    have h1 : f t = ∑ a ∈ A, if ⌈(n : ℝ) * (t + 1)⌉ = a then (1 : ℝ) else 0 :=
      (Finset.sum_ite_eq A _ (fun _ => (1 : ℝ))).symm
    rw [h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : ⌈(n : ℝ) * (t + 1)⌉ = a
    · rw [if_pos h, Set.indicator_of_mem ((ceil_eq_iff_mem hn a t).mp h)]
      rfl
    · rw [if_neg h, Set.indicator_of_notMem (fun h' => h ((ceil_eq_iff_mem hn a t).mpr h'))]
  refine ⟨f, hfm, hf01, ?_, ?_⟩
  · rw [intervalIntegral.integral_of_le (by norm_num)]
    have hcell : ∀ a ∈ A, ∫ t in Set.Ioc (-1 : ℝ) 1,
        (Set.Ioc (lo n a) (hi n a)).indicator (1 : ℝ → ℝ) t = 1 / n := by
      intro a ha
      obtain ⟨h1, h2⟩ := hmemA a ha
      have h3 : (-1 : ℝ) ≤ lo n a := by
        unfold lo
        have h4 : (0 : ℝ) ≤ ((a : ℝ) - 1) / n :=
          div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ a - 1)) hN.le
        linarith
      have h5 : hi n a ≤ 1 := by
        unfold hi
        have h6 : (a : ℝ) / n ≤ 2 := by
          rw [div_le_iff₀ hN]
          exact_mod_cast h2
        linarith
      rw [setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_right.mpr (Set.Ioc_subset_Ioc h3 h5)]
      simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one]
      rw [Real.volume_real_Ioc_of_le (by unfold lo hi; rw [sub_le_sub_iff_right]; gcongr; linarith)]
      unfold hi lo
      field_simp
      ring
    have hint : ∀ a ∈ A, Integrable
        (fun t => (Set.Ioc (lo n a) (hi n a)).indicator (1 : ℝ → ℝ) t)
        (volume.restrict (Set.Ioc (-1 : ℝ) 1)) :=
      fun a _ => (integrable_const (1 : ℝ)).indicator measurableSet_Ioc
    rw [show (fun t => f t) = fun t => ∑ a ∈ A,
        (Set.Ioc (lo n a) (hi n a)).indicator (1 : ℝ → ℝ) t from funext hfsum,
      integral_finsetSum _ hint, Finset.sum_congr rfl hcell, Finset.sum_const, hAn,
      nsmul_eq_mul]
    field_simp
  · intro x
    rw [intervalIntegral.integral_of_le (by norm_num)]
    let S : ℤ × ℤ → Set ℝ := fun p =>
      Set.Ioc (max (lo n p.1) (lo n p.2 - x)) (min (hi n p.1) (hi n p.2 - x))
    let F : ℝ → ℝ := fun t => (∑ p ∈ A ×ˢ B, (S p).indicator (1 : ℝ → ℝ) t) +
      ({-1 - x} : Set ℝ).indicator (1 : ℝ → ℝ) t
    have hF0 : ∀ t, 0 ≤ F t := by
      intro t
      refine add_nonneg (Finset.sum_nonneg fun p _ => ?_) ?_ <;>
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hSi : ∀ p : ℤ × ℤ, Integrable (fun t => (S p).indicator (1 : ℝ → ℝ) t) := fun p =>
      (integrableOn_const (by simp [S])).integrable_indicator measurableSet_Ioc
    have hPi : Integrable (fun t => ({-1 - x} : Set ℝ).indicator (1 : ℝ → ℝ) t) :=
      (integrableOn_const (by simp)).integrable_indicator (measurableSet_singleton _)
    have hFi : Integrable F := (integrable_finsetSum _ fun p _ => hSi p).add hPi
    have hpt : ∀ t, f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t) ≤ F t := by
      intro t
      by_cases hft : ⌈(n : ℝ) * (t + 1)⌉ ∈ A
      · have hf1 : f t = 1 := if_pos hft
        rw [hf1, one_mul]
        by_cases hmem : x + t ∈ Set.Icc (-1 : ℝ) 1
        · rw [Set.indicator_of_mem hmem]
          by_cases hfx : ⌈(n : ℝ) * (x + t + 1)⌉ ∈ A
          · have : f (x + t) = 1 := if_pos hfx
            rw [this, sub_self]
            exact hF0 t
          · have : f (x + t) = 0 := if_neg hfx
            rw [this, sub_zero]
            by_cases hend : x + t = -1
            · have h1 : t ∈ ({-1 - x} : Set ℝ) := by
                rw [Set.mem_singleton_iff]
                linarith
              have h2 : (1 : ℝ) ≤ ({-1 - x} : Set ℝ).indicator (1 : ℝ → ℝ) t := by
                rw [Set.indicator_of_mem h1]
                rfl
              have h3 : 0 ≤ ∑ p ∈ A ×ˢ B, (S p).indicator (1 : ℝ → ℝ) t :=
                Finset.sum_nonneg fun p _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
              simp only [F]
              linarith
            · have hlt : -1 < x + t := lt_of_le_of_ne hmem.1 (Ne.symm hend)
              have hb1 : 1 ≤ ⌈(n : ℝ) * (x + t + 1)⌉ := by
                have : (0 : ℝ) < (n : ℝ) * (x + t + 1) := mul_pos hN (by linarith)
                exact Int.one_le_ceil_iff.mpr this
              have hb2 : ⌈(n : ℝ) * (x + t + 1)⌉ ≤ 2 * (n : ℤ) := by
                rw [Int.ceil_le]
                push_cast
                nlinarith [hmem.2]
              have hbB : ⌈(n : ℝ) * (x + t + 1)⌉ ∈ B := by
                have h1 : ⌈(n : ℝ) * (x + t + 1)⌉ ∈ A ∪ B := by
                  rw [hu]
                  exact Finset.mem_Icc.mpr ⟨hb1, hb2⟩
                rcases Finset.mem_union.mp h1 with h | h
                · exact absurd h hfx
                · exact h
              have hp : (⌈(n : ℝ) * (t + 1)⌉, ⌈(n : ℝ) * (x + t + 1)⌉) ∈ A ×ˢ B :=
                Finset.mem_product.mpr ⟨hft, hbB⟩
              have hta := (ceil_eq_iff_mem hn _ t).mp rfl
              have htb := (ceil_eq_iff_mem hn _ (x + t)).mp rfl
              have hmemS : t ∈ S (⌈(n : ℝ) * (t + 1)⌉, ⌈(n : ℝ) * (x + t + 1)⌉) := by
                simp only [S, Set.mem_Ioc, max_lt_iff, le_min_iff]
                refine ⟨⟨hta.1, ?_⟩, hta.2, ?_⟩
                · linarith [htb.1]
                · linarith [htb.2]
              have h2 : (1 : ℝ) ≤ ∑ p ∈ A ×ˢ B, (S p).indicator (1 : ℝ → ℝ) t := by
                have h3 := Finset.single_le_sum
                  (f := fun p => (S p).indicator (1 : ℝ → ℝ) t)
                  (fun p _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _) hp
                rw [Set.indicator_of_mem hmemS] at h3
                exact h3
              have h4 : 0 ≤ ({-1 - x} : Set ℝ).indicator (1 : ℝ → ℝ) t :=
                Set.indicator_nonneg (fun _ _ => zero_le_one) _
              simp only [F]
              linarith
        · rw [Set.indicator_of_notMem hmem]
          exact hF0 t
      · have hf0 : f t = 0 := if_neg hft
        rw [hf0, zero_mul]
        exact hF0 t
    have hnn : ∀ t, 0 ≤ f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t) := by
      intro t
      refine mul_nonneg (hf01 t).1 (Set.indicator_nonneg (fun y _ => ?_) _)
      linarith [(hf01 y).2]
    calc ∫ t in Set.Ioc (-1 : ℝ) 1,
          f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t)
        ≤ ∫ t in Set.Ioc (-1 : ℝ) 1, F t :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) hFi.integrableOn
            (Filter.Eventually.of_forall hpt)
      _ ≤ ∫ t, F t := setIntegral_le_integral hFi (Filter.Eventually.of_forall hF0)
      _ = ∑ p ∈ A ×ˢ B, volume.real (S p) + volume.real ({-1 - x} : Set ℝ) := by
          simp only [F]
          rw [integral_add (integrable_finsetSum _ fun p _ => hSi p) hPi,
            integral_finsetSum _ (fun p _ => hSi p),
            integral_indicator_one (measurableSet_singleton _)]
          congr 1
          exact Finset.sum_congr rfl fun p _ => integral_indicator_one measurableSet_Ioc
      _ = (∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - n * x|)) / n := by
          have hs0 : volume.real ({-1 - x} : Set ℝ) = 0 := by
            rw [measureReal_def, Real.volume_singleton, ENNReal.toReal_zero]
          rw [hs0, add_zero, Finset.sum_div]
          exact Finset.sum_congr rfl fun p _ =>
            Real.volume_real_Ioc.trans (tent_eq hn p.1 p.2 x)
