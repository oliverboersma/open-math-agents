import FormalConjectures.ErdosProblems.«357»

-- Problem: Erdős Problem 357, monotone parts ii, littleO version (it asks for a value).
-- Credit: @marcusbuffett (solver of record on Left to Solve).
--
-- PORT OF A PUBLIC PROOF, not a new result. Answer: n ↦ √n / log n, just below the known
-- lower-bound order f(n) ≥ (2+o(1))√n (Weisenberg). The ported part is √n = O(f(n)); the step
-- √n / log n = o(√n) and the assembly are new here. Distinct single-term sums force the a_i
-- to be distinct, so monotone sequences are strictly increasing here and h = f.
-- Sources, both by KitaKen1 (GitHub), Apache License 2.0:
--   github.com/KitaKen1/erdos-357-sqrt-lower-bound, commit bd84e6d71644092228b6962439db2d9d582302f9,
--     file lean/Erdos357BigOLowerBoundFC.lean (the tail construction and sqrt_isBigO_f);
--   github.com/KitaKen1/erdos-357-additional-targets, commit 9991e654ca3364601c174f476ddacd422e3c8d67,
--     file lean/Erdos357AdditionalTargetsFC.lean (the bridge h = f).
-- Copyright KitaKen1. Licensed under the Apache License, Version 2.0; you may not use this file
-- except in compliance with the License. You may obtain a copy of the License at
-- https://www.apache.org/licenses/LICENSE-2.0 . Distributed on an AS IS BASIS, WITHOUT
-- WARRANTIES OR CONDITIONS OF ANY KIND. Changes here: merged into one file, renamed the
-- namespace, removed the noncomputable section and the #check / #print lines, and stated the
-- result in the OMA.answer form.

namespace OMA.E357

open scoped BigOperators
open Finset Filter Asymptotics

lemma two_mul_sum_range_int (n : ℕ) :
    2 * (∑ i ∈ range n, (i : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

lemma two_mul_sum_Icc_int (l u : ℕ) (h : l ≤ u) :
    2 * (∑ i ∈ Icc l u, (i : ℤ)) =
      ((u : ℤ) + 1) * (u : ℤ) - (l : ℤ) * ((l : ℤ) - 1) := by
  rw [← Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sub (fun i : ℕ ↦ (i : ℤ)) (by omega : l ≤ u + 1)]
  rw [mul_sub, two_mul_sum_range_int, two_mul_sum_range_int]
  push_cast
  ring

lemma ordConnected_finset_eq_of_card_eq_sum_val_eq {k : ℕ} {J K : Finset (Fin k)}
    (hJ : (J : Set (Fin k)).OrdConnected)
    (hK : (K : Set (Fin k)).OrdConnected)
    (hcard : J.card = K.card)
    (hsum : (∑ i ∈ J, (i : ℤ)) = ∑ i ∈ K, (i : ℤ)) :
    J = K := by
  by_cases hJe : J = ∅
  · subst J
    exact (Finset.card_eq_zero.mp hcard.symm).symm
  have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJe
  have hKne : K.Nonempty := by
    rw [← Finset.card_pos, ← hcard, Finset.card_pos]
    exact hJne
  letI : NeZero k := ⟨by
    intro hk
    obtain ⟨j, _⟩ := hJne
    subst k
    exact Fin.elim0 j⟩
  let jl := J.min' hJne
  let ju := J.max' hJne
  let kl := K.min' hKne
  let ku := K.max' hKne
  have hJset : (J : Set (Fin k)) = Set.Icc jl ju := by
    simpa [jl, ju, hJne.csInf_eq_min', hJne.csSup_eq_max'] using
      (Finset.coe_nonempty.mpr hJne).ordConnected_iff_of_bdd'.mp hJ
  have hKset : (K : Set (Fin k)) = Set.Icc kl ku := by
    simpa [kl, ku, hKne.csInf_eq_min', hKne.csSup_eq_max'] using
      (Finset.coe_nonempty.mpr hKne).ordConnected_iff_of_bdd'.mp hK
  have hJfin : J = Icc jl ju := by
    apply Finset.coe_injective
    simpa using hJset
  have hKfin : K = Icc kl ku := by
    apply Finset.coe_injective
    simpa using hKset
  have hjle : (jl : ℕ) ≤ ju := Finset.min'_le_max' J hJne
  have hkle : (kl : ℕ) ≤ ku := Finset.min'_le_max' K hKne
  have hlen : (ju : ℕ) + 1 - jl = (ku : ℕ) + 1 - kl := by
    simpa [hJfin, hKfin, Fin.card_Icc] using hcard
  have hsum' : (∑ i ∈ Icc (jl : ℕ) (ju : ℕ), (i : ℤ)) =
      ∑ i ∈ Icc (kl : ℕ) (ku : ℕ), (i : ℤ) := by
    calc
      (∑ i ∈ Icc (jl : ℕ) (ju : ℕ), (i : ℤ)) =
          ∑ i ∈ Icc jl ju, ((i : ℕ) : ℤ) := by
            rw [← Fin.map_valEmbedding_Icc, Finset.sum_map]
            rfl
      _ = ∑ i ∈ Icc kl ku, ((i : ℕ) : ℤ) := by
        simpa [hJfin, hKfin] using hsum
      _ = ∑ i ∈ Icc (kl : ℕ) (ku : ℕ), (i : ℤ) := by
        rw [← Fin.map_valEmbedding_Icc, Finset.sum_map]
        rfl
  have htwoJ := two_mul_sum_Icc_int (jl : ℕ) (ju : ℕ) hjle
  have htwoK := two_mul_sum_Icc_int (kl : ℕ) (ku : ℕ) hkle
  have hjl : (jl : ℕ) = kl := by
    have hlenZ : ((ju : ℕ) + 1 : ℤ) - (jl : ℕ) =
        ((ku : ℕ) + 1 : ℤ) - (kl : ℕ) := by
      omega
    have hposZ : 0 < ((ju : ℕ) + 1 : ℤ) - (jl : ℕ) := by omega
    rw [hsum'] at htwoJ
    nlinarith
  have hju : (ju : ℕ) = ku := by omega
  have hjlFin : jl = kl := Fin.ext hjl
  have hjuFin : ju = ku := Fin.ext hju
  simpa [hJfin, hKfin, hjlFin, hjuFin]

def tailSequence (n : ℕ) (i : Fin n.sqrt) : ℤ :=
  (n : ℤ) - (n.sqrt : ℤ) + 1 + (i : ℕ)

lemma tailSequence_mem_Icc (n : ℕ) :
    Set.range (tailSequence n) ⊆ Set.Icc (1 : ℤ) n := by
  rintro _ ⟨i, rfl⟩
  constructor
  · simp only [tailSequence]
    have hsqrt : n.sqrt ≤ n := Nat.sqrt_le_self n
    omega
  · simp only [tailSequence]
    have hi : (i : ℕ) < n.sqrt := i.isLt
    omega

lemma tailSequence_strictMono (n : ℕ) : StrictMono (tailSequence n) := by
  intro i j hij
  simp only [tailSequence]
  have hij' : (i : ℕ) < j := by simpa using hij
  omega

lemma tailSequence_hasDistinctSums (n : ℕ) :
    Erdos357.HasDistinctSums (tailSequence n) := by
  intro J hJ K hK hsum
  have hcard_le (L : Finset (Fin n.sqrt)) : L.card ≤ n.sqrt := by
    simpa using Finset.card_le_card (Finset.subset_univ L)
  have hupper (L : Finset (Fin n.sqrt)) :
      (∑ i ∈ L, tailSequence n i) ≤ (L.card : ℤ) * n := by
    calc
      (∑ i ∈ L, tailSequence n i) ≤ ∑ _i ∈ L, (n : ℤ) := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [tailSequence]
        have hil : (i : ℕ) < n.sqrt := i.isLt
        omega
      _ = (L.card : ℤ) * n := by simp
  have hlower (L : Finset (Fin n.sqrt)) :
      (L.card : ℤ) * ((n : ℤ) - n.sqrt + 1) ≤ ∑ i ∈ L, tailSequence n i := by
    calc
      (L.card : ℤ) * ((n : ℤ) - n.sqrt + 1) =
          ∑ _i ∈ L, ((n : ℤ) - n.sqrt + 1) := by simp
      _ ≤ ∑ i ∈ L, tailSequence n i := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [tailSequence]
        omega
  have hcard : J.card = K.card := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hJK | hKJ
    · have hsep : (J.card : ℤ) * n <
          (K.card : ℤ) * ((n : ℤ) - n.sqrt + 1) := by
        have hj : (J.card : ℤ) + 1 ≤ K.card := by exact_mod_cast hJK
        have hk : (K.card : ℤ) ≤ n.sqrt := by exact_mod_cast hcard_le K
        have hsqrt : n.sqrt * n.sqrt ≤ n := Nat.sqrt_le n
        have hsqrtZ : (n.sqrt : ℤ) * n.sqrt ≤ n := by exact_mod_cast hsqrt
        have hn : (0 : ℤ) ≤ n := by positivity
        have hr : (0 : ℤ) ≤ n.sqrt := by positivity
        nlinarith
      have := (hupper J).trans_lt (hsep.trans_le (hlower K))
      exact (ne_of_lt this) hsum
    · have hsep : (K.card : ℤ) * n <
          (J.card : ℤ) * ((n : ℤ) - n.sqrt + 1) := by
        have hk : (K.card : ℤ) + 1 ≤ J.card := by exact_mod_cast hKJ
        have hj : (J.card : ℤ) ≤ n.sqrt := by exact_mod_cast hcard_le J
        have hsqrt : n.sqrt * n.sqrt ≤ n := Nat.sqrt_le n
        have hsqrtZ : (n.sqrt : ℤ) * n.sqrt ≤ n := by exact_mod_cast hsqrt
        have hn : (0 : ℤ) ≤ n := by positivity
        have hr : (0 : ℤ) ≤ n.sqrt := by positivity
        nlinarith
      have := (hupper K).trans_lt (hsep.trans_le (hlower J))
      exact (ne_of_lt this) hsum.symm
  have hsumVal : (∑ i ∈ J, ((i : ℕ) : ℤ)) = ∑ i ∈ K, ((i : ℕ) : ℤ) := by
    simp only [tailSequence, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul] at hsum
    rw [hcard] at hsum
    linarith
  exact ordConnected_finset_eq_of_card_eq_sum_val_eq hJ hK hcard hsumVal

lemma sqrt_le_f (n : ℕ) : n.sqrt ≤ Erdos357.f n := by
  let S : Set ℕ := {k : ℕ | ∃ a : Fin k → ℤ,
    Set.range a ⊆ Set.Icc 1 n ∧ StrictMono a ∧ Erdos357.HasDistinctSums a}
  have hsqrt_mem : n.sqrt ∈ S := by
    exact ⟨tailSequence n, tailSequence_mem_Icc n, tailSequence_strictMono n,
      tailSequence_hasDistinctSums n⟩
  have hS_bdd : BddAbove S := by
    refine ⟨n, ?_⟩
    rintro k ⟨a, haRange, haMono, _⟩
    have hsub : Finset.univ.image a ⊆ Finset.Icc (1 : ℤ) n := by
      intro z hz
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
      obtain ⟨i, rfl⟩ := hz
      rw [Finset.mem_Icc]
      exact haRange ⟨i, rfl⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ haMono.injective] at hc
    simpa [Int.card_Icc] using hc
  change n.sqrt ≤ sSup S
  exact le_csSup hS_bdd hsqrt_mem

theorem sqrt_isBigO_f :
    (fun n : ℕ ↦ √(n : ℝ)) =O[atTop] (fun n ↦ (Erdos357.f n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 2
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hsqrtPos : 0 < n.sqrt := Nat.sqrt_pos.mpr hn
  have hsqrtLt : √(n : ℝ) < (n.sqrt : ℝ) + 1 := by
    apply (Real.sqrt_lt' (by positivity)).2
    have hsqrtSq : n < (n.sqrt + 1) ^ 2 := by
      simpa [pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n
    exact_mod_cast hsqrtSq
  have hbound : √(n : ℝ) ≤ 2 * (Erdos357.f n : ℝ) := by
    have hf := sqrt_le_f n
    have hfR : (n.sqrt : ℝ) ≤ Erdos357.f n := by exact_mod_cast hf
    have hsqrtPosR : (1 : ℝ) ≤ n.sqrt := by exact_mod_cast hsqrtPos
    nlinarith
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (n : ℝ))] using hbound


theorem sqrt_div_log_isLittleO_sqrt :
    (fun n : ℕ ↦ √(n : ℝ) / Real.log (n : ℝ)) =o[atTop] (fun n : ℕ ↦ √(n : ℝ)) := by
  have hlog : Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have h1 : (fun n : ℕ ↦ (Real.log (n : ℝ))⁻¹) =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 hlog
  have h2 := (isBigO_refl (fun n : ℕ ↦ √(n : ℝ)) atTop).mul_isLittleO h1
  simpa [div_eq_mul_inv] using h2

theorem answer_isLittleO_f :
    (fun n : ℕ ↦ √(n : ℝ) / Real.log (n : ℝ)) =o[atTop] (fun n ↦ (Erdos357.f n : ℝ)) :=
  sqrt_div_log_isLittleO_sqrt.trans_isBigO sqrt_isBigO_f

lemma hasDistinctSums_injective {k : ℕ} {a : Fin k → ℤ}
    (ha : Erdos357.HasDistinctSums a) : Function.Injective a := by
  intro i j hij
  apply Finset.singleton_injective
  apply ha
  · simpa using (Set.ordConnected_singleton : Set.OrdConnected ({i} : Set (Fin k)))
  · simpa using (Set.ordConnected_singleton : Set.OrdConnected ({j} : Set (Fin k)))
  · simp [hij]

lemma strictMono_of_monotone_of_hasDistinctSums {k : ℕ} {a : Fin k → ℤ}
    (hmono : Monotone a) (hsums : Erdos357.HasDistinctSums a) : StrictMono a :=
  hmono.strictMono_of_injective (hasDistinctSums_injective hsums)

lemma h_eq_f (n : ℕ) : Erdos357.h n = Erdos357.f n := by
  unfold Erdos357.h Erdos357.f
  apply congrArg sSup
  ext k
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, hrange, hmono, hsums⟩
    exact ⟨a, hrange, strictMono_of_monotone_of_hasDistinctSums hmono hsums, hsums⟩
  · rintro ⟨a, hrange, hstrict, hsums⟩
    exact ⟨a, hrange, hstrict.monotone, hsums⟩

theorem answer_isLittleO_h :
    (fun n : ℕ ↦ √(n : ℝ) / Real.log (n : ℝ)) =o[atTop] (fun n ↦ (Erdos357.h n : ℝ)) := by
  simpa only [h_eq_f] using answer_isLittleO_f

end OMA.E357

noncomputable def OMA.answer : ℕ → ℝ := fun n ↦ √(n : ℝ) / Real.log (n : ℝ)

theorem OMA.solution : Erdos357.erdos_357.variants.monotone.parts.ii.littleO_version.answer = OMA.answer → type_of% @Erdos357.erdos_357.variants.monotone.parts.ii.littleO_version := by
  intro h
  rw [h]
  exact OMA.E357.answer_isLittleO_h
