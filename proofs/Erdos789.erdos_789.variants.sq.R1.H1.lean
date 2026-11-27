import OMAReductions.R_Erdos789_erdos_789_variants_sq_R1
import Mathlib

/-! Straus's bound h(n) = O(sqrt n): summing the sizes of disjoint subset-sum layers.

Credit: this hypothesis is word for word the solved catalogue variant
Erdos789.erdos_789.variants.isBigO_sq, and this file reuses, unchanged, the merged proof of
that variant by @Genbox (pull request 84 of open-math-agents). Only the header of the final
theorem was adapted. -/

open Erdos789 Filter
open scoped Asymptotics

def OMA.straus_layer (B : Finset ℤ) (k : ℕ) : Finset ℤ :=
  (B.powersetCard k).image fun T => ∑ x ∈ T, x

lemma OMA.straus_layer_mono {B C : Finset ℤ} (h : B ⊆ C) (k : ℕ) :
    OMA.straus_layer B k ⊆ OMA.straus_layer C k := by
  intro z hz
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hTB, hk⟩ := Finset.mem_powersetCard.mp hT
  exact Finset.mem_image.mpr ⟨T, Finset.mem_powersetCard.mpr ⟨hTB.trans h, hk⟩, rfl⟩

lemma OMA.straus_layer_lower (B : Finset ℤ) (k : ℕ) (hk : k ≤ B.card) :
    k * (B.card - k) + 1 ≤ (OMA.straus_layer B k).card := by
  induction B using Finset.strongInductionOn generalizing k with
  | _ B ih =>
    by_cases heq : k = B.card
    · have hne : (OMA.straus_layer B k).Nonempty :=
        ⟨∑ x ∈ B, x, Finset.mem_image.mpr
          ⟨B, Finset.mem_powersetCard.mpr ⟨by rfl, heq.symm⟩, rfl⟩⟩
      have hpos := Finset.card_pos.mpr hne
      rw [heq, Nat.sub_self, mul_zero, zero_add]
      rw [heq] at hpos
      exact hpos
    · have hne : B.Nonempty := Finset.card_pos.mp (by omega)
      let x := B.max' hne
      have hx : x ∈ B := B.max'_mem hne
      let C := B.erase x
      have hc_lt : C ⊂ B := Finset.erase_ssubset hx
      have hc : C ⊆ B := Finset.erase_subset _ _
      have hcard : C.card + 1 = B.card := Finset.card_erase_add_one hx
      have hk' : k ≤ C.card := by omega
      have hTne : (C.powersetCard k).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_powersetCard]
        exact Nat.choose_pos hk'
      obtain ⟨T, hT, hTmax⟩ := Finset.exists_max_image (C.powersetCard k)
        (fun U => ∑ z ∈ U, z) hTne
      obtain ⟨hTC, hTk⟩ := Finset.mem_powersetCard.mp hT
      let D := T.image fun y => (∑ z ∈ T, z) + x - y
      have hDcard : D.card = k := by
        rw [show D.card = T.card from Finset.card_image_of_injective _ (by
          intro a b h
          dsimp at h
          linarith), hTk]
      have hDsub : D ⊆ OMA.straus_layer B k := by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
        have hxT : x ∉ T := by
          intro hxT
          exact (Finset.mem_erase.mp (hTC hxT)).1 rfl
        have hxU : x ∉ T.erase y := fun h => hxT (Finset.mem_of_mem_erase h)
        have hUcard : (insert x (T.erase y)).card = k := by
          rw [Finset.card_insert_of_notMem hxU, Finset.card_erase_add_one hy, hTk]
        have hUsub : insert x (T.erase y) ⊆ B :=
          Finset.insert_subset hx ((Finset.erase_subset _ _).trans (hTC.trans hc))
        have hUsum : (∑ z ∈ insert x (T.erase y), z) = (∑ z ∈ T, z) + x - y := by
          rw [Finset.sum_insert hxU]
          have he := Finset.sum_erase_add T (fun z : ℤ => z) hy
          linarith
        exact Finset.mem_image.mpr
          ⟨insert x (T.erase y), Finset.mem_powersetCard.mpr ⟨hUsub, hUcard⟩, hUsum⟩
      have hdis : Disjoint (OMA.straus_layer C k) D := by
        apply Finset.disjoint_left.mpr
        intro z hz hDz
        obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hDz
        obtain ⟨hyx, hyB⟩ := Finset.mem_erase.mp (hTC hy)
        have hy_lt : y < x := lt_of_le_of_ne (B.le_max' _ hyB) hyx
        have hu := hTmax U hU
        linarith
      have hsum := Finset.card_le_card
        (Finset.union_subset (OMA.straus_layer_mono hc k) hDsub)
      rw [Finset.card_union_of_disjoint hdis, hDcard] at hsum
      have hind := ih C hc_lt k hk'
      rw [show B.card - k = (C.card - k) + 1 by omega, Nat.mul_add, Nat.mul_one]
      omega

lemma OMA.straus_sums_disjoint (B : Finset ℤ)
    (hB : ∀ T ⊆ B, ∀ S ⊆ B, S.Nonempty → T.Nonempty →
      (∑ a ∈ T, a) = ∑ b ∈ S, b → T.card = S.card) :
    ((Finset.range B.card : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun k => OMA.straus_layer B (k + 1)) := by
  intro j _ k _ hjk
  apply Finset.disjoint_left.mpr
  intro z hzj hzk
  obtain ⟨T, hT, hj⟩ := Finset.mem_image.mp hzj
  obtain ⟨S, hS, hk⟩ := Finset.mem_image.mp hzk
  obtain ⟨hTB, hTcard⟩ := Finset.mem_powersetCard.mp hT
  obtain ⟨hSB, hScard⟩ := Finset.mem_powersetCard.mp hS
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hc := hB T hTB S hSB hSne hTne (hj.trans hk.symm)
  omega

lemma OMA.straus_sums_interval (n : ℕ) (B : Finset ℤ)
    (hBA : B ⊆ Finset.Icc (1 : ℤ) (n : ℤ)) :
    (Finset.range B.card).biUnion (fun k => OMA.straus_layer B (k + 1)) ⊆
      Finset.Icc (1 : ℤ) ((B.card : ℤ) * (n : ℤ)) := by
  intro z hz
  obtain ⟨k, hk, hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨hTB, hTcard⟩ := Finset.mem_powersetCard.mp hT
  have hlow : (T.card : ℤ) ≤ ∑ x ∈ T, x := by
    simpa using (Finset.sum_le_sum fun x hx => (Finset.mem_Icc.mp (hBA (hTB hx))).1)
  have hhigh : (∑ x ∈ T, x) ≤ (T.card : ℤ) * (n : ℤ) := by
    simpa using (Finset.sum_le_sum fun x hx => (Finset.mem_Icc.mp (hBA (hTB hx))).2)
  have hTle : (T.card : ℤ) ≤ (B.card : ℤ) := by exact_mod_cast Finset.card_le_card hTB
  exact Finset.mem_Icc.mpr ⟨by omega,
    hhigh.trans (mul_le_mul_of_nonneg_right hTle (by positivity))⟩

lemma OMA.straus_telescope (m : ℕ) :
    (6 : ℝ) * (∑ k ∈ Finset.range m,
      ((k + 1 : ℕ) : ℝ) * ((m : ℝ) - ((k + 1 : ℕ) : ℝ))) =
      (m : ℝ) * ((m : ℝ) ^ 2 - 1) := by
  let F (j : ℕ) : ℝ := (j : ℝ) * ((j : ℝ) + 1) * (3 * (m : ℝ) - 2 * (j : ℝ) - 1)
  rw [Finset.mul_sum]
  calc
    (∑ k ∈ Finset.range m, (6 : ℝ) * (((k + 1 : ℕ) : ℝ) * ((m : ℝ) - ((k + 1 : ℕ) : ℝ)))) =
        ∑ k ∈ Finset.range m, (F (k + 1) - F k) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp [F]
      push_cast
      ring
    _ = F m - F 0 := Finset.sum_range_sub F m
    _ = _ := by dsimp [F]; ring

lemma OMA.straus_attained (n : ℕ) :
    IsSubsetSumSeparatingCard n (subsetSumThreshold n) := by
  change sSup {m | IsSubsetSumSeparatingCard n m} ∈ {m | IsSubsetSumSeparatingCard n m}
  apply Nat.sSup_mem
  · refine ⟨0, ?_⟩
    intro A _
    refine ⟨∅, Finset.empty_subset _, Nat.zero_le _, ?_⟩
    intro T hT S hS _ _ _
    have heT := Finset.subset_empty.mp hT
    have heS := Finset.subset_empty.mp hS
    rw [heT, heS]
  · refine ⟨n, ?_⟩
    intro m hm
    obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℤ n
    obtain ⟨B, hBA, hcard, _⟩ := hm A hA
    exact hcard.trans ((Finset.card_le_card hBA).trans_eq hA)

theorem OMA.solution : OMA.R_Erdos789_erdos_789_variants_sq_R1.H1 := by
  unfold OMA.R_Erdos789_erdos_789_variants_sq_R1.H1
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨3, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  let A := Finset.Icc (1 : ℤ) (n : ℤ)
  have hA : A.card = n := by simp [A, Int.card_Icc]
  obtain ⟨B, hBA, hm, hB⟩ := OMA.straus_attained n A hA
  let m := B.card
  have hthreshold : (subsetSumThreshold n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  refine hthreshold.trans ?_
  by_cases hm0 : m = 0
  · rw [hm0, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hcap := Finset.card_le_card (OMA.straus_sums_interval n B hBA)
  rw [Finset.card_biUnion (OMA.straus_sums_disjoint B hB)] at hcap
  have hIcc : (Finset.Icc (1 : ℤ) ((m : ℤ) * (n : ℤ))).card = m * n := by
    rw [Int.card_Icc, add_sub_cancel_right, ← Int.natCast_mul, Int.toNat_natCast]
  rw [hIcc] at hcap
  have hcap' : (∑ k ∈ Finset.range m, ((OMA.straus_layer B (k + 1)).card : ℝ)) ≤
      (m : ℝ) * (n : ℝ) := by exact_mod_cast hcap
  have hlow : (∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * ((m : ℝ) - ((k + 1 : ℕ) : ℝ))) ≤
      ∑ k ∈ Finset.range m, ((OMA.straus_layer B (k + 1)).card : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k + 1 ≤ m := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hb := OMA.straus_layer_lower B (k + 1) hkm
    have hc : (k + 1) * (m - (k + 1)) ≤ (OMA.straus_layer B (k + 1)).card := by
      change (k + 1) * (m - (k + 1)) + 1 ≤ _ at hb
      omega
    have hc' : (((k + 1) * (m - (k + 1)) : ℕ) : ℝ) ≤ ((OMA.straus_layer B (k + 1)).card : ℝ) := by
      exact_mod_cast hc
    rw [Nat.cast_mul, Nat.cast_sub hkm] at hc'
    exact hc'
  have hbig := mul_le_mul_of_nonneg_left (hlow.trans hcap') (show (0 : ℝ) ≤ 6 by norm_num)
  rw [OMA.straus_telescope] at hbig
  have hsmall : (m : ℝ) ^ 2 - 1 ≤ 6 * (n : ℝ) := by
    apply (mul_le_mul_iff_left₀ hmpos).mp
    calc
      ((m : ℝ) ^ 2 - 1) * (m : ℝ) = (m : ℝ) * ((m : ℝ) ^ 2 - 1) := by ring
      _ ≤ 6 * ((m : ℝ) * (n : ℝ)) := hbig
      _ = 6 * (n : ℝ) * (m : ℝ) := by ring
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  apply (sq_le_sq₀ hmpos.le (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  linarith only [hsmall, hn']