import OMAReductions.R_Erdos145_erdos_145_variants_le_three_R1
import Mathlib

/-! The finite-period sieve and truncated quadratic moment lemmas below are
adapted from @marcusbuffett's merged proof of Erdos489.erdos_489.variants.squarefree,
PR 2102. Its general sieve-gap argument is by Colin Snyder and contributors,
williamjblair/lean-proofs, commit 4f915a323443bfb1709a6805a013812016dca88a.
The conversion to squarefree gaps indexed by a real upper endpoint is new. -/
namespace SquarefreeGapProof
open Filter Finset Asymptotics Classical
open scoped Topology BigOperators NNReal
theorem tendsto_tsum_nat_add_zero
    (f : ℕ → ℝ) (hf : Summable f) :
    Tendsto (fun R : ℕ => ∑' n : ℕ, f (n + R)) atTop (𝓝 0) := by
  have hpartial := hf.tendsto_sum_tsum_nat
  have hsub : Tendsto
      (fun R : ℕ => (∑' n, f n) - ∑ n ∈ Finset.range R, f n)
      atTop (𝓝 ((∑' n, f n) - ∑' n, f n)) :=
    tendsto_const_nhds.sub hpartial
  have heq : ∀ R : ℕ,
      (∑' n : ℕ, f (n + R)) =
        (∑' n, f n) - ∑ n ∈ Finset.range R, f n := by
    intro R
    have h := hf.sum_add_tsum_nat_add R
    linarith
  simpa only [heq, sub_self] using hsub

theorem eventually_finset_tail_sum_le_of_summable
    (f : ℕ → ℝ) (hf : Summable f) (hf0 : ∀ n, 0 ≤ f n)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop, ∀ T : Finset ℕ,
      (∀ r ∈ T, R ≤ r) → (∑ r ∈ T, f r) ≤ ε := by
  have htend := tendsto_tsum_nat_add_zero f hf
  have hev : ∀ᶠ R : ℕ in atTop, (∑' n : ℕ, f (n + R)) < ε :=
    (tendsto_order.1 htend).2 ε hε
  filter_upwards [hev] with R hR
  intro T hTR
  let U := T.image fun r => r - R
  have hinj : Set.InjOn (fun r => r - R) (T : Set ℕ) := by
    intro r hr s hs hrs
    have hrR := hTR r hr
    have hsR := hTR s hs
    calc
      r = (r - R) + R := (Nat.sub_add_cancel hrR).symm
      _ = (s - R) + R := congrArg (fun n => n + R) hrs
      _ = s := Nat.sub_add_cancel hsR
  have hsum : (∑ n ∈ U, f (n + R)) = ∑ r ∈ T, f r := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.sub_add_cancel (hTR r hr)]
  have hshift : Summable (fun n => f (n + R)) :=
    (summable_nat_add_iff R).2 hf
  have hle : (∑ n ∈ U, f (n + R)) ≤ ∑' n : ℕ, f (n + R) :=
    hshift.sum_le_tsum U (fun n hn => hf0 (n + R))
  rw [hsum] at hle
  exact hle.trans hR.le

lemma avoidList_periodic (l : List ℕ) :
    Function.Periodic (fun n : ℕ => ∀ a ∈ l, ¬ a ∣ n) l.prod := by
  intro n
  apply propext
  constructor
  · intro hn a ha han
    apply hn a ha
    exact (Nat.dvd_add_iff_left (List.dvd_prod ha)).1 han
  · intro hn a ha han
    apply hn a ha
    exact (Nat.dvd_add_iff_left (List.dvd_prod ha)).2 han

noncomputable def divisorWitness (p : ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ a, p a ∧ a ∣ n then Classical.choose h else 0

noncomputable def divisorWitnessRank (p : ℕ → Prop) [DecidablePred p]
    (n : ℕ) : ℕ :=
  Nat.count p (divisorWitness p n)

theorem divisorWitness_spec (p : ℕ → Prop) (n : ℕ)
    (h : ∃ a, p a ∧ a ∣ n) :
    p (divisorWitness p n) ∧ divisorWitness p n ∣ n := by
  rw [divisorWitness, dif_pos h]
  exact Classical.choose_spec h

theorem nth_divisorWitnessRank (p : ℕ → Prop) [DecidablePred p]
    (n : ℕ) (h : ∃ a, p a ∧ a ∣ n) :
    Nat.nth p (divisorWitnessRank p n) = divisorWitness p n := by
  exact Nat.nth_count (divisorWitness_spec p n h).1

theorem nth_divisorWitnessRank_dvd (p : ℕ → Prop) [DecidablePred p]
    (n : ℕ) (h : ∃ a, p a ∧ a ∣ n) :
    Nat.nth p (divisorWitnessRank p n) ∣ n := by
  rw [nth_divisorWitnessRank p n h]
  exact (divisorWitness_spec p n h).2

theorem le_divisorWitnessRank_of_avoid_prefix
    (p : ℕ → Prop) [DecidablePred p] (n R : ℕ)
    (hcov : ∃ a, p a ∧ a ∣ n)
    (havoid : ∀ a ∈ (List.range R).map (Nat.nth p), ¬a ∣ n) :
    R ≤ divisorWitnessRank p n := by
  by_contra hnot
  have hr : divisorWitnessRank p n < R := by omega
  apply havoid (Nat.nth p (divisorWitnessRank p n))
  · exact List.mem_map.mpr ⟨divisorWitnessRank p n,
      List.mem_range.mpr hr, rfl⟩
  · exact nth_divisorWitnessRank_dvd p n hcov

def multiplesIn (S : Finset ℕ) (d : ℕ) : Finset ℕ :=
  S.filter fun n => d ∣ n

theorem multiplesIn_interval_card_le
    (S : Finset ℕ) (L G p : ℕ) (hp : 0 < p)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G) :
    (multiplesIn S p).card ≤ G / p + 1 := by
  let M := multiplesIn S p
  let f : ℕ → ℕ := fun n => (n - L) / p
  have hinj : Set.InjOn f (M : Set ℕ) := by
    intro x hx y hy heq
    have hxS : x ∈ S := (Finset.mem_filter.mp hx).1
    have hyS : y ∈ S := (Finset.mem_filter.mp hy).1
    have hpx : p ∣ x := (Finset.mem_filter.mp hx).2
    have hpy : p ∣ y := (Finset.mem_filter.mp hy).2
    have hxL := (hinterval x hxS).1
    have hyL := (hinterval y hyS).1
    rcases le_total x y with hxy | hyx
    · have hpdiv : p ∣ y - x := Nat.dvd_sub hpy hpx
      have hxlow : p * ((x - L) / p) ≤ x - L := Nat.mul_div_le _ _
      have hyup : y - L < p * ((y - L) / p + 1) := Nat.lt_mul_div_succ _ hp
      have hdiffshift : (y - L) - (x - L) = y - x := by omega
      have hdiff : y - x < p := by
        dsimp [f] at heq
        rw [← heq, Nat.mul_add] at hyup
        simp only [mul_one] at hyup
        rw [← hdiffshift]
        omega
      have hz : y - x = 0 := Nat.eq_zero_of_dvd_of_lt hpdiv hdiff
      omega
    · exact (by
        apply Eq.symm
        apply Nat.le_antisymm hyx
        have hpdiv : p ∣ x - y := Nat.dvd_sub hpx hpy
        have hylow : p * ((y - L) / p) ≤ y - L := Nat.mul_div_le _ _
        have hxup : x - L < p * ((x - L) / p + 1) := Nat.lt_mul_div_succ _ hp
        have hdiffshift : (x - L) - (y - L) = x - y := by omega
        have hdiff : x - y < p := by
          dsimp [f] at heq
          rw [heq, Nat.mul_add] at hxup
          simp only [mul_one] at hxup
          rw [← hdiffshift]
          omega
        have hz : x - y = 0 := Nat.eq_zero_of_dvd_of_lt hpdiv hdiff
        omega)
  have himage : M.image f ⊆ Finset.range (G / p + 1) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
    have hnS : n ∈ S := (Finset.mem_filter.mp hn).1
    have hnL := (hinterval n hnS).1
    have hnG := (hinterval n hnS).2
    apply Finset.mem_range.mpr
    dsimp [f]
    have hsub : n - L ≤ G := by omega
    have := (Nat.div_le_div_right hsub : (n - L) / p ≤ G / p)
    omega
  calc
    M.card = (M.image f).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (G / p + 1)).card := Finset.card_le_card himage
    _ = G / p + 1 := Finset.card_range _

theorem interval_label_card_le_reciprocal_mass
    (S : Finset ℕ) (L G : ℕ) (a label : ℕ → ℕ)
    (ha : ∀ r, 0 < a r)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hdiv : ∀ n ∈ S, a (label n) ∣ n) :
    (S.card : ℝ) ≤
      (G : ℝ) * (∑ r ∈ S.image label, (a r : ℝ)⁻¹) +
        ((S.image label).card : ℝ) := by
  let T := S.image label
  have hmaps : Set.MapsTo label (S : Set ℕ) (T : Set ℕ) := by
    intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hfiber : ∀ r ∈ T,
      ((S.filter fun n => label n = r).card : ℝ) ≤
        (G : ℝ) * (a r : ℝ)⁻¹ + 1 := by
    intro r hr
    have hsubset : (S.filter fun n => label n = r) ⊆ multiplesIn S (a r) := by
      intro n hn
      have hnS := (Finset.mem_filter.mp hn).1
      have hnr := (Finset.mem_filter.mp hn).2
      apply Finset.mem_filter.mpr
      exact ⟨hnS, hnr ▸ hdiv n hnS⟩
    have hnat : (S.filter fun n => label n = r).card ≤ G / a r + 1 :=
      (Finset.card_le_card hsubset).trans
        (multiplesIn_interval_card_le S L G (a r) (ha r) hinterval)
    have hcast : (((S.filter fun n => label n = r).card : ℕ) : ℝ) ≤
        ((G / a r + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    have hq : ((G / a r : ℕ) : ℝ) ≤ (G : ℝ) / (a r : ℝ) := Nat.cast_div_le
    norm_num only [Nat.cast_add, Nat.cast_one] at hcast
    calc
      ((S.filter fun n => label n = r).card : ℝ) ≤
          (G / a r : ℕ) + 1 := hcast
      _ ≤ (G : ℝ) / (a r : ℝ) + 1 := by linarith
      _ = (G : ℝ) * (a r : ℝ)⁻¹ + 1 := by rw [div_eq_mul_inv]
  have hcard : S.card = ∑ r ∈ T, (S.filter fun n => label n = r).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  rw [hcard]
  norm_num only [Nat.cast_sum]
  calc
    (∑ r ∈ T, ((S.filter fun n => label n = r).card : ℝ)) ≤
        ∑ r ∈ T, ((G : ℝ) * (a r : ℝ)⁻¹ + 1) :=
      Finset.sum_le_sum hfiber
    _ = (G : ℝ) * (∑ r ∈ T, (a r : ℝ)⁻¹) + (T.card : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]

theorem Finset.exists_subset_injOn_card_eq_image
    {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) :
    ∃ T : Finset α, T ⊆ S ∧ Set.InjOn f (T : Set α) ∧
      T.card = (S.image f).card := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | insert a s ha ih =>
      obtain ⟨T, hTs, hinj, hcard⟩ := ih
      by_cases him : f a ∈ s.image f
      · refine ⟨T, hTs.trans (Finset.subset_insert a s), hinj, ?_⟩
        rw [Finset.image_insert, Finset.card_insert_of_mem him]
        exact hcard
      · refine ⟨insert a T, ?_, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyT
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hTs hyT)
        · intro y hy z hz heq
          rcases Finset.mem_insert.mp hy with rfl | hyT
          · rcases Finset.mem_insert.mp hz with rfl | hzT
            · rfl
            · exfalso
              apply him
              exact Finset.mem_image.mpr ⟨z, hTs hzT, heq.symm⟩
          · rcases Finset.mem_insert.mp hz with rfl | hzT
            · exfalso
              apply him
              exact Finset.mem_image.mpr ⟨y, hTs hyT, heq⟩
            · exact hinj hyT hzT heq
        · rw [Finset.card_insert_of_notMem]
          · rw [Finset.image_insert, Finset.card_insert_of_notMem him, hcard]
          · intro haT
            exact ha (hTs haT)

theorem eventually_mul_count_le_of_isLittleO_sqrt
    (p : ℕ → Prop) [DecidablePred p]
    (h : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (K : ℕ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, K * Nat.count p n ≤ n := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hcpos : (0 : ℝ) < 1 / (2 * (K : ℝ)) := by positivity
  have hb := h.bound hcpos
  filter_upwards [hb, eventually_ge_atTop 1] with n hn hn1
  have hncount : (Nat.count p n : ℝ) ≤
      (1 / (2 * (K : ℝ))) * Real.sqrt (n : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (Nat.count p n : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith
  have hmul := mul_le_mul_of_nonneg_left hncount hKR.le
  have hcast : ((K * Nat.count p n : ℕ) : ℝ) ≤ (n : ℝ) := by
    norm_num only [Nat.cast_mul]
    have hid : (K : ℝ) * (1 / (2 * (K : ℝ))) = 1 / 2 := by
      field_simp
    rw [← mul_assoc, hid] at hmul
    nlinarith
  exact_mod_cast hcast

def divisorSifted (p : ℕ → Prop) (n : ℕ) : Prop :=
  0 < n ∧ ∀ a, p a → ¬a ∣ n

noncomputable instance divisorSiftedDecidable (p : ℕ → Prop) :
    DecidablePred (divisorSifted p) := Classical.decPred _

def gapPattern (q : ℕ → Prop) (d n : ℕ) : Prop :=
  q n ∧ q (n + d) ∧ ∀ k, 0 < k → k < d → ¬q (n + k)

noncomputable def truncatedGapCost (q : ℕ → Prop) (H n : ℕ) : ℕ := by
  classical
  exact ∑ d ∈ Finset.Ico 1 H, if gapPattern q d n then d ^ 2 else 0

theorem nth_consecutive_no_mem
    (q : ℕ → Prop) (hq : Set.Infinite {n | q n})
    (i n : ℕ) (hleft : Nat.nth q i < n)
    (hright : n < Nat.nth q (i + 1)) : ¬q n := by
  classical
  intro hn
  have hicount : i < Nat.count q n := (Nat.lt_nth_iff_count_lt hq).2 hleft
  have hidx : i + 1 ≤ Nat.count q n := by omega
  have hmono : Nat.nth q (i + 1) ≤ Nat.nth q (Nat.count q n) :=
    (Nat.nth_strictMono hq).monotone hidx
  have hnth : Nat.nth q (Nat.count q n) = n := Nat.nth_count hn
  rw [hnth] at hmono
  exact (not_lt_of_ge hmono) hright

theorem gapPattern_nth_iff_gap_eq
    (q : ℕ → Prop) (hq : Set.Infinite {n | q n})
    (i d : ℕ) (hd : 0 < d) :
    gapPattern q d (Nat.nth q i) ↔
      Nat.nth q (i + 1) - Nat.nth q i = d := by
  classical
  have hbmono : StrictMono (Nat.nth q) := Nat.nth_strictMono hq
  have hbi : q (Nat.nth q i) := Nat.nth_mem_of_infinite hq i
  have hbi1 : q (Nat.nth q (i + 1)) := Nat.nth_mem_of_infinite hq (i + 1)
  constructor
  · rintro ⟨_, hend, hinterior⟩
    have hilt : Nat.nth q i < Nat.nth q i + d := by omega
    have hicount : i < Nat.count q (Nat.nth q i + d) :=
      (Nat.lt_nth_iff_count_lt hq).2 hilt
    have hidx : i + 1 ≤ Nat.count q (Nat.nth q i + d) := by omega
    have hnextle : Nat.nth q (i + 1) ≤ Nat.nth q i + d := by
      have hm : Nat.nth q (i + 1) ≤
          Nat.nth q (Nat.count q (Nat.nth q i + d)) :=
        hbmono.monotone hidx
      have hnth : Nat.nth q (Nat.count q (Nat.nth q i + d)) =
          Nat.nth q i + d := Nat.nth_count hend
      rwa [hnth] at hm
    have hnextge : Nat.nth q i + d ≤ Nat.nth q (i + 1) := by
      by_contra hnot
      have hstrict : Nat.nth q (i + 1) < Nat.nth q i + d := by omega
      let k := Nat.nth q (i + 1) - Nat.nth q i
      have hstep := hbmono (by omega : i < i + 1)
      have hkpos : 0 < k := Nat.sub_pos_of_lt hstep
      have hklt : k < d := by dsimp [k]; omega
      have hsum : Nat.nth q i + k = Nat.nth q (i + 1) := by
        dsimp [k]
        exact Nat.add_sub_of_le hstep.le
      exact hinterior k hkpos hklt (hsum ▸ hbi1)
    have heq : Nat.nth q (i + 1) = Nat.nth q i + d :=
      le_antisymm hnextle hnextge
    omega
  · intro hgap
    have hstep := hbmono (by omega : i < i + 1)
    have heq : Nat.nth q (i + 1) = Nat.nth q i + d := by omega
    refine ⟨hbi, ?_, ?_⟩
    · rw [← heq]
      exact hbi1
    · intro k hk0 hkd hkq
      apply nth_consecutive_no_mem q hq i (Nat.nth q i + k)
      · omega
      · rw [heq]
        omega
      · exact hkq

theorem truncatedGapCost_nth
    (q : ℕ → Prop) (hq : Set.Infinite {n | q n})
    (H i : ℕ) :
    truncatedGapCost q H (Nat.nth q i) =
      if Nat.nth q (i + 1) - Nat.nth q i < H then
        (Nat.nth q (i + 1) - Nat.nth q i) ^ 2 else 0 := by
  classical
  let g := Nat.nth q (i + 1) - Nat.nth q i
  have hg : 0 < g := Nat.sub_pos_of_lt (Nat.nth_strictMono hq (by omega))
  by_cases hgH : g < H
  · rw [if_pos hgH]
    unfold truncatedGapCost
    have hgmem : g ∈ Finset.Ico 1 H := Finset.mem_Ico.mpr ⟨hg, hgH⟩
    rw [Finset.sum_eq_single g]
    · rw [if_pos]
      exact gapPattern_nth_iff_gap_eq q hq i g hg |>.2 rfl
    · intro d hdmem hdne
      rw [if_neg]
      intro hpat
      have heq := (gapPattern_nth_iff_gap_eq q hq i d
        (by exact (Finset.mem_Ico.mp hdmem).1)).1 hpat
      exact hdne heq.symm
    · exact fun h => (h hgmem).elim
  · rw [if_neg hgH]
    unfold truncatedGapCost
    apply Finset.sum_eq_zero
    intro d hdmem
    rw [if_neg]
    intro hpat
    have heq := (gapPattern_nth_iff_gap_eq q hq i d
      (Finset.mem_Ico.mp hdmem).1).1 hpat
    have hdH := (Finset.mem_Ico.mp hdmem).2
    omega

theorem truncatedGapCost_eq_zero_of_not
    (q : ℕ → Prop) (H n : ℕ) (hn : ¬q n) :
    truncatedGapCost q H n = 0 := by
  classical
  unfold truncatedGapCost
  apply Finset.sum_eq_zero
  intro d hd
  rw [if_neg]
  exact fun h => hn h.1

theorem gapPattern_periodic
    (q : ℕ → Prop) (P d : ℕ) (hq : Function.Periodic q P) :
    Function.Periodic (gapPattern q d) P := by
  intro n
  apply propext
  constructor
  · rintro ⟨hn, hend, hint⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using hq n ▸ hn
    · have hp := hq (n + d)
      rw [show n + P + d = n + d + P by omega] at hend
      exact hp ▸ hend
    · intro k hk0 hkd
      have hp := hq (n + k)
      have hh := hint k hk0 hkd
      rw [show n + P + k = n + k + P by omega] at hh
      exact hp ▸ hh
  · rintro ⟨hn, hend, hint⟩
    refine ⟨?_, ?_, ?_⟩
    · exact hq n ▸ hn
    · have hp := hq (n + d)
      rw [show n + P + d = n + d + P by omega]
      exact hp.symm ▸ hend
    · intro k hk0 hkd
      have hp := hq (n + k)
      rw [show n + P + k = n + k + P by omega]
      exact hp.symm ▸ hint k hk0 hkd

theorem truncatedGapCost_periodic
    (q : ℕ → Prop) (H P : ℕ) (hq : Function.Periodic q P) :
    Function.Periodic (truncatedGapCost q H) P := by
  intro n
  unfold truncatedGapCost
  apply Finset.sum_congr rfl
  intro d hd
  have hp := gapPattern_periodic q P d hq n
  rw [hp]

theorem truncatedGapCost_eq_of_window_agree
    (q r : ℕ → Prop) (H n : ℕ)
    (hagree : ∀ k, k ≤ H → (q (n + k) ↔ r (n + k))) :
    truncatedGapCost q H n = truncatedGapCost r H n := by
  classical
  unfold truncatedGapCost
  apply Finset.sum_congr rfl
  intro d hd
  have hdH := (Finset.mem_Ico.mp hd).2
  congr 1
  apply propext
  constructor
  · rintro ⟨hn, hend, hint⟩
    refine ⟨(by simpa using (hagree 0 (Nat.zero_le H)).mp hn),
      (hagree d hdH.le).mp hend, ?_⟩
    intro k hk0 hkd
    exact fun hk => hint k hk0 hkd ((hagree k (by omega)).mpr hk)
  · rintro ⟨hn, hend, hint⟩
    refine ⟨(by simpa using (hagree 0 (Nat.zero_le H)).mpr hn),
      (hagree d hdH.le).mpr hend, ?_⟩
    intro k hk0 hkd
    exact fun hk => hint k hk0 hkd ((hagree k (by omega)).mp hk)

theorem truncatedGapCost_le_cube (q : ℕ → Prop) (H n : ℕ) :
    truncatedGapCost q H n ≤ H ^ 3 := by
  classical
  unfold truncatedGapCost
  calc
    (∑ d ∈ Finset.Ico 1 H, if gapPattern q d n then d ^ 2 else 0) ≤
        ∑ d ∈ Finset.Ico 1 H, H ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · exact Nat.pow_le_pow_left (Finset.mem_Ico.mp hd).2.le 2
      · exact Nat.zero_le _
    _ = (Finset.Ico 1 H).card * H ^ 2 := by simp
    _ ≤ H * H ^ 2 := by
      apply Nat.mul_le_mul_right
      simp
    _ = H ^ 3 := by ring

theorem image_nth_range_count
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n}) (x : ℕ) :
    (Finset.range (Nat.count q x)).image (Nat.nth q) =
      (Finset.range x).filter q := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr
      (Nat.nth_lt_of_lt_count (Finset.mem_range.mp hi)),
      Nat.nth_mem_of_infinite hq i⟩
  · intro hn
    have hnr := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hnq := (Finset.mem_filter.mp hn).2
    apply Finset.mem_image.mpr
    refine ⟨Nat.count q n, Finset.mem_range.mpr ?_, Nat.nth_count hnq⟩
    exact Nat.count_strict_mono hnq hnr

theorem sum_truncatedGapCost_eq_gap_sum
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (H x : ℕ) :
    ∑ n ∈ Finset.range x, truncatedGapCost q H n =
      ∑ i ∈ (Finset.range (Nat.count q x)).filter
        (fun i => Nat.nth q (i + 1) - Nat.nth q i < H),
        (Nat.nth q (i + 1) - Nat.nth q i) ^ 2 := by
  classical
  let S := Finset.range (Nat.count q x)
  let B := (Finset.range x).filter q
  have hfilter : (∑ n ∈ B, truncatedGapCost q H n) =
      ∑ n ∈ Finset.range x, truncatedGapCost q H n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hnx hnB
    apply truncatedGapCost_eq_zero_of_not q H n
    intro hnq
    exact hnB (Finset.mem_filter.mpr ⟨hnx, hnq⟩)
  have himage : S.image (Nat.nth q) = B := by
    simpa [S, B] using image_nth_range_count q hq x
  rw [← hfilter, ← himage, Finset.sum_image]
  · rw [Finset.sum_filter]
    change (∑ i ∈ S, truncatedGapCost q H (Nat.nth q i)) =
      ∑ i ∈ S, if Nat.nth q (i + 1) - Nat.nth q i < H then
        (Nat.nth q (i + 1) - Nat.nth q i) ^ 2 else 0
    apply Finset.sum_congr rfl
    intro i hi
    rw [truncatedGapCost_nth q hq]
  · exact (Nat.nth_injective hq).injOn

def finiteDivisorSifted (p : ℕ → Prop) (R n : ℕ) : Prop :=
  ∀ a ∈ (List.range R).map (Nat.nth p), ¬a ∣ n

theorem finiteDivisorSifted_periodic (p : ℕ → Prop) (R : ℕ) :
    Function.Periodic (finiteDivisorSifted p R)
      ((List.range R).map (Nat.nth p)).prod :=
  avoidList_periodic _

theorem divisorSifted_imp_finite (p : ℕ → Prop)
    (hp : Set.Infinite {n | p n}) (R n : ℕ) :
    divisorSifted p n → finiteDivisorSifted p R n := by
  intro hn a ha
  rcases List.mem_map.mp ha with ⟨r, hr, rfl⟩
  exact hn.2 _ (Nat.nth_mem_of_infinite hp r)

theorem finiteDivisorSifted_pos
    (p : ℕ → Prop) (_hp : Set.Infinite {n | p n})
    (_hp2 : ∀ n, p n → 2 ≤ n) (R n : ℕ) (hR : 0 < R)
    (hn : finiteDivisorSifted p R n) : 0 < n := by
  by_contra hn0
  have heq : n = 0 := by omega
  have hmem : Nat.nth p 0 ∈ (List.range R).map (Nat.nth p) :=
    List.mem_map.mpr ⟨0, List.mem_range.mpr hR, rfl⟩
  apply hn (Nat.nth p 0) hmem
  rw [heq]
  exact dvd_zero _

noncomputable def sieveMismatch (p : ℕ → Prop) (R M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range M).filter fun n =>
    finiteDivisorSifted p R n ∧ ¬divisorSifted p n

theorem sieveMismatch_card_cast_le
    (p : ℕ → Prop) [DecidablePred p] (hp : Set.Infinite {n | p n})
    (hp2 : ∀ n, p n → 2 ≤ n)
    (R M : ℕ) (hR : 0 < R) (ε : ℝ)
    (htail : ∀ T : Finset ℕ, (∀ r ∈ T, R ≤ r) →
      (∑ r ∈ T, ((Nat.nth p r : ℝ)⁻¹)) ≤ ε) :
    ((sieveMismatch p R M).card : ℝ) ≤
      (M : ℝ) * ε + (Nat.count p M : ℝ) := by
  classical
  let S := sieveMismatch p R M
  let rank := divisorWitnessRank p
  let a := Nat.nth p
  have hinterval : ∀ n ∈ S, 0 ≤ n ∧ n ≤ 0 + M := by
    intro n hn
    have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
    have hnr := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
    omega
  have hfinite : ∀ n ∈ S, finiteDivisorSifted p R n := by
    intro n hn
    have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
    exact (Finset.mem_filter.mp hh).2.1
  have hnotfull : ∀ n ∈ S, ¬divisorSifted p n := by
    intro n hn
    have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
    exact (Finset.mem_filter.mp hh).2.2
  have hpos : ∀ n ∈ S, 0 < n := by
    intro n hn
    exact finiteDivisorSifted_pos p hp hp2 R n hR (hfinite n hn)
  have hcov : ∀ n ∈ S, ∃ d, p d ∧ d ∣ n := by
    intro n hn
    have hnf := hnotfull n hn
    rw [divisorSifted] at hnf
    push Not at hnf
    exact hnf (hpos n hn)
  have hdvd : ∀ n ∈ S, a (rank n) ∣ n := by
    intro n hn
    exact nth_divisorWitnessRank_dvd p n (hcov n hn)
  have hrank : ∀ n ∈ S, R ≤ rank n := by
    intro n hn
    apply le_divisorWitnessRank_of_avoid_prefix p n R (hcov n hn)
    exact hfinite n hn
  have hmass : (∑ r ∈ S.image rank, ((a r : ℝ)⁻¹)) ≤ ε := by
    apply htail
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨n, hn, rfl⟩
    exact hrank n hn
  have ha : ∀ r, 0 < a r := by
    intro r
    dsimp [a]
    have hh := hp2 _ (Nat.nth_mem_of_infinite hp r)
    exact lt_of_lt_of_le (by omega : 0 < 2) hh
  have hcharge0 := interval_label_card_le_reciprocal_mass
    S 0 M a rank ha hinterval hdvd
  have hcharge : (S.card : ℝ) ≤
      (M : ℝ) * ε + ((S.image rank).card : ℝ) := by
    calc
      (S.card : ℝ) ≤ (M : ℝ) *
          (∑ r ∈ S.image rank, ((a r : ℝ)⁻¹)) + (S.image rank).card := hcharge0
      _ ≤ (M : ℝ) * ε + (S.image rank).card := by gcongr
  have himage : (S.image rank).card ≤ Nat.count p M := by
    have hsubset : S.image rank ⊆ Finset.range (Nat.count p M) := by
      intro r hr
      apply Finset.mem_range.mpr
      rcases Finset.mem_image.mp hr with ⟨n, hn, rfl⟩
      have hh : n ∈ sieveMismatch p R M := by simpa [S] using hn
      have hnM := Finset.mem_range.mp (Finset.mem_filter.mp hh).1
      have hale : a (rank n) ≤ n := Nat.le_of_dvd (hpos n hn) (hdvd n hn)
      exact (Nat.lt_nth_iff_count_lt hp).2 (lt_of_le_of_lt hale hnM)
    simpa using Finset.card_le_card hsubset
  dsimp [S] at hcharge ⊢
  calc
    ((sieveMismatch p R M).card : ℝ) ≤
        (M : ℝ) * ε + ((sieveMismatch p R M).image rank).card := by
      simpa using hcharge
    _ ≤ (M : ℝ) * ε + (Nat.count p M : ℝ) := by
      gcongr

noncomputable def badGapStarts (p : ℕ → Prop) (R H x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (H + 1)).biUnion fun k =>
    (Finset.range x).filter fun n => n + k ∈ sieveMismatch p R (x + H + 1)

theorem badGapStarts_subset_range (p : ℕ → Prop) (R H x : ℕ) :
    badGapStarts p R H x ⊆ Finset.range x := by
  classical
  intro n hn
  rcases Finset.mem_biUnion.mp hn with ⟨k, hk, hnk⟩
  exact (Finset.mem_filter.mp hnk).1

theorem badGapStarts_card_le (p : ℕ → Prop) (R H x : ℕ) :
    (badGapStarts p R H x).card ≤
      (H + 1) * (sieveMismatch p R (x + H + 1)).card := by
  classical
  unfold badGapStarts
  have hfiber : ∀ k ∈ Finset.range (H + 1),
      ((Finset.range x).filter fun n =>
        n + k ∈ sieveMismatch p R (x + H + 1)).card ≤
          (sieveMismatch p R (x + H + 1)).card := by
    intro k hk
    let T := (Finset.range x).filter fun n =>
      n + k ∈ sieveMismatch p R (x + H + 1)
    have himage : T.image (fun n => n + k) ⊆
        sieveMismatch p R (x + H + 1) := by
      intro m hm
      rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
      exact (Finset.mem_filter.mp hn).2
    calc
      ((Finset.range x).filter fun n =>
          n + k ∈ sieveMismatch p R (x + H + 1)).card = T.card := rfl
      _ = (T.image (fun n => n + k)).card :=
        (Finset.card_image_of_injective T (add_left_injective k)).symm
      _ ≤ (sieveMismatch p R (x + H + 1)).card :=
        Finset.card_le_card himage
  have h := Finset.card_biUnion_le_card_mul (Finset.range (H + 1))
    (fun k => (Finset.range x).filter fun n =>
      n + k ∈ sieveMismatch p R (x + H + 1))
    (sieveMismatch p R (x + H + 1)).card hfiber
  simpa using h

theorem sieve_window_agree_of_not_bad
    (p : ℕ → Prop)
    (hp : Set.Infinite {n | p n}) (R H x n : ℕ)
    (hnx : n < x) (hgood : n ∉ badGapStarts p R H x) :
    ∀ k, k ≤ H →
      (divisorSifted p (n + k) ↔ finiteDivisorSifted p R (n + k)) := by
  classical
  intro k hk
  have hkRange : k ∈ Finset.range (H + 1) := Finset.mem_range.mpr (by omega)
  constructor
  · exact divisorSifted_imp_finite p hp R (n + k)
  · intro hfinite
    by_contra hfull
    have hm : n + k ∈ sieveMismatch p R (x + H + 1) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega), hfinite, hfull⟩
    apply hgood
    apply Finset.mem_biUnion.mpr
    exact ⟨k, hkRange, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hnx, hm⟩⟩

theorem sum_range_mul_periodic
    (f : ℕ → ℕ) (P : ℕ) (hf : Function.Periodic f P) (q : ℕ) :
    ∑ n ∈ Finset.range (q * P), f n =
      q * ∑ n ∈ Finset.range P, f n := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Nat.succ_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simpa [Nat.add_comm, Nat.mul_comm] using (hf.nat_mul q n)

theorem sum_range_periodic_div_mod
    (f : ℕ → ℕ) (P x : ℕ) (hf : Function.Periodic f P) :
    ∑ n ∈ Finset.range x, f n =
      (x / P) * (∑ n ∈ Finset.range P, f n) +
        ∑ n ∈ Finset.range (x % P), f n := by
  by_cases hP : P = 0
  · subst P
    simp
  · have hx : x = (x / P) * P + x % P := by
      simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div x P).symm
    conv_lhs => rw [hx]
    rw [Finset.sum_range_add, sum_range_mul_periodic f P hf]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    simpa [Nat.mul_comm, Nat.add_comm] using (hf.nat_mul (x / P) n)

theorem tendsto_nat_div_cast_div (P : ℕ) (hP : 0 < P) :
    Tendsto (fun x : ℕ => ((x / P : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 (1 / (P : ℝ))) := by
  have hm := tendsto_mod_div_atTop_nhds_zero_nat hP
  have hbase : Tendsto (fun x : ℕ =>
      (1 - (((x % P : ℕ) : ℝ) / (x : ℝ))) / (P : ℝ))
      atTop (𝓝 ((1 - 0) / (P : ℝ))) :=
    (tendsto_const_nhds.sub hm).div_const (P : ℝ)
  have hbase' : Tendsto (fun x : ℕ =>
      (1 - (((x % P : ℕ) : ℝ) / (x : ℝ))) / (P : ℝ))
      atTop (𝓝 (1 / (P : ℝ))) := by simpa using hbase
  apply hbase'.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hdecomp := Nat.mod_add_div x P
  have hdecompR : ((x % P : ℕ) : ℝ) +
      (P : ℝ) * ((x / P : ℕ) : ℝ) = (x : ℝ) := by exact_mod_cast hdecomp
  field_simp
  nlinarith

theorem tendsto_periodic_nat_average
    (f : ℕ → ℕ) (P : ℕ) (hP : 0 < P)
    (hf : Function.Periodic f P) :
    Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range x, f n : ℕ) : ℝ) / (x : ℝ))
      atTop (𝓝 (((∑ n ∈ Finset.range P, f n : ℕ) : ℝ) / (P : ℝ))) := by
  let S : ℕ := ∑ n ∈ Finset.range P, f n
  let rem : ℕ → ℕ := fun x => ∑ n ∈ Finset.range (x % P), f n
  have hrem0 : ∀ x, 0 ≤ rem x := fun _ => Nat.zero_le _
  have hremS : ∀ x, rem x ≤ S := by
    intro x
    dsimp [rem, S]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.range_mono (Nat.mod_lt x hP).le
    · intro i hiP hir
      exact Nat.zero_le _
  have hremT : Tendsto (fun x : ℕ => (rem x : ℝ) / (x : ℝ))
      atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero (b := (0 : ℝ)) (B := (S : ℝ))
    · exact Filter.Eventually.of_forall (fun x => by exact_mod_cast hrem0 x)
    · exact Filter.Eventually.of_forall (fun x => by exact_mod_cast hremS x)
    · exact tendsto_natCast_atTop_atTop
  have hq := (tendsto_nat_div_cast_div P hP).mul_const (S : ℝ)
  have hsum := hq.add hremT
  have hlim : (1 / (P : ℝ)) * (S : ℝ) + 0 = (S : ℝ) / (P : ℝ) := by ring
  rw [hlim] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hdecomp := sum_range_periodic_div_mod f P x hf
  dsimp [S, rem] at hdecomp ⊢
  rw [hdecomp]
  norm_num only [Nat.cast_add, Nat.cast_mul]
  field_simp

theorem tendsto_count_add_div
    (p : ℕ → Prop) [DecidablePred p]
    (h : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (c : ℕ) :
    Tendsto (fun x : ℕ => (Nat.count p (x + c) : ℝ) / (x : ℝ))
      atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun x => by
      have hnonneg : (0 : ℝ) ≤ (Nat.count p (x + c) : ℝ) / (x : ℝ) := by positivity
      linarith
  · intro b hb
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / b)
    have hNpos : 0 < N := by
      have htwo : (0 : ℝ) < 2 / b := by positivity
      exact_mod_cast (lt_trans htwo hN)
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp
      (eventually_mul_count_le_of_isLittleO_sqrt p h N hNpos)
    filter_upwards [eventually_ge_atTop (max N0 (max c 1))] with x hx
    have hxN0 : N0 ≤ x + c := le_trans (le_trans (le_max_left _ _) hx) (Nat.le_add_right x c)
    have hlin := hN0 (x + c) hxN0
    have hxc : x + c ≤ 2 * x := by
      have hcx : c ≤ x := le_trans (le_max_left c 1) (le_trans (le_max_right N0 _) hx)
      omega
    have hlinR : (N : ℝ) * (Nat.count p (x + c) : ℝ) ≤ 2 * (x : ℝ) := by
      exact_mod_cast hlin.trans hxc
    have hxpos : (0 : ℝ) < x := by
      have : 1 ≤ x := le_trans (le_max_right c 1) (le_trans (le_max_right N0 _) hx)
      exact_mod_cast this
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hNb : (2 : ℝ) < b * N := by
      have := hN
      rw [div_lt_iff₀ hb] at this
      nlinarith
    rw [div_lt_iff₀ hxpos]
    nlinarith

theorem exists_tendsto_of_uniform_eventual_approx
    (f : ℕ → ℝ) (approx : ℕ → ℕ → ℝ)
    (hclose : ∀ ε : ℝ, 0 < ε → ∃ H : ℕ,
      ∀ᶠ x : ℕ in atTop, |f x - approx H x| < ε)
    (hconv : ∀ H : ℕ, ∃ L : ℝ, Tendsto (approx H) atTop (𝓝 L)) :
    ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
  have hcauchy : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨H, hH⟩ := hclose (ε / 4) (by positivity)
    obtain ⟨L, hL⟩ := hconv H
    have hLmetric := (Metric.tendsto_atTop.1 hL) (ε / 4) (by positivity)
    obtain ⟨Nclose, hNclose⟩ := Filter.eventually_atTop.mp hH
    obtain ⟨Nlim, hNlim⟩ := hLmetric
    refine ⟨max Nclose Nlim, ?_⟩
    intro m hm n hn
    have hmclose := hNclose m (le_trans (le_max_left _ _) hm)
    have hnclose := hNclose n (le_trans (le_max_left _ _) hn)
    have hmlim := hNlim m (le_trans (le_max_right _ _) hm)
    have hnlim := hNlim n (le_trans (le_max_right _ _) hn)
    rw [Real.dist_eq] at hmlim hnlim ⊢
    have htri1 : |f m - f n| ≤
        |f m - approx H m| + |approx H m - L| + |L - f n| := by
      simpa only [Real.dist_eq] using
        dist_triangle4 (f m) (approx H m) L (f n)
    have htri2 : |L - f n| ≤
        |L - approx H n| + |approx H n - f n| := by
      simpa only [Real.dist_eq] using dist_triangle L (approx H n) (f n)
    have hmclose' : |f m - approx H m| < ε / 4 := hmclose
    have hnclose' : |approx H n - f n| < ε / 4 := by
      simpa [abs_sub_comm] using hnclose
    have hnlim' : |L - approx H n| < ε / 4 := by
      simpa [abs_sub_comm] using hnlim
    nlinarith
  exact cauchySeq_tendsto_of_complete hcauchy

theorem abs_cast_sum_sub_sum_le_card_mul
    (S B : Finset ℕ) (f g : ℕ → ℕ) (K : ℕ)
    (hBS : B ⊆ S)
    (hf : ∀ n ∈ B, f n ≤ K) (hg : ∀ n ∈ B, g n ≤ K)
    (heq : ∀ n ∈ S, n ∉ B → f n = g n) :
    |((∑ n ∈ S, f n : ℕ) : ℝ) - ((∑ n ∈ S, g n : ℕ) : ℝ)| ≤
      (B.card : ℝ) * (K : ℝ) := by
  have hoff : (∑ n ∈ S \ B, f n) = ∑ n ∈ S \ B, g n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact heq n (Finset.mem_sdiff.mp hn).1 (Finset.mem_sdiff.mp hn).2
  have hfs := Finset.sum_sdiff hBS (f := f)
  have hgs := Finset.sum_sdiff hBS (f := g)
  have hfb : ∑ n ∈ B, f n ≤ B.card * K := by
    calc
      ∑ n ∈ B, f n ≤ ∑ _n ∈ B, K := Finset.sum_le_sum hf
      _ = B.card * K := by simp
  have hgb : ∑ n ∈ B, g n ≤ B.card * K := by
    calc
      ∑ n ∈ B, g n ≤ ∑ _n ∈ B, K := Finset.sum_le_sum hg
      _ = B.card * K := by simp
  have hfbR : ((∑ n ∈ B, f n : ℕ) : ℝ) ≤ (B.card : ℝ) * K := by exact_mod_cast hfb
  have hgbR : ((∑ n ∈ B, g n : ℕ) : ℝ) ≤ (B.card : ℝ) * K := by exact_mod_cast hgb
  have hfsR : ((∑ n ∈ S \ B, f n : ℕ) : ℝ) +
      ((∑ n ∈ B, f n : ℕ) : ℝ) = ((∑ n ∈ S, f n : ℕ) : ℝ) := by
    exact_mod_cast hfs
  have hgsR : ((∑ n ∈ S \ B, g n : ℕ) : ℝ) +
      ((∑ n ∈ B, g n : ℕ) : ℝ) = ((∑ n ∈ S, g n : ℕ) : ℝ) := by
    exact_mod_cast hgs
  have hoffR : ((∑ n ∈ S \ B, f n : ℕ) : ℝ) =
      ((∑ n ∈ S \ B, g n : ℕ) : ℝ) := by exact_mod_cast hoff
  have heqR : ((∑ n ∈ S, f n : ℕ) : ℝ) - ((∑ n ∈ S, g n : ℕ) : ℝ) =
      ((∑ n ∈ B, f n : ℕ) : ℝ) - ((∑ n ∈ B, g n : ℕ) : ℝ) := by
    linarith
  rw [heqR, abs_le]
  have hfn : (0 : ℝ) ≤ ((∑ n ∈ B, f n : ℕ) : ℝ) := by positivity
  have hgn : (0 : ℝ) ≤ ((∑ n ∈ B, g n : ℕ) : ℝ) := by positivity
  constructor <;> linarith

noncomputable def fullTruncatedGapAverage
    (p : ℕ → Prop) (H x : ℕ) : ℝ :=
  ((∑ n ∈ Finset.range x, truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) /
    (x : ℝ)

noncomputable def finiteTruncatedGapAverage
    (p : ℕ → Prop) (R H x : ℕ) : ℝ :=
  ((∑ n ∈ Finset.range x, truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) /
    (x : ℝ)

noncomputable def finiteTruncatedGapLimit
    (p : ℕ → Prop) (R H : ℕ) : ℝ :=
  let P := ((List.range R).map (Nat.nth p)).prod
  ((∑ n ∈ Finset.range P,
      truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (P : ℝ)

theorem finiteTruncatedGapAverage_tendsto
    (p : ℕ → Prop)
    (hp : Set.Infinite {n | p n}) (hp2 : ∀ n, p n → 2 ≤ n)
    (R H : ℕ) :
    Tendsto (finiteTruncatedGapAverage p R H) atTop
      (𝓝 (finiteTruncatedGapLimit p R H)) := by
  let P := ((List.range R).map (Nat.nth p)).prod
  have hP : 0 < P := by
    apply List.prod_pos
    intro a ha
    rcases List.mem_map.mp ha with ⟨r, hr, rfl⟩
    have hh := hp2 _ (Nat.nth_mem_of_infinite hp r)
    exact lt_of_lt_of_le (by omega : 0 < 2) hh
  have hper := truncatedGapCost_periodic (finiteDivisorSifted p R) H P
    (finiteDivisorSifted_periodic p R)
  change Tendsto (fun x : ℕ =>
      ((∑ n ∈ Finset.range x,
        truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (x : ℝ))
    atTop (𝓝 (((∑ n ∈ Finset.range P,
      truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (P : ℝ)))
  simpa only [Nat.cast_sum] using
    tendsto_periodic_nat_average
      (truncatedGapCost (finiteDivisorSifted p R) H) P hP hper

theorem full_finite_truncated_sum_difference
    (p : ℕ → Prop)
    (hp : Set.Infinite {n | p n}) (R H x : ℕ) :
    |((∑ n ∈ Finset.range x,
        truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) -
      ((∑ n ∈ Finset.range x,
        truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ)| ≤
      ((badGapStarts p R H x).card : ℝ) * (H ^ 3 : ℕ) := by
  classical
  apply abs_cast_sum_sub_sum_le_card_mul
    (Finset.range x) (badGapStarts p R H x)
  · exact badGapStarts_subset_range p R H x
  · intro n hn
    exact truncatedGapCost_le_cube _ H n
  · intro n hn
    exact truncatedGapCost_le_cube _ H n
  · intro n hnx hgood
    apply truncatedGapCost_eq_of_window_agree
    exact sieve_window_agree_of_not_bad p hp R H x n
      (Finset.mem_range.mp hnx) hgood

theorem exists_prefix_eventually_full_finite_close
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (hp2 : ∀ n, p n → 2 ≤ n)
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (hsum : Summable fun r : ℕ => ((Nat.nth p r : ℝ)⁻¹))
    (H : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ R, ∀ᶠ x : ℕ in atTop,
      |fullTruncatedGapAverage p H x - finiteTruncatedGapAverage p R H x| < ε := by
  classical
  by_cases hH : H = 0
  · subst H
    refine ⟨0, Filter.Eventually.of_forall ?_⟩
    intro x
    simp [fullTruncatedGapAverage, finiteTruncatedGapAverage,
      truncatedGapCost, hε]
  · have hHpos : 0 < H := Nat.pos_of_ne_zero hH
    let K : ℕ := (H + 1) * H ^ 3
    have hK : 0 < K := by dsimp [K]; positivity
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    let δ : ℝ := ε / (4 * (K : ℝ))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have htailEv := eventually_finset_tail_sum_le_of_summable
      (fun r : ℕ => ((Nat.nth p r : ℝ)⁻¹)) hsum
      (fun r => inv_nonneg.mpr (by positivity)) δ hδ
    obtain ⟨R, htail, hR⟩ :=
      Filter.Eventually.exists (htailEv.and (eventually_ge_atTop 1))
    have hRpos : 0 < R := by omega
    have hMlim : Tendsto
        (fun x : ℕ => (((x + (H + 1) : ℕ) : ℝ) / (x : ℝ)))
        atTop (𝓝 1) := by
      have ht := tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ)
        ((H + 1 : ℕ) : ℝ) 0 1 (d := 1) (by norm_num)
      simpa [Nat.cast_add, add_comm] using ht
    have hM2 : ∀ᶠ x : ℕ in atTop,
        (((x + (H + 1) : ℕ) : ℝ) / (x : ℝ)) < 2 :=
      (tendsto_order.1 hMlim).2 2 (by norm_num)
    have hClim := tendsto_count_add_div p hcount (H + 1)
    have hsmallPos : 0 < ε / (2 * (K : ℝ)) := by positivity
    have hCsmall : ∀ᶠ x : ℕ in atTop,
        (Nat.count p (x + (H + 1)) : ℝ) / (x : ℝ) <
          ε / (2 * (K : ℝ)) :=
      (tendsto_order.1 hClim).2 _ hsmallPos
    refine ⟨R, ?_⟩
    filter_upwards [hM2, hCsmall, eventually_ge_atTop 1] with x hxM hxC hx
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    let M : ℕ := x + H + 1
    have hMeq : M = x + (H + 1) := by dsimp [M]; omega
    have hbad := badGapStarts_card_le p R H x
    have hmis := sieveMismatch_card_cast_le p hp hp2 R M hRpos δ htail
    have hnum0 := full_finite_truncated_sum_difference p hp R H x
    have hbadR : ((badGapStarts p R H x).card : ℝ) ≤
        ((H + 1) : ℝ) * ((sieveMismatch p R M).card : ℝ) := by
      exact_mod_cast (by simpa [M] using hbad)
    have hnum :
        |((∑ n ∈ Finset.range x,
            truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) -
          ((∑ n ∈ Finset.range x,
            truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ)| ≤
        (K : ℝ) * ((M : ℝ) * δ + (Nat.count p M : ℝ)) := by
      calc
        _ ≤ ((badGapStarts p R H x).card : ℝ) * (H ^ 3 : ℕ) := hnum0
        _ ≤ (((H + 1) : ℝ) * ((sieveMismatch p R M).card : ℝ)) *
              (H ^ 3 : ℕ) := by gcongr
        _ = (K : ℝ) * ((sieveMismatch p R M).card : ℝ) := by
          dsimp [K]
          norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
          ring
        _ ≤ (K : ℝ) * ((M : ℝ) * δ + (Nat.count p M : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hmis hKR.le
    change |(((∑ n ∈ Finset.range x,
        truncatedGapCost (divisorSifted p) H n : ℕ) : ℝ) / (x : ℝ)) -
      (((∑ n ∈ Finset.range x,
        truncatedGapCost (finiteDivisorSifted p R) H n : ℕ) : ℝ) / (x : ℝ))| < ε
    rw [← sub_div, abs_div, abs_of_pos hxR]
    calc
      _ ≤ ((K : ℝ) * ((M : ℝ) * δ + (Nat.count p M : ℝ))) / (x : ℝ) :=
        div_le_div_of_nonneg_right hnum hxR.le
      _ = (K : ℝ) *
          ((((M : ℝ) / (x : ℝ)) * δ) +
            ((Nat.count p M : ℝ) / (x : ℝ))) := by field_simp
      _ < ε := by
        have hxM' : (M : ℝ) / (x : ℝ) < 2 := by simpa [hMeq] using hxM
        have hxC' : (Nat.count p M : ℝ) / (x : ℝ) <
            ε / (2 * (K : ℝ)) := by simpa [hMeq] using hxC
        have hpart1 : (K : ℝ) * (((M : ℝ) / (x : ℝ)) * δ) < ε / 2 := by
          have hm := mul_lt_mul_of_pos_right hxM' hδ
          dsimp [δ] at hm ⊢
          have hfour : (0 : ℝ) < 4 * K := by positivity
          calc
            (K : ℝ) * ((M : ℝ) / (x : ℝ) * (ε / (4 * K))) <
                (K : ℝ) * (2 * (ε / (4 * K))) :=
              mul_lt_mul_of_pos_left hm hKR
            _ = ε / 2 := by field_simp; ring
        have hpart2 : (K : ℝ) * ((Nat.count p M : ℝ) / (x : ℝ)) < ε / 2 := by
          calc
            _ < (K : ℝ) * (ε / (2 * (K : ℝ))) :=
              mul_lt_mul_of_pos_left hxC' hKR
            _ = ε / 2 := by field_simp
        nlinarith

theorem exists_fullTruncatedGapAverage_limit
    (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n}) (hp2 : ∀ n, p n → 2 ≤ n)
    (hcount : (fun n : ℕ => (Nat.count p n : ℝ)) =o[atTop]
      (fun n : ℕ => Real.sqrt (n : ℝ)))
    (hsum : Summable fun r : ℕ => ((Nat.nth p r : ℝ)⁻¹))
    (H : ℕ) :
    ∃ L : ℝ, Tendsto (fullTruncatedGapAverage p H) atTop (𝓝 L) := by
  apply exists_tendsto_of_uniform_eventual_approx
    (fullTruncatedGapAverage p H)
    (fun R => finiteTruncatedGapAverage p R H)
  · intro ε hε
    exact exists_prefix_eventually_full_finite_close
      p hp hp2 hcount hsum H ε hε
  · intro R
    exact ⟨finiteTruncatedGapLimit p R H,
      finiteTruncatedGapAverage_tendsto p hp hp2 R H⟩

theorem summable_inv_of_eventually_sq_le (a : ℕ → ℕ)
    (h : ∀ᶠ n in atTop, (n + 1) ^ 2 ≤ a n) :
    Summable (fun n : ℕ => ((a n : ℝ)⁻¹)) := by
  have hs : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
    have hζ : Summable (fun n : ℕ => (((n : ℝ) ^ 2)⁻¹)) :=
      Real.summable_nat_pow_inv.mpr (by omega)
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      hζ.comp_injective Nat.succ_injective
  apply Summable.of_norm_bounded_eventually_nat hs
  filter_upwards [h] with n hn
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have ha : 0 < (a n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < (n + 1) ^ 2) hn)
  have hb : 0 < (((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  rw [inv_le_inv₀ ha hb]
  exact_mod_cast hn

theorem summable_inv_nth_of_count_isLittleO_sqrt (p : ℕ → Prop) [DecidablePred p]
    (hp : Set.Infinite {n | p n})
    (hcount : (fun x : ℕ => (Nat.count p x : ℝ)) =o[atTop]
      (fun x : ℕ => Real.sqrt (x : ℝ))) :
    Summable (fun n : ℕ => ((Nat.nth p n : ℝ)⁻¹)) := by
  apply summable_inv_of_eventually_sq_le
  have ht : Tendsto (Nat.nth p) atTop atTop :=
    (Nat.nth_injective hp).nat_tendsto_atTop
  have hb := hcount.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hbc : ∀ᶠ n in atTop,
      ‖(Nat.count p (Nat.nth p n) : ℝ)‖ ≤
        (1 / 2 : ℝ) * ‖Real.sqrt (Nat.nth p n : ℝ)‖ := ht.eventually hb
  filter_upwards [hbc, eventually_ge_atTop 1] with n hn hnpos
  rw [Nat.count_nth_of_infinite hp n] at hn
  have hnreal : (n : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt (Nat.nth p n : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  have hsqrt : (2 : ℝ) * n ≤ Real.sqrt (Nat.nth p n : ℝ) := by
    linarith
  have hsquare : ((2 : ℝ) * n) ^ 2 ≤ (Nat.nth p n : ℝ) := by
    calc
      ((2 : ℝ) * n) ^ 2 ≤ (Real.sqrt (Nat.nth p n : ℝ)) ^ 2 :=
        (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).2 hsqrt
      _ = (Nat.nth p n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hcast : ((((n + 1) ^ 2 : ℕ) : ℝ)) ≤ (Nat.nth p n : ℝ) := by
    have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
    norm_num at hsquare ⊢
    nlinarith
  exact_mod_cast hcast

def restrictedForbidden (A : Set ℕ) (n : ℕ) : Prop := n ∈ A ∧ 2 ≤ n

noncomputable instance restrictedForbiddenDecidable (A : Set ℕ) :
    DecidablePred (restrictedForbidden A) := Classical.decPred _

theorem restricted_count_le_original_Icc (A : Set ℕ) (x : ℕ) :
    Nat.count (restrictedForbidden A) x ≤
      ((Finset.Icc 1 x).filter (· ∈ A)).card := by
  rw [Nat.count_eq_card_filter_range]
  apply Finset.card_le_card
  intro n hn
  have hnr := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
  have hnp := (Finset.mem_filter.mp hn).2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨le_trans (by omega : 1 ≤ 2) hnp.2, hnr.le⟩, hnp.1⟩

theorem restricted_count_isLittleO
    (A : Set ℕ)
    (hA : (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ))) :
    (fun x : ℕ => (Nat.count (restrictedForbidden A) x : ℝ))
      =o[atTop] (fun x : ℕ => Real.sqrt (x : ℝ)) := by
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hb := hA.bound hc
  filter_upwards [hb] with x hx
  have hleR : (Nat.count (restrictedForbidden A) x : ℝ) ≤
      (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ) := by
    exact_mod_cast restricted_count_le_original_Icc A x
  have hx' : (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ) ≤
      c * Real.sqrt (x : ℝ) := by
    simpa only [Real.norm_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤
        (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ) by positivity),
      abs_of_nonneg (Real.sqrt_nonneg _)] using hx
  simpa only [Real.norm_natCast, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (Nat.count (restrictedForbidden A) x : ℝ) by positivity),
    abs_of_nonneg (Real.sqrt_nonneg _)] using hleR.trans hx'

theorem restrictedForbidden_infinite (A : Set ℕ) (hA : A.Infinite) :
    Set.Infinite {n | restrictedForbidden A n} := by
  by_contra hnot
  rw [Set.not_infinite] at hnot
  have hsub : A ⊆ {n | restrictedForbidden A n} ∪ Set.Iio 2 := by
    intro n hn
    by_cases hn2 : 2 ≤ n
    · exact Set.mem_union_left _ ⟨hn, hn2⟩
    · apply Set.mem_union_right
      change n < 2
      omega
  exact hA ((hnot.union (Set.finite_Iio 2)).subset hsub)
end SquarefreeGapProof
open Filter Finset Asymptotics
namespace PrimeSquareGaps
private def A : Set ℕ := {n | ∃ p, Nat.Prime p ∧ n=p^2}

private theorem card_le (N : ℕ) [DecidablePred (· ∈ A)] :
    ((Icc 1 N).filter (· ∈ A)).card ≤ N.sqrt.primeCounting := by
  rw [←Nat.primesLE_card_eq_primeCounting]
  apply le_trans (b := ((Nat.primesLE N.sqrt).image (·^2)).card) _ (card_image_le)
  apply card_le_card
  intro w hw
  obtain ⟨hI,p,hp,rfl⟩ := mem_filter.mp hw
  exact mem_image.mpr ⟨p,Nat.mem_primesLE.mpr ⟨Nat.le_sqrt'.mpr (mem_Icc.mp hI).2,hp⟩,rfl⟩

open Classical in
private theorem thin : (fun x : ℕ => (((Icc 1 x).filter (· ∈ A)).card : ℝ))
    =o[atTop] (fun x : ℕ => Real.sqrt (x:ℝ)) := by
  have htop : Tendsto (fun N : ℕ => Real.sqrt (N:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [htop.eventually (Chebyshev.eventually_primeCounting_le (ε:=1) zero_lt_one),
    (Real.tendsto_log_atTop.comp htop).eventually_ge_atTop ((Real.log 4+1)/c),
    htop.eventually_gt_atTop 1] with N h hlog hpos
  simp only [Real.nat_floor_real_sqrt_eq_nat_sqrt] at h
  simp only [Real.norm_eq_abs,Nat.abs_cast,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (show ((((Icc 1 N).filter (· ∈ A)).card : ℕ):ℝ) ≤ N.sqrt.primeCounting by exact_mod_cast card_le N).trans
  apply h.trans
  apply (div_le_iff₀ (Real.log_pos hpos)).mpr
  have h1 : Real.log 4+1 ≤ Real.log (Real.sqrt N) * c := (div_le_iff₀ hc).mp hlog
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (Real.sqrt_nonneg (N:ℝ))]


end PrimeSquareGaps
namespace SquarefreeGapBridge
open Filter Finset Erdos145 SquarefreeGapProof
open scoped Topology
private lemma frequency_input (K : ℕ) : ∃ L : ℝ, Tendsto (fun x : ℝ => 1/x *
  ∑ n ∈ (A x).filter (fun n => s (n+1) - s n < K), ((s (n+1) - s n : ℕ) : ℝ)^2) atTop (𝓝 L) := by
  classical
  let P := restrictedForbidden PrimeSquareGaps.A
  have hinf : PrimeSquareGaps.A.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro a
    obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (a+1)
    exact ⟨p^2,⟨p,hprime,rfl⟩,by nlinarith [hprime.two_le]⟩
  have hP : Set.Infinite {n | P n} := restrictedForbidden_infinite _ hinf
  have hthin := restricted_count_isLittleO _ PrimeSquareGaps.thin
  have hsum := summable_inv_nth_of_count_isLittleO_sqrt P hP hthin
  obtain ⟨L,hL⟩ := exists_fullTruncatedGapAverage_limit P hP (fun n hn => hn.2) hthin hsum K
  have heq : divisorSifted P = Squarefree := by
    funext n
    apply propext
    constructor
    · intro hn
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro p hp hdiv
      exact hn.2 (p^2) ⟨⟨p,hp,rfl⟩, by nlinarith [hp.two_le]⟩ (by simpa [pow_two] using hdiv)
    · intro hn
      refine ⟨Nat.pos_of_ne_zero hn.ne_zero,?_⟩
      rintro a ⟨⟨p,hp,rfl⟩,_⟩ hd
      exact Nat.squarefree_iff_prime_squarefree.mp hn p hp (by simpa [pow_two] using hd)
  let F (N : ℕ) : ℝ :=
    (∑ i ∈ (range (Nat.count Squarefree N)).filter (fun i => s (i+1)-s i < K),
      ((s (i+1)-s i : ℕ) : ℝ)^2) / N
  have hF : Tendsto F atTop (𝓝 L) := by
    apply hL.congr'
    filter_upwards with N
    rw [fullTruncatedGapAverage,heq,sum_truncatedGapCost_eq_gap_sum Squarefree Nat.squarefree_infinite K N]
    simp [F,s]
  let b (x : ℝ) := ⌊x⌋₊ + 1
  have hb : Tendsto b atTop atTop := tendsto_atTop_mono (fun x => Nat.le_succ ⌊x⌋₊) tendsto_nat_floor_atTop
  have hratio : Tendsto (fun x : ℝ => (b x : ℝ)/x) atTop (𝓝 1) := by
    have hh := (tendsto_nat_floor_div_atTop (R := ℝ)).add (tendsto_inv_atTop_zero (𝕜 := ℝ))
    simpa [b,add_div,one_div] using hh
  refine ⟨L, ?_⟩
  have hh := ((hF.comp hb).mul hratio)
  rw [mul_one] at hh
  apply hh.congr'
  filter_upwards with x
  have hr : A x = range (Nat.count Squarefree (b x)) := by
    ext i
    simp only [A, mem_preimage, mem_Icc, Nat.zero_le, true_and, mem_range]
    rw [Nat.lt_nth_iff_count_lt Nat.squarefree_infinite]
    exact Nat.lt_succ_iff.symm
  rw [hr]
  have hx : (b x : ℝ) ≠ 0 := by dsimp [b]; positivity
  simp only [Function.comp_apply,F]
  field_simp
end SquarefreeGapBridge

theorem OMA.solution : OMA.R_Erdos145_erdos_145_variants_le_three_R1.H1 := SquarefreeGapBridge.frequency_input
