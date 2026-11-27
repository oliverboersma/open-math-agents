import FormalConjectures.ErdosProblems.«999»
import Mathlib

/-! Proof of Erdos999.erdos_999.variants.easy_direction via the Borel-Cantelli lemma. -/

open MeasureTheory Filter Set Finset

namespace OMA_Erdos999_Easy

private lemma card_coprime_Ico_three (q : ℕ) (hq : 0 < q) :
    ((Finset.Ico (-(q : ℤ)) (2 * (q : ℤ))).filter (fun p : ℤ => Int.gcd p q = 1)).card ≤
      3 * Nat.totient q := by
  let coprime := (Finset.range q).filter (fun k : ℕ => Nat.Coprime q k)
  let left := coprime.image (fun k : ℕ => (k : ℤ) - (q : ℤ))
  let center := coprime.image (fun k : ℕ => (k : ℤ))
  let right := coprime.image (fun k : ℕ => (k : ℤ) + (q : ℤ))
  have hsub : (Finset.Ico (-(q : ℤ)) (2 * (q : ℤ))).filter (fun p : ℤ => Int.gcd p q = 1) ⊆
      left ∪ center ∪ right := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    rcases hp with ⟨⟨hlo, hhi⟩, hgcd⟩
    simp only [left, center, right, coprime, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, Finset.mem_range]
    by_cases h1 : p < 0
    · left; left
      refine ⟨(p + q).toNat, ⟨by omega, ?_⟩, by omega⟩
      have hcast : ((p + q).toNat : ℤ) = p + q := Int.toNat_of_nonneg (by omega)
      have hg : Int.gcd (p + q) q = 1 := by
        rw [Int.gcd_comm, show (p : ℤ) + q = p + 1 * q by ring, Int.gcd_add_mul_right_right, Int.gcd_comm]
        exact hgcd
      rw [← hcast, Int.gcd_natCast_natCast] at hg
      exact Nat.coprime_iff_gcd_eq_one.mpr (by rw [Nat.gcd_comm]; exact hg)
    · by_cases h2 : p < q
      · left; right
        refine ⟨p.toNat, ⟨by omega, ?_⟩, by omega⟩
        have hcast : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (by omega)
        rw [← hcast, Int.gcd_natCast_natCast] at hgcd
        exact Nat.coprime_iff_gcd_eq_one.mpr (by rw [Nat.gcd_comm]; exact hgcd)
      · right
        refine ⟨(p - q).toNat, ⟨by omega, ?_⟩, by omega⟩
        have hcast : ((p - q).toNat : ℤ) = p - q := Int.toNat_of_nonneg (by omega)
        have hg : Int.gcd (p - q) q = 1 := by
          rw [Int.gcd_comm, show (p : ℤ) - q = p + (-1 : ℤ) * q by ring, Int.gcd_add_mul_right_right, Int.gcd_comm]
          exact hgcd
        rw [← hcast, Int.gcd_natCast_natCast] at hg
        exact Nat.coprime_iff_gcd_eq_one.mpr (by rw [Nat.gcd_comm]; exact hg)
  have htot : coprime.card = Nat.totient q :=
    (Nat.totient_eq_card_coprime q).symm
  calc ((Finset.Ico (-(q : ℤ)) (2 * (q : ℤ))).filter (fun p : ℤ => Int.gcd p q = 1)).card
      ≤ (left ∪ center ∪ right).card :=
        Finset.card_le_card hsub
    _ ≤ left.card + center.card + right.card := by
        exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    _ ≤ Nat.totient q + Nat.totient q + Nat.totient q := by
        rw [← htot]
        exact Nat.add_le_add (Nat.add_le_add Finset.card_image_le Finset.card_image_le) Finset.card_image_le
    _ = 3 * Nat.totient q := by ring

private lemma measure_ball_le (c r : ℝ) (_hr : 0 ≤ r) :
    volume {x : ℝ | |x - c| < r} ≤ ENNReal.ofReal (2 * r) := by
  have hsub : {x : ℝ | |x - c| < r} ⊆ Set.Ioo (c - r) (c + r) := by
    intro x hx
    have hx' : |x - c| < r := hx
    rw [abs_lt] at hx'
    exact ⟨by linarith, by linarith⟩
  calc volume {x : ℝ | |x - c| < r}
      ≤ volume (Set.Ioo (c - r) (c + r)) := measure_mono hsub
    _ = ENNReal.ofReal ((c + r) - (c - r)) := Real.volume_Ioo
    _ = ENNReal.ofReal (2 * r) := by congr 1; ring

end OMA_Erdos999_Easy

theorem OMA.solution : type_of% @Erdos999.erdos_999.variants.easy_direction := by
  intro f hf hae hsum
  -- Define A q as the set of x ∈ [0, 1] approximated with denominator q
  let A : ℕ → Set ℝ := fun q =>
    {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < q ∧
      ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - (p : ℝ) / (q : ℝ)| < f q / (q : ℝ)}
  -- Since ∑ φ(q) f(q) / q converges, φ(q) f(q) / q → 0, hence eventually f(q) / q < 1/2
  have htend : Tendsto (fun q : ℕ => (Nat.totient q : ℝ) * f q / (q : ℝ)) atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hev : ∀ᶠ q : ℕ in atTop, f q / (q : ℝ) < 1 / 2 := by
    have hlt := (tendsto_order.mp htend).2 (1 / 2) (by norm_num)
    filter_upwards [hlt, Filter.eventually_ge_atTop 1] with q hq hq1
    have htot1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hq1
    have hfq : 0 ≤ f q / (q : ℝ) := div_nonneg (hf q) (Nat.cast_nonneg q)
    have hle : f q / (q : ℝ) ≤ (Nat.totient q : ℝ) * f q / (q : ℝ) := by
      rw [mul_div_assoc]
      exact le_mul_of_one_le_left hfq htot1
    linarith
  rw [Filter.eventually_atTop] at hev
  obtain ⟨Q0, hQ0⟩ := hev
  let mass (q : ℕ) : ℝ := 6 * ((Nat.totient q : ℝ) * f q / (q : ℝ))
  -- For q ≥ Q0, measure (A q) ≤ ENNReal.ofReal (6 * φ(q) * f(q) / q)
  have hmeas_bound : ∀ q ≥ Q0,
      volume (A q) ≤ ENNReal.ofReal (mass q) := by
    intro q hq
    by_cases hq0 : q = 0
    · subst hq0
      have hA0 : A 0 = ∅ := by ext x; simp [A]
      rw [hA0, measure_empty]
      exact zero_le
    · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
      have hqr : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hqpos
      have hfhalf : f q / (q : ℝ) < 1 / 2 := hQ0 q hq
      let S : Finset ℤ := (Finset.Ico (-(q : ℤ)) (2 * (q : ℤ))).filter (fun p : ℤ => Int.gcd p q = 1)
      let interval (p : ℤ) : Set ℝ := {x : ℝ | |x - (p : ℝ) / (q : ℝ)| < f q / (q : ℝ)}
      have hsub : A q ⊆ ⋃ p ∈ S, interval p := by
        intro x hx
        rcases hx with ⟨⟨hx0, hx1⟩, _, p, hgcd, hdist⟩
        have hpS : p ∈ S := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hgcd⟩
          · have h1 : -1 / 2 < (p : ℝ) / (q : ℝ) := by
              have := (abs_lt.mp hdist).2; linarith
            have h2 : -(q : ℝ) < (p : ℝ) := by
              have h3 := (lt_div_iff₀ hqr).mp h1; linarith
            have hlt : -(q : ℤ) < p := by exact_mod_cast h2
            omega
          · have h1 : (p : ℝ) / (q : ℝ) < 3 / 2 := by
              have := (abs_lt.mp hdist).1; linarith
            have h2 : (p : ℝ) < 2 * (q : ℝ) := by
              have h3 := (div_lt_iff₀ hqr).mp h1; linarith
            exact_mod_cast h2
        exact Set.mem_biUnion hpS hdist
      have hcard : (S.card : ℝ) ≤ 3 * (Nat.totient q : ℝ) := by
        exact_mod_cast OMA_Erdos999_Easy.card_coprime_Ico_three q hqpos
      have hfq_nn : 0 ≤ f q / (q : ℝ) := div_nonneg (hf q) (Nat.cast_nonneg q)
      calc volume (A q)
          ≤ volume (⋃ p ∈ S, interval p) :=
            measure_mono hsub
        _ ≤ ∑ p ∈ S, volume (interval p) :=
            measure_biUnion_finset_le S _
        _ ≤ ∑ _p ∈ S, ENNReal.ofReal (2 * (f q / (q : ℝ))) :=
            Finset.sum_le_sum fun p _ => OMA_Erdos999_Easy.measure_ball_le _ _ hfq_nn
        _ = (S.card : ENNReal) * ENNReal.ofReal (2 * (f q / (q : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ENNReal.ofReal ((S.card : ℝ) * (2 * (f q / (q : ℝ)))) := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        _ ≤ ENNReal.ofReal (mass q) := by
            apply ENNReal.ofReal_le_ofReal
            calc (S.card : ℝ) * (2 * (f q / (q : ℝ)))
                ≤ (3 * (Nat.totient q : ℝ)) * (2 * (f q / (q : ℝ))) :=
                  mul_le_mul_of_nonneg_right hcard (by positivity)
              _ = mass q := by dsimp only [mass]; ring
  -- Show ∑' q, volume (A q) ≠ ∞
  have htsum_ne_top : (∑' q : ℕ, volume (A q)) ≠ ⊤ := by
    have hsum6 : Summable (fun q : ℕ => mass q) :=
      hsum.mul_left 6
    have htsum_tail : (∑' q : ℕ, ENNReal.ofReal (mass q)) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => by
        dsimp only [mass]
        have := hf q; positivity) hsum6]
      exact ENNReal.ofReal_ne_top
    -- Bound volume (A q) by ENNReal.ofReal (6 * ...) + (if q < Q0 then 1 else 0)
    have hle_all : ∀ q : ℕ, volume (A q) ≤
        ENNReal.ofReal (mass q) +
          (if q < Q0 then (1 : ENNReal) else 0) := by
      intro q
      by_cases hq : q < Q0
      · rw [if_pos hq]
        have hA_le1 : volume (A q) ≤ 1 := by
          calc volume (A q) ≤ volume (Set.Icc (0 : ℝ) 1) := measure_mono (fun x hx => hx.1)
            _ = 1 := by simp [Real.volume_Icc]
        exact le_trans hA_le1 le_add_self
      · rw [if_neg hq, add_zero]
        exact hmeas_bound q (Nat.le_of_not_lt hq)
    have hfin_ite : (∑' q : ℕ, if q < Q0 then (1 : ENNReal) else 0) ≠ ⊤ := by
      rw [tsum_eq_sum (s := Finset.range Q0) (fun q hq => by
        rw [Finset.mem_range, not_lt] at hq; rw [if_neg (not_lt.mpr hq)])]
      exact ENNReal.sum_lt_top.mpr (fun q _ => by split_ifs <;> simp) |>.ne
    have hsum_le : (∑' q : ℕ, volume (A q)) ≤
        (∑' q : ℕ, ENNReal.ofReal (mass q)) +
        (∑' q : ℕ, if q < Q0 then (1 : ENNReal) else 0) := by
      rw [← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum hle_all
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨htsum_tail, hfin_ite⟩) hsum_le
  -- By Borel-Cantelli, volume (limsup A atTop) = 0
  have hbc : volume (Filter.limsup A atTop) = 0 :=
    MeasureTheory.measure_limsup_atTop_eq_zero htsum_ne_top
  -- Yet almost every x ∈ [0, 1] lies in limsup A atTop
  have hIcc_ae : ∀ᵐ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → x ∈ Filter.limsup A atTop := by
    filter_upwards [hae] with x hx hIcc
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter, Set.mem_iUnion]
    intro N
    obtain ⟨q, hq_mem, hqN⟩ := hx.exists_gt N
    exact ⟨q, le_of_lt hqN, hIcc, hq_mem.1, hq_mem.2⟩
  have hvol_le : volume (Set.Icc (0 : ℝ) 1) ≤ volume (Filter.limsup A atTop) :=
    measure_mono_ae hIcc_ae
  rw [hbc, Real.volume_Icc, sub_zero, ENNReal.ofReal_one] at hvol_le
  exact one_ne_zero (le_antisymm hvol_le zero_le)
