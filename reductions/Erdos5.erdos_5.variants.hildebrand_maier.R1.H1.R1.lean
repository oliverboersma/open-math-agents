import OMAReductions.R_Erdos5_erdos_5_variants_hildebrand_maier_R1
import Mathlib

/-! A positive proportion of gaps exceeding A log p forces a bounded window
above A to recur. In the first t² gaps, omit the first t indices. Every
remaining prime has logarithm at least half the logarithm of t², and the sum
of all gaps is bounded by the prime at the right endpoint. -/

namespace OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1

open Finset Filter Real
open scoped Topology
open scoped Classical

/-- Positive lower density of large prime gaps, in the prime index.
See the theorem of positive density for large gaps, formalized in
openai/math, OAI.NumberTheory.PrimeGaps.Main. -/
def H1 : Prop := ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
  c * N ≤ (((range N).filter fun n => A * log (Nat.nth Nat.Prime n) < (primeGap n : ℝ)).card : ℝ)

/-- The upper Chebyshev estimate for the n-th prime. -/
def H2 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
  (Nat.nth Nat.Prime N : ℝ) ≤ C * N * log N

lemma sum_gaps (N : ℕ) : ∑ n ∈ range N, (primeGap n : ℝ) ≤ Nat.nth Nat.Prime N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,primeGap,Nat.cast_sub
      ((Nat.nth_strictMono Nat.infinite_setOfPred_prime) (Nat.lt_succ_self n)).le]
    linarith

theorem main : H1 → H2 → OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1.H1 := by
  intro density cheb A hA
  obtain ⟨c,hc,freq⟩ := density A hA
  obtain ⟨C,hC,hu⟩ := cheb
  let B := 8*C/c
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB.le,frequently_atTop.mpr ?_⟩
  intro M
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (freq.and hu)
  obtain ⟨T,hT⟩ := exists_nat_ge (2/c)
  let t := max M (max T (max N₀ 2))
  have htM : M ≤ t := le_max_left .. 
  have htT : T ≤ t := (le_max_left ..).trans (le_max_right ..)
  have htN : N₀ ≤ t := (le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..))
  have ht2 : 2 ≤ t := (le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..))
  have tpos : (0:ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have tc : 2 ≤ c * t := by
    have hh := (div_le_iff₀ hc).mp (hT.trans (Nat.cast_le.mpr htT))
    linarith
  have ltlog : 0 < log t := log_pos (by exact_mod_cast (show 1 < t by omega))
  obtain ⟨hn,hn'⟩ := hN₀ (t^2) (htN.trans (by nlinarith))
  let P := (range (t^2)).filter fun n => A * log (Nat.nth Nat.Prime n) < (primeGap n:ℝ)
  let S := P \ range t
  have hcard : c*(t:ℝ)^2/2 ≤ S.card := by
    change c*(t^2:ℕ) ≤ (P.card:ℝ) at hn
    push_cast at hn
    have hh := le_card_sdiff (range t) P
    rw [card_range] at hh
    have hh' : P.card ≤ S.card+t := by dsimp [S]; omega
    have r : (P.card:ℝ) ≤ S.card + (t:ℝ) := by exact_mod_cast hh'
    nlinarith [mul_le_mul_of_nonneg_right tc tpos.le]
  by_contra! bad
  have large (n : ℕ) (hn : n ∈ S) : B * log t ≤ (primeGap n : ℝ) := by
    obtain ⟨hp,ht⟩ := mem_sdiff.mp hn
    have hit := (mem_filter.mp hp).2
    have htn : t ≤ n := by simpa using ht
    have hbig := bad n (htM.trans htn) hit.le
    apply le_trans _ hbig.le
    apply mul_le_mul_of_nonneg_left _ hB.le
    exact Real.log_le_log tpos (by exact_mod_cast htn.trans (by have := Nat.add_two_le_nth_prime n; omega))
  have total : (S.card:ℝ) * (B * log t) ≤ (Nat.nth Nat.Prime (t^2):ℝ) := calc
    _ = ∑ _n ∈ S, B * log t := by simp
    _ ≤ ∑ n ∈ S, (primeGap n:ℝ) := sum_le_sum large
    _ ≤ ∑ n ∈ range (t^2), (primeGap n:ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg (sdiff_subset.trans (filter_subset _ _))
      exact fun n _ _ => Nat.cast_nonneg _
    _ ≤ _ := sum_gaps _
  have high : c*(t:ℝ)^2/2*(B*log t) ≤ C*(t:ℝ)^2*(2*log t) := by
    apply (mul_le_mul_of_nonneg_right hcard (mul_nonneg hB.le ltlog.le)).trans
    exact total.trans (by simpa only [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] using hn')
  have eq : c*(t:ℝ)^2/2*(B*log t) = 4 * (C*(t:ℝ)^2*log t) := by dsimp [B]; field_simp; ring
  rw [eq] at high
  nlinarith only [high,mul_pos (mul_pos hC (sq_pos_of_pos tpos)) ltlog]

end OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_R1_H1_R1
