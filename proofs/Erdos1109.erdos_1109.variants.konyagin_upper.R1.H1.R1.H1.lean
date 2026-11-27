import OMAReductions.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1
import Mathlib

-- Step Erdos1109.erdos_1109.variants.konyagin_upper.R1.H1.R1.H1: hypothesis H1 of reduction Erdos1109.erdos_1109.variants.konyagin_upper.R1.H1.R1
-- Credit: @ivillar

/-!
# Off-diagonal collisions modulo prime squares: the trivial bound

Counting by pairs `(a, b)` of distinct elements of `A ⊆ [1, N]`: a prime `p ≤ X` with
`a ≡ b (mod p²)` divides `d = |a - b| ≤ N`, and `d` has at most `log N / log 2 ≤ 2 log N` prime
factors, each contributing at most `X²`.
-/

namespace Erdos1109OffDiagStep

open Finset Real Filter
open scoped Classical

lemma card_primeFactors_le (N d : ℕ) (hd : 0 < d) (hdN : d ≤ N) :
    (d.primeFactors.card : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  have h1 : 2 ^ d.primeFactors.card ≤ ∏ p ∈ d.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ d.primeFactors, p ≤ d := Nat.le_of_dvd hd (Nat.prod_primeFactors_dvd d)
  have h3 : ((2 ^ d.primeFactors.card : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast h1.trans (h2.trans hdN)
  have h4 : Real.log ((2 ^ d.primeFactors.card : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by positivity) h3
  rw [Nat.cast_pow, Real.log_pow] at h4
  have h5 : (0.5 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h6 : (0 : ℝ) ≤ (d.primeFactors.card : ℝ) := Nat.cast_nonneg _
  push_cast at h4
  nlinarith

lemma pair_bound (N X a b : ℕ) (hb : b ≤ N) (hab : a < b) :
    ∑ p ∈ (range (X + 1)).filter Nat.Prime,
      (if a % (p * p) = b % (p * p) then ((p * p : ℕ) : ℝ) else 0) ≤
      2 * (X : ℝ) ^ 2 * Real.log (N : ℝ) := by
  have hd : 0 < b - a := Nat.sub_pos_of_lt hab
  have hdN : b - a ≤ N := (Nat.sub_le b a).trans hb
  rw [← Finset.sum_filter]
  have hsub : ((range (X + 1)).filter Nat.Prime).filter (fun p => a % (p * p) = b % (p * p)) ⊆
      (b - a).primeFactors := by
    intro p hp
    rw [mem_filter, mem_filter] at hp
    obtain ⟨⟨-, hpp⟩, hmod⟩ := hp
    have hdvd : p * p ∣ b - a := (Nat.modEq_iff_dvd' hab.le).mp hmod
    exact Nat.mem_primeFactors.mpr ⟨hpp, (dvd_mul_right p p).trans hdvd, hd.ne'⟩
  have hX0 : (0 : ℝ) ≤ (X : ℝ) ^ 2 := by positivity
  calc ∑ p ∈ ((range (X + 1)).filter Nat.Prime).filter (fun p => a % (p * p) = b % (p * p)),
        ((p * p : ℕ) : ℝ)
      ≤ ∑ _p ∈ ((range (X + 1)).filter Nat.Prime).filter
          (fun p => a % (p * p) = b % (p * p)), (X : ℝ) ^ 2 := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        rw [mem_filter, mem_filter, mem_range] at hp
        have hpX : (p : ℝ) ≤ (X : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hp.1.1
        have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
        push_cast
        nlinarith
    _ = ((((range (X + 1)).filter Nat.Prime).filter
          (fun p => a % (p * p) = b % (p * p))).card : ℝ) * (X : ℝ) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((b - a).primeFactors.card : ℝ) * (X : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) hX0
    _ ≤ 2 * Real.log (N : ℝ) * (X : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (card_primeFactors_le N (b - a) hd hdN) hX0
    _ = 2 * (X : ℝ) ^ 2 * Real.log (N : ℝ) := by ring

theorem offdiag : ∀ N X : ℕ, 1 ≤ N → ∀ A ⊆ Icc 1 N,
  let P := (range (X+1)).filter Nat.Prime
  let C (p : ℕ) := ((A ×ˢ A).filter (fun t => t.1 ≠ t.2 ∧ t.1%(p*p) = t.2%(p*p))).card
  ∑ p ∈ P, ((p*p:ℕ):ℝ)*C p ≤ 2*(X:ℝ)^2*log N*(A.card:ℝ)^2 := by
  intro N X hN A hA P C
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hC : ∀ p : ℕ, ((p * p : ℕ) : ℝ) * (C p : ℝ) =
      ∑ t ∈ A ×ˢ A, (if (t.1 ≠ t.2 ∧ t.1 % (p * p) = t.2 % (p * p)) then ((p * p : ℕ) : ℝ)
        else 0) := by
    intro p
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have key : ∀ t ∈ A ×ˢ A, ∑ p ∈ P,
      (if (t.1 ≠ t.2 ∧ t.1 % (p * p) = t.2 % (p * p)) then ((p * p : ℕ) : ℝ) else 0) ≤
      2 * (X : ℝ) ^ 2 * Real.log (N : ℝ) := by
    intro t ht
    obtain ⟨hta, htb⟩ := mem_product.mp ht
    have ha := (mem_Icc.mp (hA hta)).2
    have hb := (mem_Icc.mp (hA htb)).2
    rcases lt_trichotomy t.1 t.2 with hlt | heq | hgt
    · refine le_trans (Finset.sum_le_sum (fun p _ => ?_)) (pair_bound N X t.1 t.2 hb hlt)
      by_cases hc : t.1 % (p * p) = t.2 % (p * p)
      · rw [if_pos ⟨hlt.ne, hc⟩, if_pos hc]
      · rw [if_neg (fun h => hc h.2), if_neg hc]
    · have hz : ∑ p ∈ P, (if (t.1 ≠ t.2 ∧ t.1 % (p * p) = t.2 % (p * p)) then
          ((p * p : ℕ) : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero (fun p _ => if_neg (fun h => h.1 heq))
      rw [hz]
      positivity
    · refine le_trans (Finset.sum_le_sum (fun p _ => ?_)) (pair_bound N X t.2 t.1 ha hgt)
      by_cases hc : t.2 % (p * p) = t.1 % (p * p)
      · rw [if_pos ⟨hgt.ne', hc.symm⟩, if_pos hc]
      · rw [if_neg (fun h => hc h.2.symm), if_neg hc]
  calc ∑ p ∈ P, ((p * p : ℕ) : ℝ) * (C p : ℝ)
      = ∑ p ∈ P, ∑ t ∈ A ×ˢ A, (if (t.1 ≠ t.2 ∧ t.1 % (p * p) = t.2 % (p * p)) then
          ((p * p : ℕ) : ℝ) else 0) := Finset.sum_congr rfl (fun p _ => hC p)
    _ = ∑ t ∈ A ×ˢ A, ∑ p ∈ P, (if (t.1 ≠ t.2 ∧ t.1 % (p * p) = t.2 % (p * p)) then
          ((p * p : ℕ) : ℝ) else 0) := Finset.sum_comm
    _ ≤ ∑ _t ∈ A ×ˢ A, 2 * (X : ℝ) ^ 2 * Real.log (N : ℝ) := Finset.sum_le_sum key
    _ = 2 * (X : ℝ) ^ 2 * Real.log (N : ℝ) * (A.card : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
        push_cast
        ring

end Erdos1109OffDiagStep

theorem OMA.solution : OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R1_H1_R1.H1 :=
  Erdos1109OffDiagStep.offdiag
