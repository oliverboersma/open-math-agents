import OMAReductions.R_Erdos950_erdos_950_variants_debruijn_erdos_turan_R1
import Mathlib

/-! Divide prime gaps into dyadic distance ranges. The uniform interval sieve
bounds the harmonic contribution of each range around one prime by a constant.
Together with Chebyshev's estimate, the ranges below the k-th root scale
contribute O(N/k). Only the prime-pair estimate above this scale needs a sharp
leading constant. This localizes the logarithmic gap sum in Gorodetsky's
argument for the de Bruijn–Erdős–Turán second moment (MathOverflow 508491). -/
namespace OMA.R_Erdos950_erdos_950_variants_debruijn_erdos_turan_R1_H2_R1
open Finset Filter Real
open scoped Nat.Prime

def H1 : Prop := ∃ K : ℝ, 0 < K ∧ ∀ N p j : ℕ,
    let P := (range N).filter Nat.Prime
    ∑ q ∈ (P.erase p).filter (fun q => Nat.log 2 (Nat.dist p q) = j),
      (harmonic (Nat.dist p q) : ℝ) / Nat.dist p q ≤ K

def H2 : Prop := ∀ k : ℕ, 0 < k → ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    let P := (range N).filter Nat.Prime
    ∑ p ∈ P, ∑ q ∈ (P.erase p).filter (fun q => Nat.log 2 N / k ≤ Nat.log 2 (Nat.dist p q)),
      (1 + log (Nat.dist p q)) / Nat.dist p q ≤ (1+ε)*N

lemma short_rows (K : ℝ) (N p J : ℕ)
    (hs : ∀ j, ∑ q ∈ (((range N).filter Nat.Prime).erase p).filter
      (fun q => Nat.log 2 (Nat.dist p q) = j), (harmonic (Nat.dist p q) : ℝ) / Nat.dist p q ≤ K) :
    ∑ q ∈ (((range N).filter Nat.Prime).erase p).filter (fun q => Nat.log 2 (Nat.dist p q) < J),
      (harmonic (Nat.dist p q) : ℝ) / Nat.dist p q ≤ J*K := by
  let S := ((range N).filter Nat.Prime).erase p
  let bin (q : ℕ) := Nat.log 2 (Nat.dist p q)
  let w (q : ℕ) : ℝ := harmonic (Nat.dist p q) / (Nat.dist p q : ℝ)
  let U := S.filter (fun q => bin q < J)
  change ∑ q ∈ U, w q ≤ _
  have group := sum_fiberwise_of_maps_to (s := U) (t := range J) (g := bin)
    (fun q hq => mem_range.mpr (mem_filter.mp hq).2) w
  rw [←group]
  calc
    _ ≤ ∑ _ ∈ range J, K := sum_le_sum fun j hj => by
      have he : U.filter (fun q => bin q = j) = S.filter (fun q => bin q = j) := by
        ext q
        simp only [U,mem_filter]
        have hj' := mem_range.mp hj
        exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.symm ▸ hj'⟩,h.2⟩⟩
      rw [he]
      exact hs j
    _ = _ := by simp

lemma prime_budget : ∀ᶠ N : ℕ in atTop,
    ((((range N).filter Nat.Prime).card : ℝ) * Nat.log 2 N) ≤ (log 4+1)/log 2*N := by
  have hp := tendsto_natCast_atTop_atTop.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0:ℝ)<1))
  filter_upwards [hp,eventually_ge_atTop 2] with N hn hN
  have hlog : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  have h2 : 0 < log 2 := log_pos (by norm_num)
  have hcard : ((range N).filter Nat.Prime).card ≤ π N := by
    rw [←Nat.primesLE_card_eq_primeCounting]
    apply card_le_card
    intro p hp
    obtain ⟨hm,hp⟩ := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(mem_range.mp hm).le,hp⟩
  have hπ : (π N : ℝ) ≤ (log 4+1)*N/log N := by simpa using hn
  have hb : (Nat.log 2 N : ℝ) ≤ log N/log 2 := by simpa [logb] using natLog_le_logb N 2
  calc
    _ ≤ ((log 4+1)*N/log N) * (log N/log 2) :=
      mul_le_mul ((by exact_mod_cast hcard : ((((range N).filter Nat.Prime).card : ℝ)) ≤ π N).trans hπ)
        hb (by positivity) (by positivity)
    _ = _ := by field_simp <;> ring

theorem main : H1 → H2 → OMA.R_Erdos950_erdos_950_variants_debruijn_erdos_turan_R1.H2 := by
  rintro ⟨K,hK,hb⟩ hl ε hε
  let B := (log 4+1)/log 2
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨k,hk⟩ := exists_nat_gt (2*B*K/ε)
  have hkpos : 0 < k := by
    have hh : 0 < 2*B*K/ε := by positivity
    exact_mod_cast hh.trans hk
  have hkR : (0:ℝ) < k := by exact_mod_cast hkpos
  have hcoeff : B*K ≤ ε/2*k := by
    have := (div_lt_iff₀ hε).mp hk
    linarith
  filter_upwards [prime_budget,hl k hkpos (ε/2) (by positivity)] with N hπ hlong
  let P := (range N).filter Nat.Prime
  let J := Nat.log 2 N / k
  let s (p : ℕ) := (P.erase p).filter (fun q => Nat.log 2 (Nat.dist p q) < J)
  let l (p : ℕ) := (P.erase p).filter (fun q => J ≤ Nat.log 2 (Nat.dist p q))
  let w (p q : ℕ) : ℝ := harmonic (Nat.dist p q) / (Nat.dist p q : ℝ)
  let v (p q : ℕ) : ℝ := (1+log (Nat.dist p q))/(Nat.dist p q : ℝ)
  change ∑ p ∈ P, ∑ q ∈ P.erase p, w p q ≤ _
  have hsplit (p : ℕ) : ∑ q ∈ P.erase p, w p q =
      (∑ q ∈ s p, w p q) + ∑ q ∈ l p, w p q := by
    simpa [s,l,not_lt] using (sum_filter_add_sum_filter_not (s := P.erase p)
      (p := fun q => Nat.log 2 (Nat.dist p q) < J) (f := w p)).symm
  simp_rw [hsplit]
  rw [sum_add_distrib]
  have small : (∑ p ∈ P, ∑ q ∈ s p, w p q) ≤ (P.card : ℝ) * (J*K) := by
    calc
      _ ≤ ∑ _ ∈ P, (J:ℝ)*K := sum_le_sum fun p _ => short_rows K N p J (hb N p)
      _ = _ := by simp
  have hJ : (J:ℝ)*(k:ℝ) ≤ Nat.log 2 N := by exact_mod_cast Nat.div_mul_le_self (Nat.log 2 N) k
  have hbnd : (P.card:ℝ)*(J*K) ≤ ε/2*N := by
    apply (le_of_mul_le_mul_right _ hkR)
    calc
      (P.card:ℝ)*(J*K)*k = ((P.card:ℝ)*((J:ℝ)*k))*K := by ring
      _ ≤ ((P.card:ℝ)*(Nat.log 2 N))*K := by gcongr
      _ ≤ (B*N)*K := mul_le_mul_of_nonneg_right hπ hK.le
      _ = B*K*N := by ring
      _ ≤ ε/2*k*N := by gcongr
      _ = _ := by ring
  have large : (∑ p ∈ P, ∑ q ∈ l p, w p q) ≤ (1+ε/2)*N := by
    apply le_trans _ hlong
    apply sum_le_sum; intro p hp
    apply sum_le_sum; intro q hq
    dsimp [w]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact harmonic_le_one_add_log _
  linarith [small.trans hbnd,large]
end OMA.R_Erdos950_erdos_950_variants_debruijn_erdos_turan_R1_H2_R1
