import OMAReductions.R_Erdos32_erdos_32_variants_log_squared_R1
import Mathlib

/-! A block construction for the sparse complement theorem of Erdős (1954).
A block with logarithmic endpoints 4L and 8L is split at 6L. In each
half, shifts in a fixed interval give a finite covering problem. The analytic
input is a lower bound for primes in the translated intervals, and the
combinatorial input is a finite hitting-set lemma. Taking L = 2^j and
summing the cardinalities gives the required squared-logarithm bound. -/
open Finset Filter Real
namespace OMA.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1

/-- At each of two logarithmic scales, a short interval contains enough primes
to give a positive proportion, of order 1/L, of usable shifts. -/
def H1 : Prop :=
  ∃ C : ℕ, 1≤C ∧ ∀ᶠ L : ℕ in atTop, ∀ i : ℕ, i<2 →
    let t := (4+2*i)*L
    let Y := 2^(t-2)
    ∀ n ∈ Ico (2^t) (2^(t+2*L)), Even n →
      Y ≤ C*L*((Ico Y (2*Y)).filter fun a => (n-a).Prime ∧ a≤n).card

/-- A finite family of at most 2^(8L) targets, each incident to at least a
1/(CL) fraction of the possible shifts, admits a hitting set of size O_C(L²). -/
def H2 : Prop :=
  ∀ C : ℕ, 1≤C → ∃ D : ℕ, ∀ (L : ℕ) (U T : Finset ℕ) (R : ℕ → ℕ → Prop)
    [DecidableRel R], 1≤L → U.Nonempty → T.card ≤ 2^(8*L) →
    (∀ n ∈ T, U.card ≤ C*L*(U.filter (R n)).card) →
    ∃ B ⊆ U, B.card ≤ D*L^2 ∧ ∀ n ∈ T, ∃ a ∈ B, R n a

lemma finite_block (C D L : ℕ) (hL : 1≤L)
    (primes : ∀ i : ℕ, i<2 →
      let t := (4+2*i)*L
      let Y := 2^(t-2)
      ∀ n ∈ Ico (2^t) (2^(t+2*L)), Even n →
        Y ≤ C*L*((Ico Y (2*Y)).filter fun a => (n-a).Prime ∧ a≤n).card)
    (cover : ∀ (L : ℕ) (U T : Finset ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R],
      1≤L → U.Nonempty → T.card ≤ 2^(8*L) → (∀ n ∈ T, U.card ≤ C*L*(U.filter (R n)).card) →
      ∃ B ⊆ U, B.card ≤ D*L^2 ∧ ∀ n ∈ T, ∃ a ∈ B, R n a) :
    ∃ B : Finset ℕ, B.card ≤ 2*D*L^2 ∧ (∀ a ∈ B, 2^L≤a) ∧
      ∀ n ∈ Ico (2^(4*L)) (2^(8*L)), Even n → ∃ p, p.Prime ∧ ∃ a ∈ B, n=p+a := by
  classical
  have piece (i : ℕ) (hi : i<2) :
      let t := (4+2*i)*L
      ∃ B : Finset ℕ, B.card ≤ D*L^2 ∧ (∀ a ∈ B, 2^L≤a) ∧
        ∀ n ∈ Ico (2^t) (2^(t+2*L)), Even n → ∃ p, p.Prime ∧ ∃ a ∈ B, n=p+a := by
    let t := (4+2*i)*L
    let Y := 2^(t-2)
    let U := Ico Y (2*Y)
    let T := (Ico (2^t) (2^(t+2*L))).filter Even
    have hY : 0<Y := by dsimp [Y]; positivity
    have hc : U.card = Y := by simp [U]; omega
    have ht : t+2*L≤8*L := by dsimp [t]; have hh := Nat.mul_le_mul_right L (show 4+2*i≤6 by omega); omega
    have hT : T.card ≤ 2^(8*L) := calc
      _ ≤ (Ico (2^t) (2^(t+2*L))).card := card_filter_le ..
      _ ≤ 2^(t+2*L) := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by decide) ht
    obtain ⟨B,hBU,hcard,hB⟩ := cover L U T (fun n a => (n-a).Prime ∧ a≤n) hL
      (card_pos.mp (by rwa [hc])) hT (fun n hn => hc ▸ primes i hi n (mem_filter.mp hn).1 (mem_filter.mp hn).2)
    refine ⟨B,hcard,fun a ha => le_trans ?_ (mem_Ico.mp (hBU ha)).1,?_⟩
    · apply Nat.pow_le_pow_right (by decide)
      dsimp [t]
      have hh := Nat.mul_le_mul_right L (show 4≤4+2*i by omega)
      omega
    · intro n hn he
      obtain ⟨a,ha,hprime,han⟩ := hB n (mem_filter.mpr ⟨hn,he⟩)
      exact ⟨n-a,hprime,a,ha,by omega⟩
  obtain ⟨B,hB,hlo,hp⟩ := piece 0 (by decide)
  obtain ⟨B',hB',hlo',hp'⟩ := piece 1 (by decide)
  norm_num at hp hp'
  refine ⟨B∪B', (card_union_le ..).trans (by nlinarith only [hB,hB']),?_,?_⟩
  · intro a ha
    exact (mem_union.mp ha).elim (hlo a) (hlo' a)
  · intro n hn he
    obtain ⟨hn₁,hn₂⟩ := mem_Ico.mp hn
    by_cases hmid : n<2^(6*L)
    · obtain ⟨p,hpr,a,ha,heq⟩ := hp n hn₁ (by simpa only [show 4*L+2*L=6*L by omega] using hmid) he
      exact ⟨p,hpr,a,mem_union_left _ ha,heq⟩
    · obtain ⟨p,hpr,a,ha,heq⟩ := hp' n (le_of_not_gt hmid) (by simpa only [show 6*L+2*L=8*L by omega] using hn₂) he
      exact ⟨p,hpr,a,mem_union_right _ ha,heq⟩
end OMA.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1

open Finset Filter Real
namespace OMA.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1
lemma window (u : ℕ → ℕ) (n : ℕ) (h₀ : u 0 ≤ n) (h : ∃ j, n < u j) :
    ∃ j, u j ≤ n ∧ n < u (j+1) := by
  classical
  have hs := Nat.find_spec h
  cases he : Nat.find h with
  | zero => rw [he] at hs; omega
  | succ j =>
    refine ⟨j, le_of_not_gt (Nat.find_min h (show j < Nat.find h by omega)), ?_⟩
    simpa only [he] using hs

lemma geometric (k : ℕ) : ∑ j ∈ range (k+1), ((2:ℕ)^j)^2 ≤ 2*(2^k)^2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,pow_succ (2:ℕ) k]
    nlinarith only [ih]

open scoped Classical in
lemma join_blocks (D j₀ : ℕ) (B : ℕ → Finset ℕ)
    (size : ∀ j, (B j).card ≤ D*(2^j)^2)
    (low : ∀ j, ∀ a ∈ B j, 2^(2^j) ≤ a)
    (covers : ∀ j ≥ j₀, ∀ n ∈ Ico (2^(4*2^j)) (2^(8*2^j)), Even n →
      ∃ p, p.Prime ∧ ∃ a ∈ B j, n=p+a) :
    ∃ A : Set ℕ, ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (((Icc 1 N).filter (· ∈ A)).card : ℝ) ≤ C*(log N)^2 ∧
      (((Icc 1 N).filter (fun n => Even n ∧ ¬∃ p, p.Prime ∧ ∃ a ∈ A, n=p+a)).card:ℝ) ≤ C*(log N)^2 := by
  classical
  let A : Set ℕ := {a | ∃ j, a ∈ B j}
  let M : ℕ := 2^(4*2^j₀)
  have hit (n : ℕ) (hn : M ≤ n) (he : Even n) : ∃ p, p.Prime ∧ ∃ a ∈ A, n=p+a := by
    let u (j : ℕ) := 2^(4*2^j)
    have mono : StrictMono u := by
      intro i j hij
      apply Nat.pow_lt_pow_right (by decide)
      exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by decide) hij) (by decide)
    obtain ⟨j,hj,hj'⟩ := window u n ((mono.monotone (Nat.zero_le j₀)).trans hn)
      ⟨n+1,(show n < n+1 by omega).trans_le (mono.id_le (n+1))⟩
    have hj₀ : j₀ ≤ j := by
      by_contra! h
      exact (not_lt_of_ge (le_trans (mono.monotone (show j+1≤j₀ by omega)) hn)) hj'
    obtain ⟨p,hp,a,ha,hs⟩ := covers j hj₀ n (mem_Ico.mpr ⟨hj,by
      dsimp [u] at hj'
      simpa only [pow_succ (2:ℕ) j,show 4*(2^j*2)=8*2^j by ring] using hj'⟩) he
    exact ⟨p,hp,a,⟨j,ha⟩,hs⟩
  refine ⟨A,max (8*(D:ℝ)) (M:ℝ),8,?_⟩
  intro N hN
  have hN' : (8:ℝ)≤N := by exact_mod_cast hN
  have hlog : 1 ≤ log (N:ℝ) := by
    apply (le_log_iff_exp_le (by positivity)).mpr
    linarith [exp_one_lt_d9]
  have hlog2 : 1/2 ≤ log 2 := by linarith [log_two_gt_d9]
  constructor
  · let v (j : ℕ) := 2^(2^j)
    have mono : StrictMono v := fun _ _ h => Nat.pow_lt_pow_right (by decide) (Nat.pow_lt_pow_right (by decide) h)
    obtain ⟨k,hk,hk'⟩ := window v N (by dsimp [v]; omega)
      ⟨N+1,(show N<N+1 by omega).trans_le (mono.id_le (N+1))⟩
    have incl : (Icc 1 N).filter (· ∈ A) ⊆ (range (k+1)).biUnion B := by
      intro a ha
      obtain ⟨hb,j,haj⟩ := mem_filter.mp ha
      refine mem_biUnion.mpr ⟨j,mem_range.mpr ?_,haj⟩
      exact mono.lt_iff_lt.mp ((low j a haj).trans_lt ((mem_Icc.mp hb).2.trans_lt hk'))
    have cnt : ((Icc 1 N).filter (· ∈ A)).card ≤ D*(2*(2^k)^2) := calc
      _ ≤ _ := card_le_card incl
      _ ≤ ∑ j ∈ range (k+1), (B j).card := card_biUnion_le
      _ ≤ ∑ j ∈ range (k+1), D*(2^j)^2 := sum_le_sum fun j _ => size j
      _ ≤ _ := by rw [←mul_sum]; exact Nat.mul_le_mul_left _ (geometric _)
    have hb : (2:ℝ)^k * log 2 ≤ log (N:ℝ) := by
      have h := log_le_log (by positivity : 0<(2:ℝ)^(2^k:ℕ)) (show (2:ℝ)^(2^k:ℕ)≤N by exact_mod_cast hk)
      simpa only [log_pow,Nat.cast_pow,Nat.cast_ofNat] using h
    have hb' : (2:ℝ)^k ≤ 2*log N := by
      have h := mul_le_mul_of_nonneg_left hlog2 (show 0≤(2:ℝ)^k by positivity)
      linarith
    have hsq := pow_le_pow_left₀ (by positivity : 0≤(2:ℝ)^k) hb' 2
    calc
      _ ≤ (D:ℝ)*(2*((2:ℝ)^k)^2) := by exact_mod_cast cnt
      _ ≤ 8*(D:ℝ)*(log N)^2 := by nlinarith only [mul_le_mul_of_nonneg_left hsq (show 0≤(D:ℝ) by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) (sq_nonneg _)
  · have incl : ((Icc 1 N).filter (fun n => Even n ∧ ¬∃ p, p.Prime ∧ ∃ a ∈ A, n=p+a)) ⊆ range M := by
      intro n hn
      obtain ⟨_,he,hmiss⟩ := mem_filter.mp hn
      exact mem_range.mpr (lt_of_not_ge (fun h => hmiss (hit n h he)))
    calc
      _ ≤ (M:ℝ) := by exact_mod_cast (card_le_card incl).trans_eq (card_range M)
      _ ≤ (M:ℝ)*(log N)^2 := by
        have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hlog 2)
          (show 0≤(M:ℝ) by positivity)
        simpa using hh
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _)
end OMA.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1

open Finset Filter
namespace OMA.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1
theorem main : H1 → H2 → OMA.R_Erdos32_erdos_32_variants_log_squared_R1.H1 := by
  classical
  rintro ⟨C,hC,hprime⟩ hcover
  obtain ⟨D,hD⟩ := hcover C hC
  obtain ⟨j₀,hj⟩ := eventually_atTop.mp hprime
  have blocks (j : ℕ) : ∃ B : Finset ℕ, B.card ≤ (2*D)*(2^j)^2 ∧
      (∀ a ∈ B, 2^(2^j)≤a) ∧ (j₀≤j → ∀ n ∈ Ico (2^(4*2^j)) (2^(8*2^j)), Even n →
           ∃ p, p.Prime ∧ ∃ a ∈ B, n=p+a) := by
    by_cases hh : j₀≤j
    · have hL : 1≤(2:ℕ)^j := Nat.one_le_pow _ _ (by decide)
      have hj' : j₀≤2^j := hh.trans (j.lt_two_pow_self.le)
      obtain ⟨B,hs,hl,hp⟩ := finite_block C D (2^j) hL (hj _ hj') hD
      exact ⟨B,hs,hl,fun _ => hp⟩
    · exact ⟨∅,by simp,by simp,fun h => (hh h).elim⟩
  choose B hs hl hp using blocks
  exact join_blocks (2*D) j₀ B hs hl hp
end OMA.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1

