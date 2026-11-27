import OMAStatements.S_oeis_a067730
import Mathlib

namespace OMA.OddSigmaHelpers
open Finset ArithmeticFunction

lemma geom_bound (p e : ℕ) (c : ℚ) (hc : 1 ≤ c) (hpc : c + p ≤ c*p) :
    ∑ i ∈ range (e+1), (p:ℚ)^i ≤ c*(p:ℚ)^e := by
  induction e with
  | zero => simpa using hc
  | succ e ih =>
    rw [sum_range_succ, pow_succ]
    have h := mul_le_mul_of_nonneg_left hpc (show (0:ℚ) ≤ (p:ℚ)^e by positivity)
    linarith only [ih,h]

lemma sigma_upper {m : ℕ} (hm : m ≠ 0) (c : ℕ → ℚ)
    (bounds : ∀ p ∈ m.primeFactors, 1 ≤ c p ∧ c p + p ≤ c p * p) :
    (sigma 1 m : ℚ) ≤ (∏ p ∈ m.primeFactors, c p) * m := by
  have hs := sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k:=1) hm
  simp only [mul_one] at hs
  have hv : (m:ℚ) = ∏ p ∈ m.primeFactors, (p:ℚ)^m.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hm
  rw [hs]
  push_cast
  conv_rhs => rw [hv, ← prod_mul_distrib]
  first
  | exact Finset.prod_le_prod (fun _ _ => by positivity) (fun p hp => geom_bound p _ (c p) (bounds p hp).1 (bounds p hp).2)
  | exact Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun p hp => geom_bound p _ (c p) (bounds p hp).1 (bounds p hp).2)

/-- For primes at least 13, each Euler factor is at most 13/12. The four smaller odd primes receive individual correction factors. -/
lemma sparse_sigma {m : ℕ} (hm : Odd m) (hcard : m.primeFactors.card ≤ 3) :
    (sigma 1 m : ℚ) ≤ (m:ℚ)*(13/12)^3 *
      ((if 3 ∣ m then 18/13 else 1) * (if 5 ∣ m then 15/13 else 1) *
       (if 7 ∣ m then 14/13 else 1) * (if 11 ∣ m then 66/65 else 1)) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  let w := fun p : ℕ => (13/12:ℚ) * (if p=3 then 18/13 else 1) *
    (if p=5 then 15/13 else 1) * (if p=7 then 14/13 else 1) * (if p=11 then 66/65 else 1)
  have h := sigma_upper hm0 w (by
    intro p hp
    by_cases big : 13 ≤ p
    · have hp13 : (13:ℚ) ≤ p := by exact_mod_cast big
      simp only [w, if_neg (show p ≠ 3 by omega), if_neg (show p ≠ 5 by omega),
        if_neg (show p ≠ 7 by omega), if_neg (show p ≠ 11 by omega), mul_one]
      constructor <;> linarith
    · have bound : p ≤ 12 := by omega
      have prime := Nat.prime_of_mem_primeFactors hp
      have divides := Nat.dvd_of_mem_primeFactors hp
      obtain ⟨t, ht⟩ := hm
      have cases : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
        interval_cases p <;> (try norm_num at prime) <;> omega
      rcases cases with rfl|rfl|rfl|rfl <;> norm_num [w])
  have step (p : ℕ) (c : ℚ) : (∏ q ∈ m.primeFactors, if q=p then c else 1) =
      if p ∈ m.primeFactors then c else 1 := by simp
  simp only [w, prod_mul_distrib, prod_const, step] at h
  have mem (p : ℕ) (hp : p.Prime) : p ∈ m.primeFactors ↔ p ∣ m := by simp [Nat.mem_primeFactors, hp, hm0]
  simp only [mem 3 (by decide), mem 5 (by decide), mem 7 (by decide), mem 11 (by decide)] at h
  have hc := pow_le_pow_right₀ (show (1:ℚ) ≤ 13/12 by norm_num) hcard
  have factors : (0:ℚ) ≤ (if 3 ∣ m then 18/13 else 1) * (if 5 ∣ m then 15/13 else 1) *
      (if 7 ∣ m then 14/13 else 1) * (if 11 ∣ m then 66/65 else 1) := by positivity
  calc
    _ ≤ (m:ℚ)*((13/12)^m.primeFactors.card)*
      ((if 3 ∣ m then 18/13 else 1) * (if 5 ∣ m then 15/13 else 1) *
       (if 7 ∣ m then 14/13 else 1) * (if 11 ∣ m then 66/65 else 1)) := by convert h using 1 <;> ring
    _ ≤ _ := by gcongr

lemma separate_weight {a b : ℕ} {c : ℚ} (hc : 1 ≤ c) (p : ℕ) (h : ¬ (p ∣ a ∧ p ∣ b)) :
    (if p ∣ a then c else 1) * (if p ∣ b then c else 1) ≤ c := by
  split_ifs <;> simp_all

/-- An odd prime cannot divide both neighbours of an even number. Thus each correction factor is charged at most once. -/
lemma joint_bound {n : ℕ} (he : Even n) (hn : 2 ≤ n)
    (left : (n-1).primeFactors.card ≤ 3) (right : (n+1).primeFactors.card ≤ 3) :
    (sigma 1 (n-1) : ℚ) + sigma 1 (n+1) ≤ (78457/22464)*((n:ℚ)+1) := by
  let W := fun a : ℕ => (if 3 ∣ a then (18/13:ℚ) else 1) *
        (if 5 ∣ a then 15/13 else 1) * (if 7 ∣ a then 14/13 else 1) * (if 11 ∣ a then 66/65 else 1)
  have wpos (a : ℕ) : 1 ≤ W a := by dsimp [W]; split_ifs <;> norm_num
  have h3 := separate_weight (a:=n-1) (b:=n+1) (c:=18/13) (by norm_num) 3 (by omega)
  have h5 := separate_weight (a:=n-1) (b:=n+1) (c:=15/13) (by norm_num) 5 (by omega)
  have h7 := separate_weight (a:=n-1) (b:=n+1) (c:=14/13) (by norm_num) 7 (by omega)
  have h11 := separate_weight (a:=n-1) (b:=n+1) (c:=66/65) (by norm_num) 11 (by omega)
  have both : W (n-1)*W (n+1) ≤ (18/13)*(15/13)*(14/13)*(66/65) := by
    calc
      _ = ((if 3 ∣ n-1 then (18/13:ℚ) else 1) * (if 3 ∣ n+1 then 18/13 else 1)) * ((if 5 ∣ n-1 then (15/13:ℚ) else 1) * (if 5 ∣ n+1 then 15/13 else 1)) * ((if 7 ∣ n-1 then (14/13:ℚ) else 1) * (if 7 ∣ n+1 then 14/13 else 1)) * ((if 11 ∣ n-1 then (66/65:ℚ) else 1) * (if 11 ∣ n+1 then 66/65 else 1)) := by dsimp [W]; ring
      _ ≤ _ := by gcongr
  have wsum : W (n-1)+W (n+1) ≤ 1+(18/13)*(15/13)*(14/13)*(66/65) := by
    nlinarith only [both, mul_nonneg (sub_nonneg.mpr (wpos (n-1))) (sub_nonneg.mpr (wpos (n+1)))]
  have a := sparse_sigma (m:=n-1) (by exact ⟨n/2-1, by obtain ⟨x,hx⟩ := he; omega⟩) left
  have b := sparse_sigma (m:=n+1) (by obtain ⟨x,hx⟩ := he; exact ⟨x, by omega⟩) right
  change _ ≤ ((n-1:ℕ):ℚ) * (13/12)^3 * W (n-1) at a
  change _ ≤ ((n+1:ℕ):ℚ) * (13/12)^3 * W (n+1) at b
  have hcast : ((n-1:ℕ):ℚ) ≤ (n:ℚ)+1 := by exact_mod_cast (show n-1 ≤ n+1 by omega)
  push_cast at b
  have wa : 0 ≤ W (n-1) := by linarith [wpos (n-1)]
  have hleft : ((n-1:ℕ):ℚ) * (13/12)^3 * W (n-1) ≤ ((n:ℚ)+1) * (13/12)^3 * W (n-1) := by gcongr
  have scaled := mul_le_mul_of_nonneg_left wsum (show 0 ≤ ((n:ℚ)+1)*(13/12)^3 by positivity)
  linarith only [a,b,hleft,scaled]

lemma sigma_double {n : ℕ} (hn : 0 < n) (he : Even n) : 7*n ≤ 2*sigma 1 (2*n) := by
  obtain ⟨u,rfl⟩ := he
  have hu : 0 < u := by omega
  have sub : ({u,2*u,4*u} : Finset ℕ) ⊆ (4*u).divisors := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    apply Nat.mem_divisors.mpr
    refine ⟨?_,by positivity⟩
    rcases hx with rfl|rfl|rfl
    · exact dvd_mul_left _ _
    · exact ⟨2,by ring⟩
    · exact dvd_rfl
  have s := sum_le_sum_of_subset_of_nonneg (f:=fun x : ℕ => x) sub (by intros; omega)
  have h : u ∉ ({2*u,4*u}:Finset ℕ) := by simp; omega
  have h' : 2*u ∉ ({4*u}:Finset ℕ) := by simp; omega
  rw [sum_insert h,sum_insert h',sum_singleton] at s
  rw [show 2*(u+u)=4*u by ring, sigma_one_apply]
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
lemma small_even (i : Fin 235) :
    let n := 2*i.val+2
    sigma 1 (n-1) + sigma 1 (n+1) ≠ sigma 1 (2*n) := by
  revert i
  decide +kernel

lemma many_factors {n : ℕ} (hn : 2 ≤ n) (he : Even n)
    (eq : sigma 1 (n-1) + sigma 1 (n+1) = sigma 1 (2*n)) :
    4 ≤ (n-1).primeFactors.card ∨ 4 ≤ (n+1).primeFactors.card := by
  by_contra! small
  by_cases low : n ≤ 470
  · obtain ⟨x,hx⟩ := he
    have cert := small_even ⟨x-1, by omega⟩
    dsimp only at cert
    rw [show 2*(x-1)+2=n by omega] at cert
    exact cert eq
  have up := joint_bound he hn (by omega) (by omega)
  have down := sigma_double (by omega : 0 < n) he
  have ed : (sigma 1 (n-1) : ℚ)+sigma 1 (n+1) = sigma 1 (2*n) := by exact_mod_cast eq
  have ld : 7*(n:ℚ) ≤ 2*(sigma 1 (2*n):ℚ) := by exact_mod_cast down
  have hn' : (471:ℚ) ≤ n := by exact_mod_cast (show 471 ≤ n by omega)
  linarith

end OMA.OddSigmaHelpers
namespace OMA.R_oeis_a067730_R1

open ArithmeticFunction OMA.OddSigmaHelpers

/-- A counterexample whose preceding odd neighbour has at least four distinct prime factors. -/
def H1 : Prop := ∀ n : ℕ, 470 < n → Even n → 4 ≤ (n-1).primeFactors.card →
  sigma 1 (n-1) + sigma 1 (n+1) ≠ sigma 1 (2*n)

/-- When the preceding neighbour has small support, only the succeeding one can have large support. -/
def H2 : Prop := ∀ n : ℕ, 470 < n → Even n → (n-1).primeFactors.card ≤ 3 →
  4 ≤ (n+1).primeFactors.card → sigma 1 (n-1) + sigma 1 (n+1) ≠ sigma 1 (2*n)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a067730.main := by
  intro left right n hn eq
  by_contra ho
  have he : Even n := by rcases Nat.even_or_odd n with he|hn; exact he; contradiction
  by_cases small : n ≤ 470
  · obtain ⟨x,hx⟩ := he
    have cert := small_even ⟨x-1, by omega⟩
    dsimp only at cert
    rw [show 2*(x-1)+2=n by omega] at cert
    exact cert eq
  by_cases big : 4 ≤ (n-1).primeFactors.card
  · exact left n (by omega) he big eq
  · exact right n (by omega) he (by omega) ((many_factors hn he eq).resolve_left big) eq

end OMA.R_oeis_a067730_R1
