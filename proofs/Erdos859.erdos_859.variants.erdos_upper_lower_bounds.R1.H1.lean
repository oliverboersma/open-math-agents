import OMAReductions.R_Erdos859_erdos_859_variants_erdos_upper_lower_bounds_R1
import Mathlib

/-! Construct a practical divisor by requiring one prime factor from each
of two logarithmic windows at every scale. The Chinese remainder theorem
multiplies their densities. The first Mertens estimate below is adapted
from @senamakel's Romanoff proof (#2394), via @marcusbuffett's Erdős 688
step (#3586). The practical-divisor construction and counting proof are new. -/
noncomputable section
open Finset Filter Real Erdos859
open scoped Topology Classical
namespace PracticalDensity

def Covers (m : ℕ) := ∀ t ≤ m, ∃ S : Finset ℕ, (∀ s ∈ S, s ∣ m) ∧ ∑ s ∈ S, s = t

lemma coversTwo (k : ℕ) : Covers (2^k) := by
  intro t ht
  let L := t.bitIndices
  let F : Finset ℕ := ⟨L,Nat.bitIndices_nodup⟩
  refine ⟨F.image (fun i => 2^i),?_,?_⟩
  · rintro _ hs
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hs
    apply pow_dvd_pow
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp ((Nat.two_pow_le_of_mem_bitIndices hi).trans ht)
  · rw [sum_image (fun i _ j _ h => (Nat.pow_right_injective (by decide : 1<2)) h)]
    exact Nat.sum_map_two_pow_bitIndices t

lemma coversMul {m p : ℕ} (hm : Covers m) (hp : p.Prime) (hc : ¬p∣m) (hle : p ≤ m+1) :
    Covers (m*p) := by
  intro t ht
  obtain ⟨A,hA,sa⟩ := hm (t%p) (by have := Nat.mod_lt t hp.pos; omega)
  obtain ⟨B,hB,sb⟩ := hm (t/p) ((Nat.div_le_div_right ht).trans (by rw [Nat.mul_div_cancel _ hp.pos]))
  let f (b:ℕ) := p*b
  have dis : Disjoint A (B.image f) := by
    rw [Finset.disjoint_left]
    intro a ha hab
    obtain ⟨b,_,rfl⟩ := mem_image.mp hab
    exact hc (dvd_trans (dvd_mul_right _ _) (hA _ ha))
  refine ⟨A ∪ B.image f,?_,?_⟩
  · intro a ha
    rcases mem_union.mp ha with h|h
    · exact (hA _ h).trans (dvd_mul_right _ _)
    · obtain ⟨b,hb,rfl⟩ := mem_image.mp h
      simpa [f,Nat.mul_comm] using Nat.mul_dvd_mul_left p (hB _ hb)
  · rw [sum_union dis,sum_image (fun i _ j _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
    change (∑ a ∈ A,a) + ∑ b ∈ B,p*b = _
    rw [← mul_sum,sa,sb,Nat.mod_add_div]

lemma covered {m n t : ℕ} (hm : Covers m) (hd : m ∣ n) (hn : n ≠ 0) (ht : t ≤ m) :
    n ∈ DivisorSumSet t := by
  obtain ⟨S,hS,hs⟩ := hm t ht
  exact ⟨S,fun a ha => Nat.mem_divisors.mpr ⟨(hS a ha).trans hd,hn⟩,hs.symm⟩

def join {a b : ℕ} (h : a.Coprime b) (A : Finset (ZMod a)) (B : Finset (ZMod b)) :=
  (A ×ˢ B).map (ZMod.chineseRemainder h).symm.toEquiv.toEmbedding

lemma card_join {a b : ℕ} (h : a.Coprime b) (A : Finset (ZMod a)) (B : Finset (ZMod b)) :
    (join h A B).card = A.card*B.card := by simp [join]

lemma join_cast {a b n : ℕ} {h : a.Coprime b} {A : Finset (ZMod a)} {B : Finset (ZMod b)}
    (hn : (n:ZMod (a*b)) ∈ join h A B) : (n : ZMod a) ∈ A ∧ (n : ZMod b) ∈ B := by
  obtain ⟨v,hv,he⟩ := mem_map.mp hn
  have hs : v = ((n:ZMod a),(n:ZMod b)) := by
    change (ZMod.chineseRemainder h).symm v = n at he
    have hv := congrArg (ZMod.chineseRemainder h) he
    rw [RingEquiv.apply_symm_apply, map_natCast] at hv
    exact hv
  exact mem_product.mp (hs ▸ hv)

open OMA.R_Erdos859_erdos_859_variants_erdos_upper_lower_bounds_R1

lemma density_of_good (t d : ℕ) (hd : 0<d) (G : Finset (ZMod d))
    (hg : ∀ n : ℕ, ((n+1:ℕ):ZMod d) ∈ G → n+1 ∈ DivisorSumSet t) :
    (G.card:ℝ)/d ≤ (Nat.count (fun n => n+1 ∈ DivisorSumSet t) t.factorial : ℝ)/t.factorial := by
  letI : NeZero d := ⟨hd.ne'⟩
  let P (i : ℕ) := ((i+1:ℕ):ZMod d) ∈ G
  letI : DecidablePred P := fun i => Classical.propDecidable (P i)
  have period : Function.Periodic P d := by
    intro n; simp [P,add_assoc,add_left_comm,add_comm]
  have cnt : Nat.count P d = G.card := by
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_bij (fun i _ => ((i+1:ℕ):ZMod d))
    · intro i hi; exact (mem_filter.mp hi).2
    · intro i hi j hj he
      have e : (i:ZMod d) = (j:ZMod d) := by simpa using he
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hi).1),
        Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hj).1)] using congrArg ZMod.val e
    · intro y hy
      let x := (y-1).val
      have hxy : ((x+1:ℕ):ZMod d) = y := by simp [x]
      exact ⟨x,mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _),show P x from (show ((x+1:ℕ):ZMod d) ∈ G from hxy.symm ▸ hy)⟩,hxy⟩
  have h₁ := periodic_count_ratio P d hd period
  rw [← cnt]
  apply le_of_tendsto_of_tendsto' h₁ (periodic_count_ratio _ t.factorial (Nat.factorial_pos _) (successor_mem_periodic t))
  intro n
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Nat.count_mono_left (p:=P) (fun k _ => hg k) : Nat.count P n ≤ _)

end PracticalDensity

open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

end OMALib.Mertens
open Finset Filter Real OMALib.Mertens
open scoped Topology Classical
namespace PracticalDensity

def W (x k : ℕ) := Nat.primesLE (x^(k+1)) \ Nat.primesLE (x^k)

lemma memW {p x k : ℕ} : p ∈ W x k ↔ p.Prime ∧ x^k < p ∧ p ≤ x^(k+1) := by
  constructor
  · intro h
    obtain ⟨hi,lo⟩ := Finset.mem_sdiff.mp h
    obtain ⟨hu,hp⟩ := Nat.mem_primesLE.mp hi
    exact ⟨hp,lt_of_not_ge (fun hh => lo (Nat.mem_primesLE.mpr ⟨hh,hp⟩)),hu⟩
  · rintro ⟨hp,hl,hu⟩
    exact Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hu,hp⟩,fun hn => hl.not_ge (Nat.mem_primesLE.mp hn).1⟩
-- The weighted prime sum on this window is log x up to a bounded error.
lemma windowMass : ∀ᶠ x : ℕ in atTop, ∀ k ≤ 3, (1:ℝ)/8 ≤ ∑ p ∈ W x k, (p:ℝ)⁻¹ := by
  have grow : Tendsto (fun x : ℕ => log (x:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [grow.eventually_ge_atTop (4*mertens1Const),eventually_ge_atTop 2] with x hlarge hx k hk
  have hxpos : 0 < log (x:ℝ) := log_pos (by exact_mod_cast (show 1<x by omega))
  have hsub : Nat.primesLE (x^k) ⊆ Nat.primesLE (x^(k+1)) := by
    intro p hp
    obtain ⟨lt,pr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨lt.trans (Nat.pow_le_pow_right (by omega) (by omega)),pr⟩
  have hs := sum_sdiff hsub (f := fun p:ℕ => log (p:ℝ)/p)
  change (∑ p ∈ W x k, _) + _ = _ at hs
  have hlo := (abs_le.mp (abs_sum_log_div_sub_log_le_nat (x^(k+1)))).1
  have hhi := (abs_le.mp (abs_sum_log_div_sub_log_le_nat (x^k))).2
  rw [Nat.cast_pow,log_pow] at hlo hhi
  push_cast at hlo
  have hbd : (∑ p ∈ W x k, log (p:ℝ)/p) ≤ (4*log x)*(∑ p ∈ W x k, (p:ℝ)⁻¹) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨pr,_,hlt⟩ := memW.mp hp
    have hh := log_le_log (show 0<(p:ℝ) by exact_mod_cast pr.pos)
      (show (p:ℝ) ≤ (x:ℝ)^(k+1) by exact_mod_cast hlt)
    rw [log_pow] at hh
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact hh.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast (show k+1 ≤ 4 by omega)) hxpos.le)
  apply le_of_mul_le_mul_left (a := 4*log (x:ℝ)) _ (by positivity)
  linarith only [hs,hlo,hhi,hbd,hlarge]

set_option maxHeartbeats 800000 in
lemma groupEvent (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hm : (1:ℝ)/8 ≤ ∑ p ∈ P, (p:ℝ)⁻¹) :
    ∃ G : Finset (ZMod (∏ p ∈ P,p)), (∏ p ∈ P,p) ≤ 10*G.card ∧
      ∀ n : ℕ, (n:ZMod (∏ p ∈ P,p)) ∈ G → ∃ p ∈ P, p∣n := by
  classical
  let d := ∏ p ∈ P,p
  have hd : 0<d := Finset.prod_pos fun p hp => (hP p hp).pos
  letI : NeZero d := ⟨hd.ne'⟩
  let U := (univ : Finset (ZMod d)ˣ).image (fun u : (ZMod d)ˣ => (u:ZMod d))
  let G := (univ : Finset (ZMod d)) \ U
  have cards : G.card+ d.totient = d := by
    have h := card_sdiff_add_card_eq_card (subset_univ U)
    simpa [G,U,Finset.card_image_of_injective _ Units.val_injective,ZMod.card] using h
  have frac := congrArg (fun q : ℚ => (q:ℝ)) (Nat.totient_eq_mul_prod_factors d)
  push_cast at frac
  have fact : d.primeFactors = P := Nat.primeFactors_prod hP
  rw [fact] at frac
  have hpr : (∏ p ∈ P, (1-(p:ℝ)⁻¹)) ≤ exp (-(∑ p ∈ P, (p:ℝ)⁻¹)) := by
    rw [← sum_neg_distrib,Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      have h : (1:ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ h)
    · intro p hp; linarith [Real.add_one_le_exp (-(p:ℝ)⁻¹)]
  have hsmall : exp (-(∑ p ∈ P, (p:ℝ)⁻¹)) ≤ 9/10 :=
    (Real.exp_le_exp.mpr (neg_le_neg hm)).trans (by
      rw [Real.exp_neg,inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith [Real.add_one_le_exp ((1:ℝ)/8)])
  refine ⟨G,?_,?_⟩
  · have h := mul_le_mul_of_nonneg_left (hpr.trans hsmall) (Nat.cast_nonneg (α:=ℝ) d)
    try simp only [one_div] at frac
    exact_mod_cast (show (d:ℝ) ≤ 10*(G.card:ℝ) by
      have cc : (G.card:ℝ)+d.totient=d := by exact_mod_cast cards
      linarith)
  · intro n hn
    have hnot : ¬ n.Coprime d := by
      intro hc
      obtain ⟨u,hu⟩ := (ZMod.isUnit_iff_coprime n d).mpr hc
      have huU : (n:ZMod d) ∈ U := by
        dsimp only [U]
        rw [Finset.mem_image]
        exact ⟨u,Finset.mem_univ _,hu⟩
      exact ((Finset.mem_sdiff.mp (show (n:ZMod d) ∈ (univ : Finset (ZMod d)) \ U from hn)).2 huU)
    obtain ⟨p,pr,pn,pd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hp : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨pr,pd,hd.ne'⟩
    exact ⟨p,fact ▸ hp,pn⟩

end PracticalDensity


noncomputable section
open Finset Filter Real Erdos859
open scoped Topology Classical
namespace PracticalDensity

-- Each favorable residue contains a practical divisor at least cap.
-- All primes used in the modulus are bounded by bound.
def Stage (bound cap cost : ℕ) : Prop :=
  ∃ d : ℕ, 0 < d ∧ ∃ G : Finset (ZMod d), d ≤ cost*G.card ∧
    (∀ p : ℕ, p.Prime → p ∣ d → p ≤ bound) ∧
    ∀ n : ℕ, (n:ZMod d) ∈ G → ∃ m : ℕ, m ∣ d ∧ m ∣ n ∧ cap ≤ m ∧ Covers m

lemma extendStage {bound cap cost top : ℕ} (h : Stage bound cap cost) (hst : bound ≤ top)
    (ht : top ≤ cap) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ bound < p ∧ p ≤ top)
    (hmass : (1:ℝ)/8 ≤ ∑ p ∈ P, (p:ℝ)⁻¹) : Stage top (cap*bound) (cost*10) := by
  obtain ⟨d,hd,G,hG,hs,cover⟩ := h
  let D := ∏ p ∈ P,p
  have pr : ∀ p ∈ P, p.Prime := fun p hp => (hP p hp).1
  have hD : 0<D := Finset.prod_pos fun p hp => (pr p hp).pos
  have hfac : D.primeFactors=P := Nat.primeFactors_prod pr
  have cp (p) (hp : p ∈ P) : d.Coprime p := (Nat.Prime.coprime_iff_not_dvd (pr p hp)).mpr
    (fun pd => ((hP p hp).2.1).not_ge (hs p (pr p hp) pd)) |>.symm
  have cop : d.Coprime D := Nat.coprime_prod_right_iff.mpr cp
  obtain ⟨H,size,hit⟩ := groupEvent P pr hmass
  refine ⟨d*D,mul_pos hd hD,join cop G H,?_,?_,?_⟩
  · rw [card_join]
    calc d*D ≤ (cost*G.card)*(10*H.card) := Nat.mul_le_mul hG size
         _ = _ := by ring
  · intro p hp pd
    rcases hp.dvd_mul.mp pd with pd|pd
    · exact (hs p hp pd).trans hst
    · have hpP : p ∈ P := hfac ▸ Nat.mem_primeFactors.mpr ⟨hp,pd,hD.ne'⟩
      exact (hP p hpP).2.2
  · intro n hn
    obtain ⟨hold,hnew⟩ := join_cast hn
    obtain ⟨m,md,mn,hcap,hcov⟩ := cover n hold
    obtain ⟨p,hp,pn⟩ := hit n hnew
    have pm : ¬p∣m := fun dvd => (hP p hp).2.1.not_ge (hs _ (pr p hp) (dvd.trans md))
    exact ⟨m*p,Nat.mul_dvd_mul md (Finset.dvd_prod_of_mem id hp),
      ((pr p hp).coprime_iff_not_dvd.mpr pm).symm.mul_dvd_of_dvd_of_dvd mn pn,
      Nat.mul_le_mul hcap (hP p hp).2.1.le,
      coversMul hcov (pr p hp) pm (by have := (hP p hp).2.2; omega)⟩

def Y (Q j : ℕ) := Q^(2^j)

lemma y_succ (Q j : ℕ) : Y Q (j+1) = (Y Q j)^2 := by simp [Y,pow_succ,pow_mul]

lemma buildStages (K : ℕ) (hQ : 2 ≤ 2^K)
    (hm : ∀ x ≥ 2^K, ∀ k ≤ 3, (1:ℝ)/8 ≤ ∑ p ∈ W x k, (p:ℝ)⁻¹) (j : ℕ) :
    Stage ((Y (2^K) j)^2) ((Y (2^K) j)^4) ((2^K)^4*100^j) := by
  let Q := 2^K
  induction j with
  | zero =>
    simp only [Y,pow_zero,pow_one,mul_one]
    let d := (2^K)^4
    refine ⟨d,by dsimp [d]; positivity,{0},by simp [d],?_,?_⟩
    · intro p hp pd
      have h : p ∣ 2 := hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow pd)
      have he := (Nat.dvd_prime Nat.prime_two).mp h
      have hx := Nat.pow_le_pow_right (by omega : 0<2^K) (by decide : 1≤2)
      simp at hx
      rcases he with he|he <;> omega
    · intro n hn
      have hd : d ∣ n := (ZMod.natCast_eq_zero_iff _ _).mp (mem_singleton.mp hn)
      exact ⟨d,dvd_rfl,hd,le_rfl,by dsimp [d]; rw [← pow_mul]; exact coversTwo _⟩
  | succ j ih =>
    let x := Y (2^K) j
    have hx₀ : 2^K ≤ x := Nat.le_self_pow (by positivity) _
    have hx : 0<x := (by omega : 0<2^K).trans_le hx₀
    have hpow (a b : ℕ) (h : a≤b) : x^a ≤ x^b := Nat.pow_le_pow_right hx h
    have s₁ := extendStage ih (hpow 2 3 (by decide)) (hpow 3 4 (by decide))
      (W x 2) (fun p hp => memW.mp hp) (hm x hx₀ 2 (by decide))
    have s₂ := extendStage s₁ (hpow 3 4 (by decide)) (Nat.le_mul_of_pos_right _ (pow_pos hx 2))
      (W x 3) (fun p hp => memW.mp hp) (hm x hx₀ 3 (by decide))
    rw [y_succ]
    change Stage ((x^2)^2) ((x^2)^4) (_*100^(j+1))
    obtain ⟨d,hd,G,size,hs,cover⟩ := s₂
    refine ⟨d,hd,G,?_,?_,?_⟩
    · convert size using 1 <;> ring
    · convert hs using 2 <;> ring
    · intro n hn
      obtain ⟨m,md,mn,hm,hc⟩ := cover n hn
      refine ⟨m,md,mn,le_trans ?_ hm,hc⟩
      calc (x^2)^4 = x^8 := by ring
           _ ≤ x^9 := hpow 8 9 (by decide)
           _ = _ := by change _ = (x^4*x^2)*x^3; ring
end PracticalDensity

noncomputable section
open Finset Filter Real Erdos859 PracticalDensity
open scoped Topology Classical

theorem OMA.solution : OMA.R_Erdos859_erdos_859_variants_erdos_upper_lower_bounds_R1.H1 := by
  obtain ⟨L,hL⟩ := eventually_atTop.mp windowMass
  let K := L+2
  let Q := 2^K
  have hLQ : L ≤ Q := by
    have := Nat.lt_two_pow_self (n := K); dsimp [Q,K] at *; omega
  have hQ : 4 ≤ Q := by
    exact Nat.pow_le_pow_right (by decide : 0<2) (show 2≤K by dsimp [K]; omega)
  have hQ' : (4:ℝ) ≤ Q := by exact_mod_cast hQ
  have hlogQ : 1 ≤ log Q := by
    have := Real.log_le_log (by norm_num : (0:ℝ)<4) hQ'
    have he := Real.log_two_gt_d9
    rw [show (4:ℝ) = 2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)] at this
    linarith
  have grow : Tendsto (fun t:ℕ => log (t:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨8,by norm_num,?_⟩
  filter_upwards [grow.eventually_gt_atTop ((Q:ℝ)^4),eventually_gt_atTop (Q^4)] with t hlog ht
  have ht' : 0 < t := (Nat.zero_le _).trans_lt ht
  have hex : ∃ j : ℕ, t ≤ (Y Q j)^4 := by
    refine ⟨t,?_⟩
    have h : t ≤ 2^t := Nat.lt_two_pow_self.le
    have h' : 2^t ≤ Y Q t := by
      dsimp [Y]
      exact (Nat.pow_le_pow_left (by omega : 2≤Q) _).trans (Nat.pow_le_pow_right (by omega) h)
    exact (h.trans h').trans (Nat.le_self_pow (by decide : 4 ≠ 0) _)
  let j := Nat.find hex
  obtain ⟨d,hd,G,hsize,_,hgood⟩ := buildStages K (by omega : 2≤Q)
    (fun x hx => hL x (hLQ.trans hx)) j
  have coversT := Nat.find_spec hex
  change t ≤ (Y Q j)^4 at coversT
  have hdensity := density_of_good t d hd G (fun n hn => by
    obtain ⟨m,_,mn,hcap,hc⟩ := hgood (n+1) hn
    exact covered hc mn (by omega) (coversT.trans hcap))
  have htwo : (2:ℝ)^j ≤ log t := by
    obtain ⟨k,hk⟩ : ∃ k, j=k+1 := Nat.exists_eq_succ_of_ne_zero (by
      intro hz; rw [hz] at coversT; simp [Y] at coversT; omega)
    have hprev : (Y Q k)^4 < t := lt_of_not_ge (Nat.find_min hex (show k<j by omega))
    have hpos : 0< ((Y Q k)^4:ℕ) := by dsimp [Y]; positivity
    have hb := log_le_log (show (0:ℝ) < ((Y Q k)^4:ℕ) by exact_mod_cast hpos)
      (show (((Y Q k)^4:ℕ):ℝ) ≤ t by exact_mod_cast hprev.le)
    dsimp [Y] at hb
    push_cast at hb
    rw [log_pow,log_pow] at hb
    push_cast at hb
    rw [hk,pow_succ]
    have hr : (2:ℝ)^k ≤ 2^k * log (Q:ℝ) := le_mul_of_one_le_right (by positivity) hlogQ
    linarith only [hr,hb,show (0:ℝ) ≤ 2^k by positivity]
  have hlogp : 0 < log t := (by positivity : (0:ℝ)<2^j).trans_le htwo
  have hcost : (100:ℝ)^j ≤ (log t)^7 := calc
    _ ≤ ((2:ℝ)^7)^j := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = ((2:ℝ)^j)^7 := by rw [← pow_mul, Nat.mul_comm, pow_mul]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) htwo _
  have hgap : (Q:ℝ)^4*100^j < (log t)^8 := calc
    _ ≤ (Q:ℝ)^4 * (log t)^7 := mul_le_mul_of_nonneg_left hcost (by positivity)
    _ < (log t)*(log t)^7 := mul_lt_mul_of_pos_right hlog (by positivity)
    _ = _ := by ring
  apply lt_of_lt_of_le _ hdensity
  rw [show (8:ℝ) = ((8:ℕ):ℝ) by norm_num,Real.rpow_natCast,
    div_lt_div_iff₀ (pow_pos hlogp _) (show (0:ℝ)<d by exact_mod_cast hd),one_mul]
  have hsize' : (d:ℝ) ≤ (Q:ℝ)^4*100^j*G.card := by exact_mod_cast hsize
  have hc : 0 < (G.card:ℝ) := by
    have : G.card ≠ 0 := by intro hz; rw [hz,mul_zero] at hsize; omega
    exact_mod_cast Nat.pos_of_ne_zero this
  exact hsize'.trans_lt (by simpa [mul_comm] using mul_lt_mul_of_pos_right hgap hc)
